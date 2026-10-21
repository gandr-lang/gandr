//! Capabilities in the lowering: the capability type `Cap {op, …}`, a
//! returner's effect row `-F [I, …] A`, the exercise `c.op(v)`, the
//! capability scope `handle c : I { M } with { … }`, and the resumption
//! `k(v)` an operation clause calls.
//!
//! The rules these forms lower into are `gandr-core-checker`'s `capability`
//! module; this one decides only their spelling and what each spelling
//! denotes.
//!
//! # Operations and interfaces are the host's
//!
//! The interfaces a capability names are the host's — `Exec`, `Fs`, `Proc`
//! and `Env`, as `gandr_core_term::effect::host` declares them — and the
//! classification resolves every written name against that table, minted
//! once into a scratch arena of its own, so the names are never a second
//! copy. The mint sweep mints the table into the module's arena once, at the
//! first form that needs a signature, each of its types carrying that form's
//! origin.
//!
//! A capability type names its operations bare, `Cap {read, write}`, and each
//! belongs to the one host interface that offers it: no two host interfaces
//! share an operation name. The alternative was a qualified spelling,
//! `Cap {Fs.read}`; it was declined because the bare spelling is the one the
//! capability rules are stated in and the host table never makes it
//! ambiguous. Reversal: interfaces the surface declares itself, whose
//! operation names may collide, qualify them.
//!
//! An operation no host interface offers is
//! [`LoweringRefusal::UnresolvedName`] at the operation, and an interface the
//! host does not declare is [`LoweringRefusal::UnresolvedTypeHead`] at the
//! interface.
//!
//! # The grade is written where a bridge's is
//!
//! `Cap {…}` and `Cap[ω] {…}` are durable; `Cap[1] {…}` is consumable, which
//! the checker refuses at formation by name, so the drop of a linear
//! capability is refused rather than read as a durable one. Any other grade
//! is [`LoweringRefusal::GradedBridge`], as it is on a thunk type.
//!
//! # A returner's row is written in its bracket
//!
//! `-F [Fs] String` is the returner whose row holds the whole `Fs` interface,
//! in the bracket a thunk type's grade takes; `-F String` is the pure
//! returner. The alternative was a row after the result, `-F String ! {Fs}`;
//! it was declined because the bracket after the keyword is where a bridge
//! already carries what qualifies it. Reversal: row polymorphism, whose row
//! variable needs a spelling of its own.
//!
//! # An exercise is decided by the written type
//!
//! `c.op(v)` is a call whose head selects `op` off a name whose binder or
//! declaration was written with a `Cap` type, or that a capability scope
//! introduced. No argument passes the unit payload, one passes itself, and
//! several pass their tuple, so `c.write("notes", "x")` sends `Fs.write` its
//! pair. Every other selection stays an observation of a lazy record. The
//! lowering reads no types, so the decision is the written type's; the
//! alternative, a type-directed choice, waits on an elaborator. Reversal: an
//! elaborator that reads types, which would let a capability bound without a
//! written type be exercised.
//!
//! # A scope's clauses
//!
//! `handle c : I { M } with { pure(x) => N, oper op(p, k) => N_op, … }` binds
//! `c` over `M` alone, `x` over `N`, and `p` then `k` over `N_op`. The return
//! clause is spelled `pure`, the returner's own keyword, because `return` is
//! the function exit in this surface; an operation clause is led by `oper`,
//! the keyword a signature declares an operation with. The alternative was an
//! operation clause led by the operation's name, `op(p, k) => N_op`; it was
//! declined because its tiles gave every damaged call `f(a, b)` a stray
//! clause to read, and the parser's recovery from a dropped token worsened
//! wherever a call stood. Reversal: a recovery that never reads a form's
//! inner tiles without the tile that opens it. Within an operation clause
//! `k(v)` resumes the subject with `pure v`; `k` is bound in that clause
//! alone, so a resumption written elsewhere names nothing. Coverage — one
//! clause per operation of `I` — is the checker's.
//!
//! # Exits across a scope
//!
//! Each clause is a body of its own, as a lambda's is: an exit written
//! inside one leaves that body, so its value is the scope's. The subject is
//! no body: its tail is its result, which the `pure` clause receives, and an
//! exit written in it acts on the body around the scope, past the handler's
//! frame, which is live while the subject runs.
//!
//! - choice: a `return` in the subject leaves the body around the scope with
//!   its value, every handler frame between unwound and no `pure` clause run. A
//!   `become` there, and a `break` or a `continue` whose loop holds the scope,
//!   are [`LoweringRefusal::AcrossHandler`]: each would run code in place of
//!   the live frame, and a computation run there is no tail of the body. A loop
//!   inside the subject is a loop as any other.
//! - mechanism: the core's delimited control. The `return` mints a shift that
//!   never resumes what it captures, and the body it leaves is minted under a
//!   reset; the machine's shift captures through handler frames to the nearest
//!   reset, as the checker types it, so the frames are dropped with the
//!   capture. No clause runs while unwinding, and unwinding performs no effect.
//! - alternatives: a `return` that leaves the subject alone, its value passed
//!   to `pure` — the reading a `pure` tail already spells; a jump former in the
//!   core, which every pass over core terms and the command IL would learn, and
//!   whose label the machine could not keep as a mark while a delimiter is
//!   live; a sum the subject returns and the scope's continuation inspects,
//!   which needs the types the lowering does not read.
//! - cost: a body holding such a `return` keeps its reset frame while it runs,
//!   so its own tail calls no longer run in constant continuation.
//! - reversal: relocatable continuation marks, with which the `return` becomes
//!   a jump to the body's own continuation and no reset is minted.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::control::EffectClause;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::effect::host::HostSignatures;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowered;
use super::Lowerer;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arguments;
use super::arity::Planned;
use super::arity::clause_body;
use super::closed;
use super::exhausted;
use super::lowered;
use super::native;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::HeadArity;
use crate::resolve::SurfaceName;

#[cfg(test)]
mod tests;

/// What a name a selection is made off holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Holder
{
    /// A capability: the selection is an exercise.
    Capability,
    /// Anything else: the selection is an observation or a member.
    Other,
}

/// The host's interfaces, minted into a scratch arena for their names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the host table; only its names are read, never its types.
/// - fails: the unadmitted refusal at `site` if the host table conflicts with
///   itself, which its own tests rule out.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::OutOfFragment`] for a host table in conflict.
///
/// # Adequacy
/// - hypothesis: L3 — every capability form resolves its names through here.
/// - witness: `lower::capability::tests::a_capability_type_lowers_to_its_authority`
#[spec(ensures: |ret| ret.is_ok())]
fn host<'source>(site: Site) -> Result<HostSignatures, LoweringRefusal<'source>>
{
    HostSignatures::new(&mut CoreArena::new())
        .map_err(|_conflict| site.out(FragmentBoundary::Unadmitted))
}

/// The operations a capability type grants, named bare.
pub(super) type Authority = BTreeSet<OperationName>;

/// An exercise `c.op(v, …)`, as the classification read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Exercised
{
    /// The capability's name.
    capability: NodeIndex,
    /// The interface the operation belongs to.
    interface: EffectName,
    /// The operation exercised.
    operation: OperationName,
    /// The bytes of the head `c.op` that selects it.
    head: ByteSpan,
    /// The payload's values, in the lowerer's operand store.
    payload: Stretch,
}

/// A capability scope, as the classification read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Scoped
{
    /// The interface the scope handles.
    interface: EffectName,
    /// The capability's binder, as written.
    binder: NodeIndex,
    /// The subject, under the capability's binder.
    subject: Block,
    /// The return clause's body, under its result's binder.
    on_return: NodeIndex,
    /// Each operation clause's body, under its payload's binder and its
    /// continuation's, in written order.
    clauses: Vec<(OperationName, NodeIndex)>,
}

/// The host signatures the mint sweep has minted into the module's arena.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(super) enum Host
{
    /// No capability form has been minted.
    Unminted,
    /// The host table, in the module's arena.
    Minted(HostSignatures),
}

impl Sink<'_>
{
    /// The host table in the module's arena, minted at the first call, each
    /// of its types at `origin`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the host table, every type of which resolves in the arena; it
    ///   is minted at most once per sink.
    /// - fails: the unminted absence if the host table conflicts with itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module with capability forms over two interfaces
    ///   mints one table and checks.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    #[spec(ensures: |ref ret| match *ret {
        | Maybe::Present(table) => table.interfaces().iter().all(|signature| signature.types().all(|ty| self.arena.value_type(ty).is_some())),
        | Maybe::Absent(_) => true,
    })]
    fn host(
        &mut self,
        origin: Origin,
    ) -> Maybe<&HostSignatures, lowered::Absent>
    {
        if matches!(self.host, Host::Unminted) {
            let mark = self.arena.watermark();
            let Ok(minted) = HostSignatures::new(self.arena)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            for id in self.arena.value_types_since(mark) {
                self.origins.record_value_type(id, origin);
            }
            self.host = Host::Minted(minted);
        }
        match self.host {
            Host::Minted(ref table) => Maybe::Present(table),
            Host::Unminted => Maybe::Absent(lowered::Absent::Unminted),
        }
    }

    /// The signature of the host interface `interface` in the module's arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the interface's signature, as [`Self::host`] mints it; the
    ///   unminted absence for a name the host does not declare, which the
    ///   classification rules out.
    /// - fails: as [`Self::host`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::host`].
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    #[spec(ensures: |ref ret| match *ret {
        | Maybe::Present(ref signature) => signature.name() == interface,
        | Maybe::Absent(_) => true,
    })]
    fn signature(
        &mut self,
        interface: &EffectName,
        origin: Origin,
    ) -> Maybe<EffectSig, lowered::Absent>
    {
        self.host(origin)
            .and_then(|table| match table.named(interface) {
                Maybe::Present(signature) => Maybe::Present(signature.clone()),
                Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
            })
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a capability type, `Cap {op, …}` or `Cap[r] {op, …}`.
    ///
    /// # Specification
    /// - requires: `site` is a capability type.
    /// - ensures: the type stands as a value type, planned over the authority
    ///   its operations name, each under the host interface offering it, and
    ///   the grade its bracket writes: durable for none and for `ω`, consumable
    ///   for `1`.
    /// - fails: the wrong-sort refusal where no value type is read;
    ///   [`LoweringRefusal::GradedBridge`] for any other grade;
    ///   [`LoweringRefusal::UnresolvedName`] for an operation no host interface
    ///   offers; a misplaced-tile fault for a type out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The type's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-interface authority, the consumable grade, a
    ///   refused grade and an unknown operation, each asserted as the exact
    ///   minted type or refusal.
    /// - witness: `lower::capability::tests::a_capability_type_lowers_to_its_authority`
    /// - witness: `lower::capability::tests::an_unknown_operation_or_interface_is_refused_by_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Capability(..))))]
    pub(super) fn capability_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        closed(site, &mut cursor, TileName::CAP)?;
        let grade = if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            self.capability_grade(site, &mut cursor)?
        }
        else {
            CapabilityGrade::Durable
        };
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let table = host(site)?;
        let mut authority = Authority::new();
        loop {
            let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            let name = self.name_at(written);
            let operation = OperationName::from(name.as_ref());
            if let Maybe::Absent(_) = table.offering(&operation) {
                return Err(LoweringRefusal::UnresolvedName {
                    span: written.span,
                    name,
                });
            }
            let _first = authority.insert(operation);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                break;
            }
            if let Maybe::Present(_) = cursor.at(TileName::BRACE_CLOSE) {
                break;
            }
        }
        closed(site, &mut cursor, TileName::BRACE_CLOSE)?;
        exhausted(site, &cursor)?;

        let region = self
            .regions
            .get(&site.at.node)
            .map_or(Region::Held, |&depth| Region::Scoped(depth));
        self.plan(site, super::Plan::Capability(authority, grade, region));

        Ok(())
    }

    /// Classify a type placed somewhere, `T at c`: a type kept in a scope's
    /// region, or a handle to a value meaningful at a world.
    ///
    /// # Specification
    /// - requires: `site` is an at type.
    /// - ensures: where `c` names a capability scope around the type, the
    ///   type's region is that scope's: [`Region::Scoped`] at the number of
    ///   capability scopes from the outermost to the one binding `c`, counted
    ///   from one, the depth the checker gives the capability that scope
    ///   introduces. A capability type operand stands as the type, its region
    ///   recorded; any other operand is kept in the region, the operand read as
    ///   a value type where the at type stands. Where `c` names an earlier
    ///   declaration, the type is the handle `T at c` to a value of the operand
    ///   meaningful at the world that declaration declares, the operand read as
    ///   a value type where the at type stands (a declaration that declares no
    ///   world is the checker's to refuse).
    /// - fails: the wrong-sort refusal where no value type is read;
    ///   [`LoweringRefusal::UnresolvedName`] at `c` when neither a capability
    ///   scope nor an earlier declaration binds it; a misplaced tile or missing
    ///   operand fault for a type out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The type's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a capability at the inner of two nested scopes and at
    ///   the outer one mint their depths, a name no scope binds is refused and
    ///   an integer kept at a scope mints the kept type, each asserted exactly;
    ///   a handle at a declared world mints the handle type.
    /// - witness: `lower::capability::tests::a_capability_at_a_scope_lives_in_its_region`
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(ensures: |ret| ret.is_err()
        || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Transparent(operand)) if self.regions.contains_key(&operand))
        || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Kept(..)))
        || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::World(super::world::Worlded::At { .. }))))]
    pub(super) fn at_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let operand = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::AT)?;
        let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        exhausted(site, &cursor)?;
        let name = self.name_at(written);
        let unbound = move || LoweringRefusal::UnresolvedName {
            span: written.span,
            name,
        };
        let bound = match self.resolve_name(site, frame, name) {
            Ok(Maybe::Present(Resolved::Binder(bound)))
                if self.capabilities.contains(&bound.binder) =>
            {
                bound
            },
            Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => {
                return self.located_type(site, operand, constant);
            },
            Ok(Maybe::Present(Resolved::Binder(_)) | Maybe::Absent(_)) | Err(_) => {
                return Err(unbound());
            },
        };
        let depth = self
            .scope
            .chain(Frame::Inner(bound.binder))
            .filter(|binder| self.capabilities.contains(binder))
            .count();
        let depth = RegionDepth::from(u32::try_from(depth).map_err(|_overflow| unbound())?);
        self.read(operand.node, site.reading);
        if let Some((_, Former::CapabilityType)) = self.form_at(operand)? {
            let _first = self.regions.insert(operand.node, depth);
            self.plan(site, super::Plan::Transparent(operand.node));
        }
        else {
            self.plan(site, super::Plan::Kept(operand.node, depth));
        }

        Ok(())
    }

    /// Read a capability's grade, `[r]`, past its `[`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the grade's `[`.
    /// - ensures: `ω` is durable and `1` consumable, the cursor past the `]`.
    /// - fails: [`LoweringRefusal::GradedBridge`] for any other numeral or a
    ///   name, at the grade; a misplaced-tile fault for a grade out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The grade's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `ω`, `1`, `0` and a name, each asserted as the grade
    ///   or the exact refusal.
    /// - witness: `lower::capability::tests::a_capability_type_lowers_to_its_authority`
    #[spec(
        captures: first = cursor.peek(),
        ensures: |ret| match ret {
            | Ok(CapabilityGrade::Durable) => matches!(first, Maybe::Present(Piece::Tile { label: TileName::OMEGA, .. })),
            | Ok(CapabilityGrade::Consumable) => matches!(first, Maybe::Present(Piece::Tile { label: TileName::NUMBER, .. })),
            | Err(_) => true,
        },
    )]
    fn capability_grade(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<CapabilityGrade, LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let grade = if label == TileName::OMEGA {
            CapabilityGrade::Durable
        }
        else if label == TileName::NUMBER && self.name_at(at).as_ref() == "1" {
            CapabilityGrade::Consumable
        }
        else if label == TileName::NUMBER || label == TileName::IDENTIFIER {
            return Err(LoweringRefusal::GradedBridge {
                span: at.span,
                grade: self.name_at(at),
            });
        }
        else {
            return Err(site.fault(at.span, FormFault::MisplacedTile));
        };
        closed(site, cursor, TileName::BRACKET_CLOSE)?;

        Ok(grade)
    }

    /// Read a returner's row, `[I, …]`, past its `[`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the row's `[`.
    /// - ensures: the interfaces the row names, each once, in host order, the
    ///   cursor past the `]`.
    /// - fails: [`LoweringRefusal::UnresolvedTypeHead`] for an interface the
    ///   host does not declare, at the name; a misplaced-tile fault for a row
    ///   out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The row's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row of two interfaces and an undeclared one, each
    ///   asserted as the minted returner or the exact refusal.
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    /// - witness: `lower::capability::tests::an_unknown_operation_or_interface_is_refused_by_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |row| !row.is_empty()))]
    pub(super) fn returner_row(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<BTreeSet<EffectName>, LoweringRefusal<'source>>
    {
        let table = host(site)?;
        let mut row = BTreeSet::new();
        loop {
            let Maybe::Present(written) = cursor.tile(TileName::TYPE_IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            let name = self.name_at(written);
            let Maybe::Present(interface) = table.named(&EffectName::from(name.as_ref()))
            else {
                return Err(LoweringRefusal::UnresolvedTypeHead {
                    span: written.span,
                    name,
                    arity: HeadArity::Nullary,
                });
            };
            let _first = row.insert(interface.name().clone());
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                break;
            }
        }
        closed(site, cursor, TileName::BRACKET_CLOSE)?;

        Ok(row)
    }

    /// Plan the returner over `argument` whose row holds `row`.
    ///
    /// # Specification
    /// - requires: `argument` is the returner's one operand.
    /// - ensures: the returner stands as a computation type, its argument read
    ///   as a value type under its frame, planned over both.
    /// - fails: the wrong-sort refusal where no computation type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::returner_row`].
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Effectful(_, child)) if child == argument))]
    pub(super) fn effectful(
        &mut self,
        site: Site,
        row: BTreeSet<EffectName>,
        argument: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::CompType)?;
        self.read(argument, Reading::ValueType(frame));
        self.plan(site, super::Plan::Effectful(row, argument));

        Ok(())
    }

    /// What the type written at `declared` makes of a selection off its name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a capability exactly when the node is a `Cap` form, bare or
    ///   placed at a scope.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter and a declaration written at `Cap` are
    ///   exercised, and a selection off a lazy record stays an observation.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    fn written_holder(
        &self,
        declared: Maybe<NodeIndex, crate::resolve::binder_type::Absent>,
    ) -> Result<Holder, LoweringRefusal<'source>>
    {
        let Maybe::Present(declared) = declared
        else {
            return Ok(Holder::Other);
        };
        let Some(node) = self.tree.node(declared)
        else {
            return Ok(Holder::Other);
        };

        Ok(match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::CapabilityType | Former::AtType,
                ..
            } => Holder::Capability,
            Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => Holder::Other,
        })
    }

    /// Classify the call at `site` as an exercise when its head selects an
    /// operation off a capability.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head.
    /// - ensures: a head `c.op` whose `c` is bound or declared at a written
    ///   `Cap` type, or bound by a capability scope, stands as a computation
    ///   reading `c` and each argument as a value under its frame, planned as
    ///   the exercise of `op` under the host interface offering it; any other
    ///   call is left unplanned.
    /// - fails: [`LoweringRefusal::UnresolvedName`] for an operation no host
    ///   interface offers; the wrong-sort refusal where no computation is read;
    ///   the name's resolution refusal; the argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exercises through a parameter, a declaration and a
    ///   scope's binder lower and check, and one outside the authority is
    ///   refused by the checker by name.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Exercise(_))))]
    pub(super) fn exercise(
        &mut self,
        site: Site,
        cursor: &Cursor<'_>,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let mut ahead = cursor.clone();
        let Run::One(head) = ahead.operands()
        else {
            return Ok(Planned(false));
        };
        let Some((_, Former::Projection)) = self.form_at(head)?
        else {
            return Ok(Planned(false));
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, head.node, &mut pieces)?;
        let &[
            Piece::Operand(target),
            Piece::Tile {
                label: TileName::DOT,
                ..
            },
            Piece::Tile {
                label: TileName::IDENTIFIER,
                at: selected,
            },
        ] = pieces.pieces.as_slice()
        else {
            return Ok(Planned(false));
        };
        let Some((_, Former::Name)) = self.form_at(target)?
        else {
            return Ok(Planned(false));
        };
        // Resolved at the call, whose declaration already owns it: the holder's
        // own node inherits its owner only once the projection is read.
        let resolved = self.resolve_name(site, site.reading.frame(), self.name_at(target));
        let holder = match resolved {
            Ok(Maybe::Present(Resolved::Binder(bound)))
                if self.capabilities.contains(&bound.binder) =>
            {
                Holder::Capability
            },
            Ok(Maybe::Present(Resolved::Binder(bound))) => self.written_holder(bound.declared)?,
            Ok(Maybe::Present(Resolved::Declaration { declared, .. })) => {
                self.written_holder(declared)?
            },
            Ok(Maybe::Absent(_)) | Err(_) => Holder::Other,
        };
        if holder == Holder::Other {
            return Ok(Planned(false));
        }
        let name = self.name_at(selected);
        let operation = OperationName::from(name.as_ref());
        let table = host(site)?;
        let Maybe::Present(offered) = table.offering(&operation)
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: selected.span,
                name,
            });
        };
        let interface = offered.name().clone();
        let frame = self.require(site, Produced::Computation)?;
        let start = self.operands.len();
        arguments(site, &mut ahead, &mut self.operands)?;
        let payload = Stretch {
            start,
            end: self.operands.len(),
        };
        self.read(target.node, Reading::Value(frame));
        for position in payload.start .. payload.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(
            site,
            super::Plan::Exercise(Exercised {
                capability: target.node,
                interface,
                operation,
                head: head.span,
                payload,
            }),
        );

        Ok(Planned(true))
    }

    /// Classify the call at `site` as a resumption when its head is a
    /// continuation an operation clause binds.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head.
    /// - ensures: a head naming a clause's continuation stands as a computation
    ///   reading the continuation and each argument as a value under its frame,
    ///   planned as the resumption with the reply its arguments make; any other
    ///   call is left unplanned.
    /// - fails: the wrong-sort refusal where no computation is read; the name's
    ///   resolution refusal; the argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause resuming its subject lowers to the
    ///   resumption of `pure unit` and checks.
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Resume(..))))]
    pub(super) fn resumption(
        &mut self,
        site: Site,
        cursor: &Cursor<'_>,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let mut ahead = cursor.clone();
        let Run::One(head) = ahead.operands()
        else {
            return Ok(Planned(false));
        };
        let Some((_, Former::Name)) = self.form_at(head)?
        else {
            return Ok(Planned(false));
        };
        let Maybe::Present(bound) =
            self.scope
                .resolve(site.reading.frame(), self.name_at(head), &mut self.fuel)?
        else {
            return Ok(Planned(false));
        };
        if !self.resumptions.contains(&bound.binder) {
            return Ok(Planned(false));
        }
        let frame = self.require(site, Produced::Computation)?;
        let start = self.operands.len();
        arguments(site, &mut ahead, &mut self.operands)?;
        let reply = Stretch {
            start,
            end: self.operands.len(),
        };
        self.read(head.node, Reading::Value(frame));
        for position in reply.start .. reply.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, super::Plan::Resume(head.node, reply));

        Ok(Planned(true))
    }

    /// Classify a capability scope,
    /// `handle c : I { M } with { pure(x) => N, oper op(p, k) => N_op, … }`.
    ///
    /// # Specification
    /// - requires: `site` is a capability scope in term position.
    /// - ensures: the scope stands as a computation; `c` is bound over the
    ///   subject `M` alone, read as a body a path runs through; `x` is bound
    ///   over `N`, and `p` then `k` over each `N_op`, every clause read as a
    ///   computation body under the scope's own frame; `k` is recorded as a
    ///   continuation and `c` as a capability; the scope is planned over the
    ///   interface, the subject and the clauses in written order.
    /// - fails: the wrong-sort refusal where no computation is read;
    ///   [`LoweringRefusal::UnresolvedTypeHead`] for an interface the host does
    ///   not declare; [`LoweringRefusal::DuplicateDefinition`] for a second
    ///   return clause; a missing-operand fault for a scope with none; a
    ///   misplaced-tile fault for a scope out of shape; the block's and each
    ///   body's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The scope's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope whose subject exercises its capability and
    ///   whose clause resumes checks; one returning its capability is refused
    ///   by the checker as escaping; an undeclared interface and a second
    ///   return clause are refused here by name.
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    /// - witness: `lower::capability::tests::a_scoped_capability_cannot_escape`
    /// - witness: `lower::capability::tests::an_unknown_operation_or_interface_is_refused_by_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Scope(_))))]
    pub(super) fn capability_scope(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let split = pieces
            .pieces
            .iter()
            .position(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::WITH),
            )
            .unwrap_or(pieces.pieces.len());
        let Some((head, handlers)) = pieces.pieces.split_at_checked(split)
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };

        let mut cursor = Cursor::new(head, site.at.span);
        closed(site, &mut cursor, TileName::HANDLE)?;
        let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(site, &mut cursor, TileName::COLON)?;
        let Maybe::Present(written) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let handled = self.name_at(written);
        let table = host(site)?;
        let Maybe::Present(interface) = table.named(&EffectName::from(handled.as_ref()))
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: written.span,
                name: handled,
                arity: HeadArity::Nullary,
            });
        };
        let interface = interface.name().clone();
        let held = self.bind(binder, frame)?;
        let _first = self.capabilities.insert(held);
        let subject = self.block(site, &mut cursor, Frame::Inner(held))?;
        self.open_subject(site, subject)?;

        let mut cursor = Cursor::new(handlers, site.at.span);
        closed(site, &mut cursor, TileName::WITH)?;
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let mut on_return: Maybe<(NodeIndex, Placed), clause::Absent> =
            Maybe::Absent(clause::Absent::Unwritten);
        let mut clauses = Vec::new();
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, at }) if label == TileName::PURE => {
                    let (result, body) = Self::clause_parameter(site, &mut cursor)?;
                    if let Maybe::Present((_, first)) = on_return {
                        return Err(LoweringRefusal::DuplicateDefinition {
                            span: at.span,
                            name: SurfaceName::from("pure"),
                            first: first.span,
                        });
                    }
                    let bound = self.bind(result, frame)?;
                    self.clause(site, body, Frame::Inner(bound))?;
                    on_return = Maybe::Present((body, at));
                },
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::OPER => {
                    let Maybe::Present(at) = cursor.tile(TileName::IDENTIFIER)
                    else {
                        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                    };
                    closed(site, &mut cursor, TileName::PAREN_OPEN)?;
                    let Maybe::Present(payload) = cursor.tile(TileName::IDENTIFIER)
                    else {
                        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                    };
                    closed(site, &mut cursor, TileName::COMMA)?;
                    let Maybe::Present(continuation) = cursor.tile(TileName::IDENTIFIER)
                    else {
                        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                    };
                    closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
                    closed(site, &mut cursor, TileName::FAT_ARROW)?;
                    let body = site.one(cursor.operands())?;
                    let bound = self.bind(payload, frame)?;
                    let resumed = self.bind(continuation, Frame::Inner(bound))?;
                    let _first = self.resumptions.insert(resumed);
                    self.clause(site, body.node, Frame::Inner(resumed))?;
                    clauses.push((OperationName::from(self.name_at(at).as_ref()), body.node));
                },
                Maybe::Present(piece) => {
                    return Err(site.fault(piece.placed().span, FormFault::MisplacedTile));
                },
                Maybe::Absent(_) => {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                break;
            }
            if let Maybe::Present(_) = cursor.at(TileName::BRACE_CLOSE) {
                break;
            }
        }
        closed(site, &mut cursor, TileName::BRACE_CLOSE)?;
        exhausted(site, &cursor)?;
        let Maybe::Present((on_return, _)) = on_return
        else {
            return Err(site.fault(site.at.span, FormFault::MissingOperand));
        };

        self.plan(
            site,
            super::Plan::Scope(Scoped {
                interface,
                subject,
                binder: binder.node,
                on_return,
                clauses,
            }),
        );

        Ok(())
    }

    /// Read a return clause's `(x) =>` and its body, past its `pure`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the clause's `pure`.
    /// - ensures: the result's binder and the body, the cursor past the body.
    /// - fails: a misplaced-tile fault for a clause out of shape; the body
    ///   hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::capability_scope`].
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::MalformedForm { .. })))]
    fn clause_parameter(
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<(Placed, NodeIndex), LoweringRefusal<'source>>
    {
        closed(site, cursor, TileName::PAREN_OPEN)?;
        let Maybe::Present(result) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(site, cursor, TileName::PAREN_CLOSE)?;
        closed(site, cursor, TileName::FAT_ARROW)?;
        let body = site.one(cursor.operands())?;

        Ok((result, body.node))
    }

    /// Bind the name written at `binder` in a frame extending `frame`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the new frame, its binder named and sited as written.
    /// - fails: the binder note's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The binder note's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::capability_scope`].
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&bound| self.scope.site(bound) == Maybe::Present(binder.span)))]
    fn bind(
        &mut self,
        binder: Placed,
        frame: Frame,
    ) -> Result<crate::resolve::ScopeId, LoweringRefusal<'source>>
    {
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;

        Ok(self.scope.extend(frame, name, Maybe::Present(binder.span)))
    }

    /// Read a clause's body at `body` as a computation under `frame`, a body a
    /// path runs through.
    ///
    /// # Specification
    /// - requires: `body` is a clause's one operand.
    /// - ensures: the body reads as a computation under `frame` and is where a
    ///   path ends.
    /// - fails: the unreachable refusal, as [`Self::open_body`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::capability_scope`].
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| ret.is_err() || self.reading(body) == Reading::Computation(frame))]
    fn clause(
        &mut self,
        site: Site,
        body: NodeIndex,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.read(body, Reading::Computation(frame));
        self.open_body(
            site,
            clause_body(body),
            Maybe::Absent(native::answered::Absent::Unstated),
        )
    }

    /// Mint a capability type over `authority` at `grade`, living in `region`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the capability type whose authority restricts each host
    ///   interface to the operations written of it, at `origin`.
    /// - fails: the unminted absence when an operation is no host interface's,
    ///   which the classification rules out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::capability_type`].
    /// - witness: `lower::capability::tests::a_capability_type_lowers_to_its_authority`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::ValueType(id)) => sink.origins.value_type(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_capability(
        authority: &Authority,
        grade: CapabilityGrade,
        region: Region,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let row = match sink.host(origin) {
            Maybe::Present(table) => table.authority(authority),
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let Ok(row) = row
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let id = sink.arena.value_type_capability(row, grade, region);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint the returner over `argument` whose row holds the interfaces of
    /// `row`, whole.
    ///
    /// # Specification
    /// - requires: `argument` is already minted or absent.
    /// - ensures: `F^⟨row⟩ A` at `origin`; the argument's absence when it did
    ///   not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::returner_row`].
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::CompType(id)) => sink.origins.comp_type(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_effectful(
        &self,
        row: &BTreeSet<EffectName>,
        argument: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let result = match self.value_type_at(argument) {
            Maybe::Present(result) => result,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut signatures = Vec::with_capacity(row.len());
        for interface in row {
            match sink.signature(interface, origin) {
                Maybe::Present(signature) => signatures.push(signature),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let Ok(effects) = EffectRow::from_signatures(signatures)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let id = sink.arena.comp_type_returner_with_effects(result, effects);
        sink.origins.record_comp_type(id, origin);

        Maybe::Present(Lowered::CompType(id))
    }

    /// Mint the payload the values of `written` make: unit for none, the value
    /// for one, and their tuple for several.
    ///
    /// # Specification
    /// - requires: every value `written` names is already minted or absent.
    /// - ensures: the payload, a new unit or tuple carrying `origin`; the first
    ///   absence among the values.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — payloads of one and two values check against their
    ///   operations' payload types.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(id) => sink.arena.value(id).is_some(),
        | Maybe::Absent(_) => true,
    })]
    fn mint_payload(
        &self,
        written: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        let mut values = Vec::with_capacity(written.end.saturating_sub(written.start));
        for &position in super::stretch(&self.operands, written) {
            match self.value_at(position) {
                Maybe::Present(value) => values.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        if let &[only] = values.as_slice() {
            return Maybe::Present(only);
        }
        let id = sink.arena.value_tuple(&values);
        sink.origins.record_value(id, origin);

        Maybe::Present(id)
    }

    /// Mint the exercise `exercised` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the exercise of the operation, under its interface's whole
    ///   signature, of the capability with the payload its arguments make, at
    ///   `origin`, and a label at the head naming the operation's type, its
    ///   payload to the returner of its reply; the first absence among the
    ///   children.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::exercise`]; the head answers at the
    ///   operation it selects.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `lower::capability::tests::an_exercise_s_head_answers_at_its_operation`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_exercise(
        &self,
        exercised: &Exercised,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let capability = match self.value_at(exercised.capability) {
            Maybe::Present(capability) => capability,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let payload = match self.mint_payload(exercised.payload, sink, origin) {
            Maybe::Present(payload) => payload,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        sink.signature(&exercised.interface, origin)
            .map(|signature| {
                if let Maybe::Present(&EffectOp { payload, reply, .. }) =
                    signature.operation(&exercised.operation)
                {
                    let replied = sink.arena.comp_type_returner(reply);
                    let ty = sink.arena.comp_type_arrow(payload, replied);
                    sink.origins.record_label(Label {
                        span: exercised.head,
                        labelled: Labelled::CompType {
                            ty,
                            context: Vec::new(),
                        },
                    });
                }
                let id = sink.arena.computation_exercise(
                    capability,
                    signature,
                    exercised.operation.clone(),
                    payload,
                );
                sink.computation(id, origin)
            })
    }

    /// Mint the resumption of the continuation at `continuation` with the
    /// reply the values of `reply` make.
    ///
    /// # Specification
    /// - requires: every node named is already minted or absent.
    /// - ensures: the resumption of the continuation with `pure` of the reply,
    ///   both at `origin`; the first absence among the children.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::resumption`].
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_resume(
        &self,
        continuation: NodeIndex,
        reply: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let stack = match self.value_at(continuation) {
            Maybe::Present(stack) => stack,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        self.mint_payload(reply, sink, origin).map(|replied| {
            let returned = sink.arena.computation_return(replied);
            sink.origins.record_computation(returned, origin);
            let id = sink.arena.computation_resume(stack, returned);
            sink.computation(id, origin)
        })
    }

    /// Mint the capability scope `scoped` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the scope over the interface's whole signature, its subject,
    ///   its return clause and its operation clauses in written order, each
    ///   body minted as a body a path runs through, at `origin`, with the
    ///   capability's written name recorded as the scope's binder; the first
    ///   absence among the bodies.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::capability_scope`].
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_scope(
        &self,
        scoped: &Scoped,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let subject = match self.mint_body(scoped.subject, sink, origin) {
            Maybe::Present(subject) => subject,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let on_return = match self.mint_body(clause_body(scoped.on_return), sink, origin) {
            Maybe::Present(on_return) => on_return,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut clauses: Vec<EffectClause> = Vec::with_capacity(scoped.clauses.len());
        for (operation, body) in scoped.clauses.iter().cloned() {
            let body: ComputationId = match self.mint_body(clause_body(body), sink, origin) {
                Maybe::Present(body) => body,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            clauses.push(EffectClause { operation, body });
        }
        sink.signature(&scoped.interface, origin).map(|signature| {
            let id =
                sink.arena
                    .computation_scope(signature, subject, on_return, Arc::from(clauses));
            let scope = sink.computation(id, origin);
            if let Maybe::Present(name) = self.origin_at(scoped.binder) {
                sink.origins.record_binder(id, name);
            }
            scope
        })
    }
}

quenchant_shape::reason_enum! {
    /// Why a capability scope has no return clause.
    pub mod clause {
        /// The scope's clauses hold no `pure` clause.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No return clause was written.
            Unwritten,
        }
    }
}
