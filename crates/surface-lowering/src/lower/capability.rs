//! Capabilities in the lowering: the capability type `Cap {op, …}`, a
//! returner's effect row `-F [I, …] A`, the exercise `c.op(v)`, the perform
//! `I.op(v)` by an interface's name, the capability scope `handle c : I { M }
//! with { … }`, and the resumption `k(v)` of a continuation an operation
//! clause binds or a parameter states.
//!
//! The rules these forms lower into are `gandr-core-checker`'s `capability`
//! module; this one decides only their spelling and what each spelling
//! denotes.
//!
//! # Operations and interfaces are the host's
//!
//! The interfaces a capability names are the host's — `Exec`, `Fs`, `Proc`,
//! `Env`, `Ring` and `Console`, as `gandr_core_term::effect::host` declares
//! them — and the classification resolves every written name against that
//! table, minted once into a scratch arena of its own, so the names are never a
//! second copy. The mint sweep mints the table into the module's arena once, at
//! the first form that needs a signature, each of its types carrying that
//! form's origin.
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
//! # A perform is named by its interface
//!
//! `I.op(v)`, where `I` names no value in scope but a host interface, is the
//! perform of `op` of `I`: no capability is exercised, the computation's row
//! holds `I`, and the operation goes to whichever handler stands nearest when
//! it runs — a scope handling `I`, or else the host at the run target. So
//! `Console.print("hello, world!")` is a computation at `-F [Console] Unit`.
//! An operation `I` does not offer is [`LoweringRefusal::UnresolvedName`] at
//! the operation; a value named `I` shadows the interface, and its selection
//! reads as it would otherwise.
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
//! `k(v)` resumes the subject with `pure v`, and `abandon(k)` ends the
//! subject's continuation without running it, its value the unit; `abandon`
//! is that former only where the program binds no `abandon` of its own. `k`
//! is bound in that clause alone, so an abandonment written elsewhere names
//! nothing. A clause may hand `k` on: a function stating `Stack(C, D)`, or a
//! type member abbreviating it, resumes the stack its parameter holds with the
//! same former, `j(v)`. Coverage — one clause per operation of `I` — is the
//! checker's, and so is the rule that a clause whose continuation holds an
//! obligation ends `k` exactly once, never handing it on.
//!
//! # A clause that mints a buffer
//!
//! An operation replying a buffer, `Ring.alloc`, has its clause written
//! `oper alloc(n, b, k) => N`: the scope mints `b`, the buffer the clause
//! resumes with, and the clause holds it live. The core clause keeps its two
//! binders: its payload binder holds the pair of the payload and the mint,
//! which the body splits, and the mint is placed under `b`'s linear binder,
//! so `N` returns it exactly once, through `k(b)`.
//!
//! - choice: the mint rides the payload binder, so every walk over a clause's
//!   binders is unchanged; the placement is the session action
//!   `SessionAction::Place` the perform site uses.
//! - alternatives: a third clause binder for the mint, which every pass over
//!   clauses would learn; a scope that resumes with a buffer of its own, the
//!   clause resuming with unit, which leaves the handler no buffer to recycle.
//! - reversal: a clause former whose binders are read off its operation.
//!
//! A run statement `run b <- c.alloc(n) ;` binds the reply under a binder no
//! name reaches and places it under `b`'s linear binder, so the rest of the
//! block holds `b` live: it hands `b` back to a `free`, or on through a send,
//! exactly once, and never reads it.
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
//!   so its own tail calls do not run in constant continuation.
//! - reversal: relocatable continuation marks, with which the `return` becomes
//!   a jump to the body's own continuation and no reset is minted.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
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
use gandr_core_term::session::SessionAction;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;
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
use crate::origin::ClauseBinder;
use crate::origin::ClausePlace;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
use crate::origin::WrittenModel;
use crate::resolve::Frame;
use crate::resolve::HeadArity;
use crate::resolve::SurfaceName;
use crate::resolve::binder_site;
use crate::unbuilt::Unbuilt;

#[cfg(test)]
mod tests;
mod theory;

pub(super) use theory::TheoryInterface;

/// The name an abandonment is called by, where the program binds none.
const ABANDON: &str = "abandon";

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

/// What a binder's declared type states to a call its name heads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Stated
{
    /// A continuation's type, `Stack(C, D)`: the call resumes it.
    Stack,
    /// Any other type: the call applies it.
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
        .map_err(|_conflict| site.out(FragmentBoundary::Unadmitted(Unbuilt::CapabilityHost)))
}

/// What the reply of an operation is to the scope handling it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Reply
{
    /// A buffer the scope mints, which its performer holds live.
    Minted,
    /// Any other value.
    Plain,
}

/// What the reply of the host operation `operation` is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Reply::Minted`] exactly for an operation a host interface
///   offers whose reply is the buffer type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `Ring.alloc` mints, `Ring.free` and `Proc.exit` do not.
/// - witness: `lower::capability::tests::an_allocated_buffer_is_placed_live_and_freed`
#[spec(ensures: |ret| ret == Reply::Plain || matches!(HostSignatures::new(&mut CoreArena::new()), Ok(ref table) if matches!(table.offering(operation), Maybe::Present(_))))]
pub(super) fn mints(operation: &OperationName) -> Reply
{
    let mut arena = CoreArena::new();
    let Ok(table) = HostSignatures::new(&mut arena)
    else {
        return Reply::Plain;
    };
    let Maybe::Present(offered) = table.offering(operation)
    else {
        return Reply::Plain;
    };
    let Maybe::Present(requested) = offered.operation(operation)
    else {
        return Reply::Plain;
    };
    if matches!(arena.value_type(requested.reply), Some(&ValueType::Buffer)) {
        Reply::Minted
    }
    else {
        Reply::Plain
    }
}

/// The operations a capability type grants, named bare.
pub(super) type Authority = BTreeSet<OperationName>;

/// What performs an operation a call `x.op(v, …)` selects.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Performer
{
    /// `c.op(v)`: the capability `c` names is exercised, of the theory its
    /// scope handles where one does.
    Capability(NodeIndex, Option<Arc<TheoryInterface>>),
    /// `I.op(v)`: the operation of the host interface `I` is performed by
    /// name, handled by whichever handler stands nearest when it runs — the
    /// host's at the run target.
    Interface(EffectName),
}

/// The interface a form names: a host interface, or a theory a capability
/// scope handles.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Interface
{
    /// The host interface of this name.
    Host(EffectName),
    /// The theory a capability scope reads as an interface.
    Theory(Arc<TheoryInterface>),
}

/// An exercise `c.op(v, …)` or a perform `I.op(v, …)`, as the classification
/// read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Exercised
{
    /// What performs the operation.
    performer: Performer,
    /// The interface the operation belongs to.
    interface: Interface,
    /// The operation exercised.
    operation: OperationName,
    /// The bytes of the head `c.op` that selects it.
    head: ByteSpan,
    /// The payload's values, in the lowerer's operand store.
    payload: Stretch,
}

quenchant_shape::reason_enum! {
    /// Why a returner's row stands open through no tail.
    pub mod tail {
        /// The row is closed: it names its interfaces alone.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no `| t` after the interfaces.
            Closed,
        }
    }
}

/// A returner's row, `[I, …]`, `[a : I, …]`, `[I, … | t]` or `[t]`, as the
/// classification read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct WrittenRow
{
    /// The interfaces the row names whole, each its default instance.
    interfaces: BTreeSet<EffectName>,
    /// Each label `a : I` the row writes, its tile beside its interface.
    labels: Vec<(Placed, EffectName)>,
    /// Each label's instance, its interface at the region its name resolves
    /// to, once the row is planned under its frame.
    placed: Vec<(EffectName, Region)>,
    /// The operand the row stays open through, read as a row value.
    tail: Maybe<NodeIndex, tail::Absent>,
}

/// A capability scope, as the classification read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Scoped
{
    /// The interface the scope handles.
    interface: Interface,
    /// The capability's binder, as written.
    binder: NodeIndex,
    /// The subject, under the capability's binder.
    subject: Block,
    /// The return clause's body, under its result's binder.
    on_return: NodeIndex,
    /// The return clause's result binder, as written.
    result: NodeIndex,
    /// Each operation clause, in written order.
    clauses: Vec<Clause>,
}

/// An operation clause of a capability scope, as the classification read
/// it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Clause
{
    /// The operation the clause handles.
    operation: OperationName,
    /// The payload's binder, as written; none for `oper op(k)`.
    payload: Option<NodeIndex>,
    /// The continuation's binder, as written.
    continuation: NodeIndex,
    /// The body, under the clause's binders.
    body: NodeIndex,
    /// The buffer the scope mints for the clause, for an operation that
    /// replies one.
    mint: Mint,
}

/// The buffer a clause's scope mints, by the names its clause gives it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mint
{
    /// The operation replies no buffer: the payload binder holds the payload.
    Unminted,
    /// The payload binder holds the pair of the payload and the mint, split
    /// into the payload's name and the mint's, the mint placed live.
    Minted
    {
        /// The mint's name, as written.
        mint: NodeIndex,
    },
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
    pub(super) fn signature(
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
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&super::Plan::Capability(..))))]
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
            .copied()
            .unwrap_or(Region::Held);
        self.plan(site, super::Plan::Capability(authority, grade, region));

        Ok(())
    }

    /// Classify a type placed somewhere, `T at c`: a type kept in a region, or
    /// a handle to a value meaningful at a world.
    ///
    /// # Specification
    /// - requires: `site` is an at type.
    /// - ensures: where `c` names a capability scope or a hold around the type,
    ///   the type's region is the one that scope or hold opens:
    ///   [`Region::Scoped`] at the number of capability scopes and holds from
    ///   the outermost to the one binding `c`, counted from one, the depth the
    ///   checker gives that region. Where `c` names none and is a region binder
    ///   of the definition the type stands in, the region is [`Region::Bound`]
    ///   at that binder's ordinal. A capability type operand stands as the
    ///   type, its region recorded; any other operand is kept in the region,
    ///   the operand read as a value type where the at type stands. Where `c`
    ///   names none of these and an earlier declaration, the type is the handle
    ///   `T at c` to a value of the operand meaningful at the world that
    ///   declaration declares, the operand read as a value type where the at
    ///   type stands (a declaration that declares no world is the checker's to
    ///   refuse).
    /// - fails: the wrong-sort refusal where no value type is read;
    ///   [`LoweringRefusal::UnresolvedName`] at `c` when neither a capability
    ///   scope, a hold, a region binder nor an earlier declaration binds it; a
    ///   misplaced tile or missing operand fault for a type out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The type's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a capability at the inner of two nested scopes and at
    ///   the outer one mint their depths, a name no scope binds is refused, an
    ///   integer kept at a scope mints the kept type and one kept at a hold
    ///   inside the scope counts both, each asserted exactly; a handle at a
    ///   declared world mints the handle type; a thunk kept at a region binder
    ///   in a parameter and in a body's ascription keeps it at the binder's
    ///   ordinal, and a scope of the binder's name inside the body shadows it.
    /// - witness: `lower::capability::tests::a_capability_at_a_scope_lives_in_its_region`
    /// - witness: `lower::capability::tests::a_kept_type_at_a_region_binder_is_bound_to_it_1221`
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(ensures: |ret| ret.is_err()
        || matches!(self.plans.get(site.at.node), Some(&super::Plan::Transparent(operand)) if self.regions.contains_key(&operand))
        || matches!(self.plans.get(site.at.node), Some(&super::Plan::Kept(..)))
        || matches!(self.plans.get(site.at.node), Some(&super::Plan::World(super::world::Worlded::At { .. }))))]
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
        let Some(region) = self.region_named(site, frame, name)
        else {
            return match self.resolve_name(site, frame, name) {
                Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => {
                    self.located_type(site, operand, constant)
                },
                Ok(Maybe::Present(Resolved::Binder(_)) | Maybe::Absent(_)) | Err(_) => {
                    Err(unbound())
                },
            };
        };
        self.read(operand.node, site.reading);
        if let Some((_, Former::CapabilityType)) = self.form_at(operand)? {
            let _first = self.regions.insert(operand.node, region);
            self.plan(site, super::Plan::Transparent(operand.node));
        }
        else {
            self.plan(site, super::Plan::Kept(operand.node, region));
        }

        Ok(())
    }

    /// The region the name `name` names where `frame` stands, read at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a capability scope's binder or a hold, [`Region::Scoped`]
    ///   at the count of scopes and holds from the binder outward; otherwise,
    ///   for a region binder of the declaration owning `site` — one its
    ///   telescope binds, or an instance's a label of its row binds —
    ///   [`Region::Bound`] at it; none for any other name, and for a count past
    ///   the region's width.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::at_type`], and a row's label naming its
    ///   function's instance, and one naming nothing.
    /// - witness: `lower::capability::tests::a_capability_at_a_scope_lives_in_its_region`
    /// - witness: `lower::capability::tests::a_kept_type_at_a_region_binder_is_bound_to_it_1221`
    /// - witness: `lower::capability::tests::a_row_names_two_instances_of_one_interface_apart_2271`
    #[spec(ensures: |ret| ret.is_none_or(|region| region != Region::Held))]
    fn region_named(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Option<Region>
    {
        if let Ok(Maybe::Present(Resolved::Binder(bound))) = self.resolve_name(site, frame, name)
            && (self.capabilities.contains(&bound.binder) || self.held.contains(&bound.binder))
        {
            let depth = self
                .scope
                .chain(Frame::Inner(bound.binder))
                .filter(|binder| self.capabilities.contains(binder) || self.held.contains(binder))
                .count();
            return u32::try_from(depth)
                .ok()
                .map(|depth| Region::Scoped(RegionDepth::from(depth)));
        }
        self.region_binder(site.at.node, name).map(Region::Bound)
    }

    /// Bind the instance `entry`, a label of the result row of the function
    /// `site` declares, as a parameter under `frame`.
    ///
    /// # Specification
    /// - requires: `entry` is an [`Plicity::Instance`](crate::module::Plicity)
    ///   entry of the function's merged telescope.
    /// - ensures: the label bound in a frame extending `frame`, recorded as an
    ///   instance of its interface living at a region binder of the
    ///   declaration's own, named as the label and numbered after every one the
    ///   declaration binds before it, and pushed as a parameter whose type is
    ///   that instance's capability; the frame it bound is returned.
    /// - fails: [`LoweringRefusal::UnresolvedTypeHead`] for an interface the
    ///   host does not declare, at the name; a binder's own refusal; a fault at
    ///   the label when the declaration has no owner or its region binders
    ///   overflow their width.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function whose row labels two instances of one
    ///   interface takes them as two capability parameters at two region
    ///   binders, after its explicit parameter.
    /// - witness: `lower::implicit::tests::a_row_label_is_an_instance_after_every_parameter_2271`
    #[spec(
        captures: before = self.parameters.len(),
        ensures: |ret| ret.is_err() || self.parameters.len() == before.saturating_add(1),
    )]
    pub(super) fn instance_parameter(
        &mut self,
        site: Site,
        entry: crate::module::TelescopeEntry<'source>,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let misplaced = site.fault(entry.binder.span, FormFault::MisplacedTile);
        let Maybe::Present(written) = entry.declared
        else {
            return Err(misplaced);
        };
        let named = self.name_at(written);
        let table = host(site)?;
        let Maybe::Present(interface) = table.named(&EffectName::from(named.as_ref()))
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: written.span,
                name: named,
                arity: HeadArity::Nullary,
            });
        };
        let interface = interface.name().clone();
        let Maybe::Present(slot) = self.collected.owner_of(site.at.node)
        else {
            return Err(misplaced);
        };
        let binders = self.region_binders.entry(slot).or_default();
        let ordinal = u32::try_from(binders.len()).map_err(|_wide| misplaced)?;
        let region = gandr_core_term::effect::capability::RegionBinder::from(ordinal);
        let _shadowed = binders.insert(entry.name, region);
        self.note_binder(entry.binder, entry.name)?;
        let bound =
            self.scope
                .extend_instance(frame, entry.name, Maybe::Present(entry.binder.span));
        let _first = self.labelled.insert(bound, (interface.clone(), region));
        let _first = self
            .instance_parameters
            .insert(entry.binder.node, (interface, region));
        self.parameters.push(super::Parameter {
            binder: entry.binder.node,
            frame: bound,
            declared: Maybe::Absent(super::stated::Absent::Instance),
            component: None,
        });

        Ok(Frame::Inner(bound))
    }

    /// The variable a call at `site`, read under `frame`, passes for the
    /// instance `entry` of `function` it omits: the one instance of the
    /// entry's interface standing in scope.
    ///
    /// # Specification
    /// - requires: `entry` is an instance of `function`'s merged telescope.
    /// - ensures: the index, where `frame` stands, of the one binder in scope
    ///   holding an instance of the entry's interface — a capability scope's
    ///   capability, or an instance a label of the caller's own row binds.
    /// - fails: [`LoweringRefusal::InstanceUnanswered`] when none stands;
    ///   [`LoweringRefusal::InstanceAmbiguous`] naming the innermost two when
    ///   several do; a fault at the call for an entry naming no interface.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one scope of the interface resolves the call to its
    ///   capability beneath a binder of each zone, none refuses the call as
    ///   unanswered and two as ambiguous, naming both.
    /// - witness: `lower::implicit::tests::an_omitted_instance_is_the_one_handled_in_scope_2271`
    /// - witness: `lower::implicit::tests::an_omitted_instance_is_refused_when_none_or_several_stand_2271`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::InstanceUnanswered { .. } | LoweringRefusal::InstanceAmbiguous { .. } | LoweringRefusal::MalformedForm { .. })))]
    pub(super) fn resolved_instance(
        &self,
        site: Site,
        frame: Frame,
        function: SurfaceName<'source>,
        entry: crate::module::TelescopeEntry<'source>,
    ) -> Result<DeBruijnIndex, LoweringRefusal<'source>>
    {
        let Maybe::Present(written) = entry.declared
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };
        let named = self.name_at(written);
        let wanted = EffectName::from(named.as_ref());
        let mut standing = self.scope.bindings(frame).filter(|&(_, bound)| {
            self.answered.get(&bound.binder) == Some(&wanted)
                || self
                    .labelled
                    .get(&bound.binder)
                    .is_some_and(|&(ref interface, _)| *interface == wanted)
        });
        let Some((first, only)) = standing.next()
        else {
            return Err(LoweringRefusal::InstanceUnanswered {
                span: site.at.span,
                function,
                instance: entry.name,
                interface: named,
            });
        };
        if let Some((second, _)) = standing.next() {
            return Err(LoweringRefusal::InstanceAmbiguous {
                span: site.at.span,
                function,
                instance: entry.name,
                interface: named,
                first,
                second,
            });
        }

        Ok(only.index)
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

    /// Read a returner's row, `[I, …]`, `[a : I, …]`, `[I, … | t]` or `[t]`,
    /// past its `[`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the row's `[`.
    /// - ensures: the interfaces the row names whole, in host order, each label
    ///   it writes beside its interface, in written order, and the operand it
    ///   stays open through when one is written, the cursor past the `]`; a row
    ///   names an interface, a label or a tail.
    /// - fails: [`LoweringRefusal::UnresolvedTypeHead`] for an interface the
    ///   host does not declare, at the name;
    ///   [`LoweringRefusal::DuplicateDefinition`] for an interface named whole
    ///   again, or a label written again, at the second, since a row holds each
    ///   label once; a misplaced-tile fault for a row out of shape or a label
    ///   that is not one name.
    /// - panics: none.
    ///
    /// # Errors
    /// The row's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row of two interfaces and an undeclared one, each
    ///   asserted as the minted returner or the exact refusal, a row open
    ///   through a tail after its interfaces and alone, each minted over it,
    ///   and a row naming two instances of one interface apart.
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    /// - witness: `lower::capability::tests::an_unknown_operation_or_interface_is_refused_by_name`
    /// - witness: `lower::capability::tests::a_row_names_each_interface_once`
    /// - witness: `lower::capability::tests::a_row_stays_open_through_its_tail_2270`
    /// - witness: `lower::capability::tests::a_row_names_two_instances_of_one_interface_apart_2271`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |row| !row.interfaces.is_empty() || !row.labels.is_empty() || matches!(row.tail, Maybe::Present(_))))]
    pub(super) fn returner_row(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<WrittenRow, LoweringRefusal<'source>>
    {
        // An operand first is the row's tail written alone, `[r]`, or its
        // first label, `[a : I]`, as the tile after it says.
        let mut first = None;
        if let Maybe::Present(Piece::Operand(written)) = cursor.peek() {
            let _written = cursor.read();
            if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                closed(site, cursor, TileName::BRACKET_CLOSE)?;
                return Ok(WrittenRow {
                    interfaces: BTreeSet::new(),
                    labels: Vec::new(),
                    placed: Vec::new(),
                    tail: Maybe::Present(written.node),
                });
            }
            first = Some(self.label_of(site, written)?);
        }
        let table = host(site)?;
        let mut row = BTreeMap::new();
        let mut labels: Vec<(Placed, EffectName)> = Vec::new();
        let mut labelled_at = BTreeMap::new();
        loop {
            let label = match first.take() {
                Some(label) => Some(label),
                None => match cursor.peek() {
                    Maybe::Present(Piece::Operand(written)) => {
                        let _written = cursor.read();
                        closed(site, cursor, TileName::COLON)?;
                        Some(self.label_of(site, written)?)
                    },
                    Maybe::Present(Piece::Tile { .. }) | Maybe::Absent(_) => None,
                },
            };
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
            if let Some(label) = label {
                let named = self.name_at(label);
                if let Some(&first) = labelled_at.get(&named) {
                    return Err(LoweringRefusal::DuplicateDefinition {
                        span: label.span,
                        name: named,
                        first,
                    });
                }
                let _first = labelled_at.insert(named, label.span);
                labels.push((label, interface.name().clone()));
            }
            else {
                if let Some(&first) = row.get(interface.name()) {
                    return Err(LoweringRefusal::DuplicateDefinition {
                        span: written.span,
                        name,
                        first,
                    });
                }
                let _first = row.insert(interface.name().clone(), written.span);
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                break;
            }
        }
        let tail = if let Maybe::Present(_) = cursor.tile(TileName::BAR) {
            let Maybe::Present(Piece::Operand(tail)) = cursor.read()
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            Maybe::Present(tail.node)
        }
        else {
            Maybe::Absent(tail::Absent::Closed)
        };
        closed(site, cursor, TileName::BRACKET_CLOSE)?;

        Ok(WrittenRow {
            interfaces: row.into_keys().collect(),
            labels,
            placed: Vec::new(),
            tail,
        })
    }

    /// The name tile of the row label `written`, the operand before a `:`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the operand's one tile, when it is an identifier or a type
    ///   variable.
    /// - fails: a misplaced-tile fault at the operand for any other operand; a
    ///   form fault reading its pieces.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::returner_row`].
    /// - witness: `lower::capability::tests::a_row_names_two_instances_of_one_interface_apart_2271`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|at| written.span.start() <= at.span.start() && at.span.end() <= written.span.end()))]
    fn label_of(
        &self,
        site: Site,
        written: Placed,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, written.node, &mut pieces)?;
        match *pieces.pieces.as_slice() {
            [Piece::Tile { label, at }]
                if label == TileName::IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                Ok(at)
            },
            _ => Err(site.fault(written.span, FormFault::MisplacedTile)),
        }
    }

    /// Plan the returner over `argument` whose row is `row`.
    ///
    /// # Specification
    /// - ensures: the returner stands as a computation type, its row's tail
    ///   read as a value and its argument as a value type under its frame, each
    ///   label of its row placed at the region its name names there
    ///   ([`Self::region_named`]), planned over both.
    /// - fails: the wrong-sort refusal where no computation type is read;
    ///   [`LoweringRefusal::UnresolvedName`] at a label naming no region.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::returner_row`].
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    /// - witness: `lower::capability::tests::a_row_stays_open_through_its_tail_2270`
    /// - witness: `lower::capability::tests::a_row_names_two_instances_of_one_interface_apart_2271`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&super::Plan::Effectful(_, child)) if child == argument))]
    pub(super) fn effectful(
        &mut self,
        site: Site,
        mut row: WrittenRow,
        argument: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::CompType)?;
        for &(label, ref interface) in &row.labels {
            let name = self.name_at(label);
            let Some(region) = self.region_named(site, frame, name)
            else {
                return Err(LoweringRefusal::UnresolvedName {
                    span: label.span,
                    name,
                });
            };
            row.placed.push((interface.clone(), region));
        }
        if let Maybe::Present(tail) = row.tail {
            self.read(tail, Reading::Value(frame));
        }
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
    /// operation off a capability, or as a perform when it selects one off a
    /// host interface by name.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head.
    /// - ensures: a head `c.op` whose `c` is bound or declared at a written
    ///   `Cap` type, or bound by a capability scope, stands as a computation
    ///   reading `c` and each argument as a value under its frame, planned as
    ///   the exercise of `op` under the host interface offering it; a head
    ///   `I.op` whose `I` names no value in scope but a host interface stands
    ///   as a computation reading each argument, planned as the perform of `op`
    ///   of `I`; any other call is left unplanned.
    /// - fails: [`LoweringRefusal::UnresolvedName`] for an operation no host
    ///   interface offers, or one the interface `I` does not; the wrong-sort
    ///   refusal where no computation is read; the name's resolution refusal;
    ///   the argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exercises through a parameter, a declaration and a
    ///   scope's binder lower and check, and one outside the authority is
    ///   refused by the checker by name; a perform by an interface's name
    ///   checks at the row holding the interface, and an operation the named
    ///   interface does not offer is refused at the operation.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    /// - witness: `lower::capability::tests::an_operation_is_performed_by_its_interface_s_name_2279`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&super::Plan::Exercise(_))))]
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
        let Some((performer, selected)) = self.exercised(site, site.reading.frame(), head)?
        else {
            return Ok(Planned(false));
        };
        let name = self.name_at(selected);
        let operation = OperationName::from(name.as_ref());
        let interface = if let Performer::Capability(_, Some(ref theory)) = performer {
            if theory.operation(&operation).is_none() {
                return Err(LoweringRefusal::UnresolvedName {
                    span: selected.span,
                    name,
                });
            }
            Interface::Theory(Arc::clone(theory))
        }
        else {
            let table = host(site)?;
            let Maybe::Present(offered) = table.offering(&operation)
            else {
                return Err(LoweringRefusal::UnresolvedName {
                    span: selected.span,
                    name,
                });
            };
            let interface = offered.name().clone();
            if let Performer::Interface(ref named) = performer
                && *named != interface
            {
                return Err(LoweringRefusal::UnresolvedName {
                    span: selected.span,
                    name,
                });
            }
            Interface::Host(interface)
        };
        let frame = self.require(site, Produced::Computation)?;
        let start = self.operands.len();
        arguments(site, &mut ahead, &mut self.operands)?;
        let payload = Stretch {
            start,
            end: self.operands.len(),
        };
        if let Performer::Capability(capability, _) = performer {
            self.read(capability, Reading::Value(frame));
        }
        for position in payload.start .. payload.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(
            site,
            super::Plan::Exercise(Exercised {
                performer,
                interface,
                operation,
                head: head.span,
                payload,
            }),
        );

        Ok(Planned(true))
    }

    /// What performs the operation a call head `x.op` selects, and the
    /// selected `op`, when `x` holds a capability where `frame` stands or
    /// names a host interface and no value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the capability `c` and the selected `op` for a projection off
    ///   a name bound or declared at a written `Cap` type, or bound by a
    ///   capability scope; the interface `I` and `op` for a projection off a
    ///   name that resolves to no binder or declaration, or a capitalised name
    ///   no constructor bears, that a host interface bears; nothing for any
    ///   other head.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::exercise`].
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `lower::capability::tests::an_operation_is_performed_by_its_interface_s_name_2279`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    fn exercised(
        &mut self,
        site: Site,
        frame: Frame,
        head: Placed,
    ) -> Result<Option<(Performer, Placed)>, LoweringRefusal<'source>>
    {
        let Some((_, Former::Projection)) = self.form_at(head)?
        else {
            return Ok(None);
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
            return Ok(None);
        };
        let written = self.name_at(target);
        match self.form_at(target)? {
            Some((_, Former::Name)) => {},
            // A capitalised name the source declares no constructor by: the
            // interface it names, when a host interface bears it.
            Some((_, Former::Constructor)) => {
                return Ok(match self.constructor_named(site, written) {
                    Maybe::Present(_) => None,
                    Maybe::Absent(_) => Self::interface_named(written)
                        .map(|interface| (Performer::Interface(interface), selected)),
                });
            },
            Some(_) | None => return Ok(None),
        }
        // Resolved at the call, whose declaration already owns it: the holder's
        // own node inherits its owner only once the projection is read.
        let resolved = self.resolve_name(site, frame, written);
        let holder = match resolved {
            Ok(Maybe::Present(Resolved::Binder(bound)))
                if self.capabilities.contains(&bound.binder)
                    || self.labelled.contains_key(&bound.binder) =>
            {
                let theory = self.theory_capabilities.get(&bound.binder).cloned();
                return Ok(Some((Performer::Capability(target.node, theory), selected)));
            },
            Ok(Maybe::Present(Resolved::Binder(bound))) => self.written_holder(bound.declared)?,
            Ok(Maybe::Present(Resolved::Declaration { declared, .. })) => {
                self.written_holder(declared)?
            },
            Ok(Maybe::Absent(_)) | Err(_) => {
                if let Some(interface) = Self::interface_named(written) {
                    return Ok(Some((Performer::Interface(interface), selected)));
                }
                Holder::Other
            },
        };
        Ok((holder == Holder::Capability)
            .then_some((Performer::Capability(target.node, None), selected)))
    }

    /// The host interface named `written`, when the host declares one.
    ///
    /// # Specification
    /// trivial.
    fn interface_named(written: SurfaceName<'_>) -> Option<EffectName>
    {
        let interface = EffectName::from(written.as_ref());
        let table = HostSignatures::new(&mut CoreArena::new()).ok()?;
        matches!(table.named(&interface), Maybe::Present(_)).then_some(interface)
    }

    /// Whether the computation `bound` a run statement binds, read where
    /// `frame` stands, exercises an operation the scope handling it mints a
    /// buffer for, so the statement places the buffer live.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly for a call `c.op(…)` whose head is a selection
    ///   off a capability and whose `op` replies a buffer.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `run b <- r.alloc(n) ;` places `b`, a run of any
    ///   other exercise names its reply.
    /// - witness: `lower::capability::tests::an_allocated_buffer_is_placed_live_and_freed`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn placing(
        &mut self,
        site: Site,
        frame: Frame,
        bound: Placed,
    ) -> Result<Reply, LoweringRefusal<'source>>
    {
        let Some((_, Former::Call)) = self.form_at(bound)?
        else {
            return Ok(Reply::Plain);
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, bound.node, &mut pieces)?;
        let Some(&Piece::Operand(head)) = pieces.pieces.first()
        else {
            return Ok(Reply::Plain);
        };
        // A theory's operation replies a value of a sort its manifest fixes,
        // which no scope mints.
        Ok(match self.exercised(site, frame, head)? {
            Some((Performer::Capability(_, Some(_)), _)) | None => Reply::Plain,
            Some((_, selected)) => mints(&OperationName::from(self.name_at(selected).as_ref())),
        })
    }

    /// What the type written at `declared` states: a stack, `Stack(C, D)`
    /// itself or a type member abbreviating one through any number of
    /// members, or another type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Stated::Stack`] exactly when the chain of transparent plans
    ///   from `declared`, each the type a manifest member was written at,
    ///   reaches a node planned as a stack, or a node not yet classified that
    ///   [`Self::written_stack`] reads as one; a member is classified after a
    ///   declaration that reads it whenever the member's type lies deeper in
    ///   the tree.
    /// - fails: an engine fault.
    /// - panics: none.
    /// - executable: none — the answer is the walk itself, and no predicate
    ///   over the plans states it without walking them again.
    ///
    /// # Errors
    /// The engine fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written stack, a member abbreviating one read
    ///   inside its module and one read qualified from a declaration classified
    ///   before it are resumed, and a thunk type is applied.
    /// - witness: `lower::capability::tests::a_stated_stack_is_resumed_as_a_clause_resumes_1387`
    fn states_a_stack(
        &mut self,
        declared: NodeIndex,
    ) -> Result<Stated, LoweringRefusal<'source>>
    {
        let mut at = declared;
        loop {
            self.fuel.spend()?;
            match self.plans.get(at) {
                Some(&super::Plan::Stack(..)) => return Ok(Stated::Stack),
                Some(&super::Plan::Transparent(written)) => at = written,
                Some(&super::Plan::Unplanned) => return self.written_stack(at),
                Some(_) | None => return Ok(Stated::Other),
            }
        }
    }

    /// Classify the call at `site` as a resumption when its head is a
    /// continuation: one an operation clause binds, or a binder declared at
    /// `Stack(C, D)` or a member abbreviating it, which a clause hands its
    /// continuation on by.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head.
    /// - ensures: a head naming a clause's continuation or a binder whose
    ///   declared type is a stack, as [`Self::states_a_stack`] reads it, stands
    ///   as a computation reading the continuation and each argument as a value
    ///   under its frame, planned as the resumption with the reply its
    ///   arguments make; any other call is left unplanned.
    /// - fails: the wrong-sort refusal where no computation is read; the name's
    ///   resolution refusal; an engine fault reading the binder's declared
    ///   type; the argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause resuming its subject lowers to the
    ///   resumption of `pure unit` and checks; a function resuming the stack it
    ///   states lowers to the same resumption.
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    /// - witness: `lower::capability::tests::a_stated_stack_is_resumed_as_a_clause_resumes_1387`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&super::Plan::Resume(..))))]
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
        let resumes = self.resumptions.contains(&bound.binder)
            || match bound.declared {
                Maybe::Present(declared) => self.states_a_stack(declared)? == Stated::Stack,
                Maybe::Absent(_) => false,
            };
        if !resumes {
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

    /// Classify the call at `site` as an abandonment when its head is the
    /// name `abandon`, which the program does not bind, and its one argument
    /// a continuation an operation clause binds.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head.
    /// - ensures: such a call stands as a computation reading the continuation
    ///   as a value under its frame, planned as the abandonment; any other call
    ///   is left unplanned, the operand store as it was found.
    /// - fails: the wrong-sort refusal where no computation is read; a name's
    ///   resolution refusal; the argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause abandoning its continuation lowers to the
    ///   abandonment of the clause's stack, and a program binding its own
    ///   `abandon` calls it.
    /// - witness: `lower::capability::tests::a_clause_abandons_its_continuation_1334`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&super::Plan::Abandon(_))))]
    pub(super) fn abandonment(
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
        let name = self.name_at(head);
        if name.as_ref() != ABANDON {
            return Ok(Planned(false));
        }
        if let Maybe::Present(_) = self
            .scope
            .resolve(site.reading.frame(), name, &mut self.fuel)?
        {
            return Ok(Planned(false));
        }
        let start = self.operands.len();
        arguments(site, &mut ahead, &mut self.operands)?;
        let argument = if let Some(&[argument]) = self.operands.get(start ..) {
            Some(argument)
        }
        else {
            None
        };
        self.operands.truncate(start);
        let Some(argument) = argument
        else {
            return Ok(Planned(false));
        };
        let Some(node) = self.tree.node(argument)
        else {
            return Ok(Planned(false));
        };
        let placed = Placed::of(argument, node);
        let Some((_, Former::Name)) = self.form_at(placed)?
        else {
            return Ok(Planned(false));
        };
        let Maybe::Present(bound) =
            self.scope
                .resolve(site.reading.frame(), self.name_at(placed), &mut self.fuel)?
        else {
            return Ok(Planned(false));
        };
        if !self.resumptions.contains(&bound.binder) {
            return Ok(Planned(false));
        }
        let frame = self.require(site, Produced::Computation)?;
        self.read(argument, Reading::Value(frame));
        self.plan(site, super::Plan::Abandon(argument));
        Ok(Planned(true))
    }

    /// Classify a capability scope,
    /// `handle c : I { M } with { pure(x) => N, oper op(p, k) => N_op, … }`,
    /// its interface a host's or a theory's with its value sorts, `handle c :
    /// T with sort S = A { M } with { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a capability scope in term position.
    /// - ensures: the scope stands as a computation; each manifest type is read
    ///   as a value type under the scope's own frame, a fixed carrier minted
    ///   before the sweep; `c` is bound over the subject `M` alone, read as a
    ///   body a path runs through; `x` is bound over `N`, and `p` then `k` over
    ///   each `N_op`, `k` alone over an unnamed payload for `oper op(k)`, every
    ///   clause read as a computation body under the scope's own frame; `k` is
    ///   recorded as a continuation and `c` as a capability answering the
    ///   interface's name ([`Self::answered`]), beside the theory it handles
    ///   for a theory's scope; the scope is planned over the interface,
    ///   [`Self::handled`], the subject and the clauses in written order.
    /// - fails: the wrong-sort refusal where no computation is read; the
    ///   refusals of [`Self::handled`];
    ///   [`LoweringRefusal::DuplicateDefinition`] for a second return clause; a
    ///   missing-operand fault for a scope with none; a misplaced-tile fault
    ///   for a scope out of shape, a minting clause naming no payload among
    ///   them; the block's and each body's own refusal.
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
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&super::Plan::Scope(_))))]
    pub(super) fn capability_scope(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        // The clauses' `with` is the last: every manifest sort's stands
        // before the subject.
        let split = pieces
            .pieces
            .iter()
            .rposition(
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
        let mut manifest = Vec::new();
        while let Maybe::Present(_) = cursor.tile(TileName::WITH) {
            closed(site, &mut cursor, TileName::SORT)?;
            let Maybe::Present(sort) = cursor.tile(TileName::TYPE_IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(site, &mut cursor, TileName::EQUALS)?;
            let ty = site.one(cursor.operands())?;
            self.read(ty.node, Reading::ValueType(frame));
            // Every operation exercised in the subject reads the type, and the
            // subject stands after it in the tree.
            self.fixed_carriers.push(ty);
            manifest.push((sort, ty.node));
        }
        let interface = self.handled(site, written, &manifest)?;
        let held = self.bind(binder, frame)?;
        let _first = self.capabilities.insert(held);
        match interface {
            Interface::Host(ref name) => {
                let _first = self.answered.insert(held, name.clone());
            },
            Interface::Theory(ref theory) => {
                let _first = self.answered.insert(held, theory.name.clone());
                let _first = self.theory_capabilities.insert(held, Arc::clone(theory));
            },
        }
        let subject = self.block(site, &mut cursor, Frame::Inner(held))?;
        self.open_subject(site, subject)?;

        let mut cursor = Cursor::new(handlers, site.at.span);
        closed(site, &mut cursor, TileName::WITH)?;
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let mut on_return: Maybe<(NodeIndex, Placed, NodeIndex), clause::Absent> =
            Maybe::Absent(clause::Absent::Unwritten);
        let mut clauses = Vec::new();
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, at }) if label == TileName::PURE => {
                    let (result, body) = Self::clause_parameter(site, &mut cursor)?;
                    if let Maybe::Present((_, first, _)) = on_return {
                        return Err(LoweringRefusal::DuplicateDefinition {
                            span: at.span,
                            name: SurfaceName::from("pure"),
                            first: first.span,
                        });
                    }
                    let bound = self.bind(result, frame)?;
                    self.clause(site, body, Frame::Inner(bound))?;
                    on_return = Maybe::Present((body, at, result.node));
                },
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::OPER => {
                    let Maybe::Present(at) = cursor.tile(TileName::IDENTIFIER)
                    else {
                        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                    };
                    closed(site, &mut cursor, TileName::PAREN_OPEN)?;
                    let Maybe::Present(first) = cursor.tile(TileName::IDENTIFIER)
                    else {
                        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                    };
                    // `oper op(k)`: an operation that sends nothing binds its
                    // resumption alone.
                    let (payload, second) = if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                    {
                        let Maybe::Present(second) = cursor.tile(TileName::IDENTIFIER)
                        else {
                            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                        };
                        (Some(first), second)
                    }
                    else {
                        (None, first)
                    };
                    let operation = OperationName::from(self.name_at(at).as_ref());
                    // A host operation replying a buffer names its mint
                    // between the payload and the continuation; a theory's
                    // replies values of the sorts its manifest fixes.
                    let minting = matches!(interface, Interface::Host(_))
                        && mints(&operation) == Reply::Minted;
                    let (minted, continuation) = match (minting, payload) {
                        (true, Some(_)) => {
                            closed(site, &mut cursor, TileName::COMMA)?;
                            let Maybe::Present(continuation) = cursor.tile(TileName::IDENTIFIER)
                            else {
                                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                            };
                            (Some(second), continuation)
                        },
                        (true, None) => {
                            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                        },
                        (false, _) => (None, second),
                    };
                    closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
                    closed(site, &mut cursor, TileName::FAT_ARROW)?;
                    let body = site.one(cursor.operands())?;
                    let (under, mint) = if let (Some(minted), Some(payload)) = (minted, payload) {
                        // The payload binder holds the pair the body splits
                        // into the payload and the mint, placed live.
                        let unwritten = || Maybe::Absent(binder_site::Absent::Unwritten);
                        let pair = self.scope.extend(frame, SurfaceName::from(""), unwritten());
                        let resumed = self.bind(continuation, Frame::Inner(pair))?;
                        let _first = self.resumptions.insert(resumed);
                        let split = self.bind(payload, Frame::Inner(resumed))?;
                        let placed = self.scope.extend(
                            Frame::Inner(split),
                            SurfaceName::from(""),
                            unwritten(),
                        );
                        let name = self.name_at(minted);
                        self.note_binder(minted, name)?;
                        let live = self.scope.extend_linear(
                            Frame::Inner(placed),
                            name,
                            Maybe::Present(minted.span),
                        );
                        (Frame::Inner(live), Mint::Minted { mint: minted.node })
                    }
                    else {
                        let bound = match payload {
                            Some(payload) => self.bind(payload, frame)?,
                            None => self.scope.extend(
                                frame,
                                SurfaceName::from(""),
                                Maybe::Absent(binder_site::Absent::Unwritten),
                            ),
                        };
                        let resumed = self.bind(continuation, Frame::Inner(bound))?;
                        let _first = self.resumptions.insert(resumed);
                        (Frame::Inner(resumed), Mint::Unminted)
                    };
                    self.clause(site, body.node, under)?;
                    clauses.push(Clause {
                        operation,
                        payload: payload.map(|payload| payload.node),
                        continuation: continuation.node,
                        body: body.node,
                        mint,
                    });
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
        let Maybe::Present((on_return, _, result)) = on_return
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
                result,
                clauses,
            }),
        );

        Ok(())
    }

    /// The interface a capability scope names at `written`, the value sorts
    /// `manifest` fixes each beside the node of the type it writes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the host interface of the name, where the host declares one
    ///   and the manifest is empty; otherwise the theory the name resolves to
    ///   where the scope stands, read as an interface whose value sorts the
    ///   manifest fixes ([`theory::operations`]), held for the scope.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at a manifest sort the
    ///   interface does not declare, a host interface declaring none;
    ///   [`LoweringRefusal::DuplicateDefinition`] at a sort the manifest fixes
    ///   twice; the refusals of [`crate::module::Collected::presented_theory`]
    ///   for a name neither the host nor a theory answers; an unadmitted form
    ///   for a theory whose value codes no presentation;
    ///   [`LoweringRefusal::UninterfacedMember`] at the theory's name, for its
    ///   first member out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `State` fixed at `Integer` handled and exercised; a
    ///   theory refused at each fault; a manifest sort the theory does not
    ///   declare and one a host interface is written with, each refused by
    ///   name.
    /// - witness: `lower::capability::tests::a_scope_handles_a_theory_s_operations_2272`
    /// - witness: `lower::capability::tests::a_scope_s_manifest_names_only_its_theory_s_sorts_2272`
    /// - witness: `lower::capability::theory::tests::each_member_out_of_shape_is_refused_by_its_fault_2272`
    #[spec(ensures: |ret| ret.is_err() || manifest.is_empty() || matches!(ret, Ok(Interface::Theory(_))))]
    fn handled(
        &self,
        site: Site,
        written: Placed,
        manifest: &[(Placed, NodeIndex)],
    ) -> Result<Interface, LoweringRefusal<'source>>
    {
        let handled = self.name_at(written);
        let table = host(site)?;
        if let Maybe::Present(interface) = table.named(&EffectName::from(handled.as_ref())) {
            if let Some(&(sort, _)) = manifest.first() {
                return Err(LoweringRefusal::UnresolvedName {
                    span: sort.span,
                    name: self.name_at(sort),
                });
            }
            return Ok(Interface::Host(interface.name().clone()));
        }
        let (_, presentation) =
            self.collected
                .presented_theory(written.span.start(), written.span, handled)?;
        // A handler is a model of the theory: a value presenting no theory
        // has none, as `Model(T)` refuses it.
        let Ok(members) = presentation.members()
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::ModelType)));
        };
        let declared: BTreeSet<&Name> = members.sorts.iter().map(|sort| &sort.name).collect();
        let mut fixed: BTreeMap<Name, NodeIndex> = BTreeMap::new();
        let mut first: BTreeMap<Name, Placed> = BTreeMap::new();
        for &(sort, ty) in manifest {
            let name = self.name_at(sort);
            let key = Name::from(name.as_ref());
            if !declared.contains(&key) {
                return Err(LoweringRefusal::UnresolvedName {
                    span: sort.span,
                    name,
                });
            }
            if let Some(&earlier) = first.get(&key) {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: sort.span,
                    name,
                    first: earlier.span,
                });
            }
            let _first = first.insert(key.clone(), sort);
            let _fixed = fixed.insert(key, ty);
        }
        match theory::operations(&members, &fixed) {
            Ok(operations) => Ok(Interface::Theory(Arc::new(TheoryInterface {
                scope: site.at.node,
                name: EffectName::from(handled.as_ref()),
                operations,
                manifest: manifest
                    .iter()
                    .map(|&(sort, ty)| (Name::from(self.name_at(sort).as_ref()), ty))
                    .collect(),
            }))),
            Err((member, fault)) => Err(LoweringRefusal::UninterfacedMember {
                span: written.span,
                name: self.name_at(member),
                fault,
            }),
        }
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
    /// `row`, whole, and its labels' instances, open through its tail when
    /// one is written.
    ///
    /// # Specification
    /// - requires: `argument` and the row's tail are already minted or absent.
    /// - ensures: `F^⟨row⟩ A` at `origin`, each interface named whole at its
    ///   default label and each label's instance at its region, its tail
    ///   standing for the row the tail's value denotes; the argument's or the
    ///   tail's absence when it did not lower, and the unminted absence when
    ///   two labels name one instance.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::returner_row`].
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    /// - witness: `lower::capability::tests::a_row_stays_open_through_its_tail_2270`
    /// - witness: `lower::capability::tests::a_row_names_two_instances_of_one_interface_apart_2271`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::CompType(id)) => sink.origins.comp_type(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_effectful(
        &self,
        row: &WrittenRow,
        argument: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let result = match self.value_type_at(argument) {
            Maybe::Present(result) => result,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let tail = match row.tail {
            Maybe::Present(written) => match self.value_at(written) {
                Maybe::Present(value) => {
                    let tail = sink.arena.value_type_row_tail(value);
                    sink.origins.record_value_type(tail, origin);
                    Some(tail)
                },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Maybe::Absent(_) => None,
        };
        let mut placed = Vec::with_capacity(row.interfaces.len().saturating_add(row.placed.len()));
        let interfaces = row
            .interfaces
            .iter()
            .map(|interface| (interface, Region::Held));
        let labels = row
            .placed
            .iter()
            .map(|&(ref interface, region)| (interface, region));
        for (interface, region) in interfaces.chain(labels) {
            match sink.signature(interface, origin) {
                Maybe::Present(signature) => placed.push((signature, region)),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let Ok(effects) = EffectRow::from_placed(placed)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let id = sink
            .arena
            .comp_type_returner_with_effects(result, effects.with_tail(tail));
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

    /// The signature of `interface` in the module's arena: the host's, or the
    /// theory's, minted at the first form naming its scope and the same
    /// signature for every form after.
    ///
    /// # Specification
    /// - requires: every type a theory operation names is already minted or
    ///   absent.
    /// - ensures: the host interface's signature, as [`Sink::signature`]; a
    ///   theory's, one operation per theory operation, its payload and its
    ///   reply each [`Self::tuple_at`] of the operation's types, kept by the
    ///   scope so every later call answers it.
    /// - fails: never; the first absence among the types, or the unminted
    ///   absence for a theory naming one operation twice, which the theory's
    ///   own presentation rules out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope over `State` and the exercises in its subject
    ///   check against one signature.
    /// - witness: `lower::capability::tests::a_scope_handles_a_theory_s_operations_2272`
    #[spec(ensures: |ref ret| match *ret {
        | Maybe::Present(ref signature) => match *interface {
            | Interface::Host(ref name) => signature.name() == name,
            | Interface::Theory(ref theory) => signature.name() == &theory.name,
        },
        | Maybe::Absent(_) => true,
    })]
    fn interface_signature(
        &self,
        interface: &Interface,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<EffectSig, lowered::Absent>
    {
        let theory = match *interface {
            Interface::Host(ref name) => return sink.signature(name, origin),
            Interface::Theory(ref theory) => theory,
        };
        if let Some(minted) = sink.theories.get(&theory.scope) {
            return Maybe::Present(minted.clone());
        }
        let operations = theory
            .operations
            .iter()
            .map(|operation| {
                let payload = match self.tuple_at(&operation.payload, sink, origin) {
                    Maybe::Present(payload) => payload,
                    Maybe::Absent(reason) => return Err(reason),
                };
                let reply = match self.tuple_at(&operation.reply, sink, origin) {
                    Maybe::Present(reply) => reply,
                    Maybe::Absent(reason) => return Err(reason),
                };
                Ok(EffectOp {
                    name: operation.name.clone(),
                    payload,
                    reply,
                })
            })
            .collect::<Result<Vec<EffectOp>, lowered::Absent>>();
        let operations = match operations {
            Ok(operations) => operations,
            Err(reason) => return Maybe::Absent(reason),
        };
        let Ok(signature) = EffectSig::new(theory.name.clone(), operations)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let _first = sink.theories.insert(theory.scope, signature.clone());
        Maybe::Present(signature)
    }

    /// The type of the values whose written types are `types`: the unit for
    /// none, its own for one, and their tuple for several, as an exercise
    /// passes its arguments.
    ///
    /// # Specification
    /// - requires: every node of `types` is already minted or absent.
    /// - ensures: the one type's minted id for one; otherwise the product of
    ///   the minted ids, in order, at `origin`.
    /// - fails: never; the first absence among the types.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::interface_signature`]: `get` replies one
    ///   type and sends none.
    /// - witness: `lower::capability::tests::a_scope_handles_a_theory_s_operations_2272`
    #[spec(ensures: |ret| types.len() == 1 || match ret {
        | Maybe::Present(id) => matches!(sink.arena.value_type(id), Some(&ValueType::Product(ref components)) if components.len() == types.len()),
        | Maybe::Absent(_) => true,
    })]
    fn tuple_at(
        &self,
        types: &[NodeIndex],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        if let &[only] = types {
            return self.value_type_at(only);
        }
        let components = types
            .iter()
            .map(|&ty| match self.value_type_at(ty) {
                Maybe::Present(id) => Ok(id),
                Maybe::Absent(reason) => Err(reason),
            })
            .collect::<Result<Vec<ValueTypeId>, lowered::Absent>>();
        match components {
            Ok(components) => {
                let id = sink.arena.value_type_product(&components);
                sink.origins.record_value_type(id, origin);
                Maybe::Present(id)
            },
            Err(reason) => Maybe::Absent(reason),
        }
    }

    /// Mint the exercise or the perform `exercised` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the exercise of the operation, under its interface's whole
    ///   signature, of the capability with the payload its arguments make, or,
    ///   for an interface named, the perform of the operation under that
    ///   signature with the payload, at `origin`, and a label at the head
    ///   naming the operation's type, its payload to the returner of its reply;
    ///   the first absence among the children.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::exercise`]; the head answers at the
    ///   operation it selects.
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `lower::capability::tests::an_exercise_s_head_answers_at_its_operation`
    /// - witness: `lower::capability::tests::an_operation_is_performed_by_its_interface_s_name_2279`
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
        let capability = match exercised.performer {
            Performer::Capability(node, _) => match self.value_at(node) {
                Maybe::Present(capability) => Some(capability),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Performer::Interface(_) => None,
        };
        let payload = match self.mint_payload(exercised.payload, sink, origin) {
            Maybe::Present(payload) => payload,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        self.interface_signature(&exercised.interface, sink, origin)
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
                let id = match capability {
                    Some(capability) => sink.arena.computation_exercise(
                        capability,
                        signature,
                        exercised.operation.clone(),
                        payload,
                    ),
                    None => sink.arena.computation_perform(
                        signature,
                        exercised.operation.clone(),
                        payload,
                    ),
                };
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

    /// Mint the abandonment of the continuation at `continuation`.
    ///
    /// # Specification
    /// - requires: the continuation's node is already minted or absent.
    /// - ensures: the abandonment of the continuation at `origin`; the
    ///   continuation's absence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::abandonment`].
    /// - witness: `lower::capability::tests::a_clause_abandons_its_continuation_1334`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_abandon(
        &self,
        continuation: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.value_at(continuation).map(|stack| {
            let id = sink.arena.computation_abandon(stack);
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
    ///   capability's written name recorded as the scope's binder and each
    ///   clause's binders — the result, and each operation clause's payload and
    ///   continuation by its place — as the scope's clause binders, and, for a
    ///   scope over a theory, the theory and each sort its manifest fixes
    ///   beside the type it fixes it to, in the order written, as the scope's
    ///   theory; the first absence among the bodies.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::capability_scope`].
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    /// - witness: `lower::capability::tests::a_scope_records_where_its_clauses_bind_1439`
    /// - witness: `lower::capability::tests::a_scope_records_the_theory_and_sorts_it_handles_2382`
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
        for clause in &scoped.clauses {
            let mut body: ComputationId =
                match self.mint_body(clause_body(clause.body), sink, origin) {
                    Maybe::Present(body) => body,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
            if let Mint::Minted { mint } = clause.mint {
                // Under the pair and the continuation: split the pair, the
                // payload then the mint, and place the mint live.
                let minted = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(minted, origin);
                let placed = sink.arena.computation_session(SessionAction::Place {
                    payload: minted,
                    body,
                });
                sink.origins.record_computation(placed, origin);
                if let Maybe::Present(name) = self.origin_at(mint) {
                    sink.origins.record_binder(placed, name);
                }
                let pair = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
                sink.origins.record_value(pair, origin);
                body = sink
                    .arena
                    .computation_split(pair, ComponentCount::from(2_usize), placed);
                sink.origins.record_computation(body, origin);
                if let Some(payload) = clause.payload
                    && let Maybe::Present(name) = self.origin_at(payload)
                {
                    sink.origins.record_binder(body, name);
                }
            }
            clauses.push(EffectClause {
                operation: clause.operation.clone(),
                body,
            });
        }
        self.interface_signature(&scoped.interface, sink, origin)
            .map(|signature| {
                let id =
                    sink.arena
                        .computation_scope(signature, subject, on_return, Arc::from(clauses));
                let scope = sink.computation(id, origin);
                if let Maybe::Present(name) = self.origin_at(scoped.binder) {
                    sink.origins.record_binder(id, name);
                }
                let written = core::iter::once((ClauseBinder::Result, Some(scoped.result))).chain(
                    scoped
                        .clauses
                        .iter()
                        .enumerate()
                        .flat_map(|(place, clause)| {
                            let place = ClausePlace::from(place);
                            [
                                (ClauseBinder::Payload(place), clause.payload),
                                (ClauseBinder::Continuation(place), Some(clause.continuation)),
                            ]
                        }),
                );
                for (binder, node) in written {
                    if let Some(node) = node
                        && let Maybe::Present(name) = self.origin_at(node)
                    {
                        sink.origins.place_clause_binder(id, binder, name);
                    }
                }
                if let Interface::Theory(ref theory) = scoped.interface {
                    let sorts = theory
                        .manifest
                        .iter()
                        .filter_map(|&(ref sort, ty)| match self.value_type_at(ty) {
                            Maybe::Present(fixed) => Some((sort.clone(), fixed)),
                            Maybe::Absent(_) => None,
                        })
                        .collect();
                    sink.origins.record_scope_theory(id, WrittenModel {
                        theory: Name::from(theory.name.as_ref()),
                        sorts,
                    });
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
