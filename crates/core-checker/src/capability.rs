//! The capability rules: `Cap E` is a context hypothesis carrying the
//! authority `E`.
//!
//! The leaves — the authority as a set of (interface, operation) grant atoms,
//! the region a capability lives for and its grade — are `gandr-core-term`'s
//! `effect::capability`. This module states the six rules the judgement runs
//! over them, and holds the pieces of those rules that read no machine state.
//!
//! # The rules
//!
//! ```text
//!                Γ ⊢ v ⇒ Cap_ρ E    E′ ⊆ E    ρ outlives ρ′
//!   Attenuate   ───────────────────────────────────────────
//!                Γ ⊢ v ⇐ Cap_ρ′ E′
//!
//!                Γ ⊢ c ⇒ Cap_ρ E    op : A → B ∈ I    (I, op) ∈ E    Γ ⊢ v ⇐ A
//!   Exercise    ────────────────────────────────────────────────────────────────
//!                Γ ⊢ c.op v ⇒ F^⟨I⟩ B
//!
//!                Γ, c : Cap_ρ ⟨I⟩ ⊢ M ⇐ F^⟨I | ε⟩ A    ρ ∉ (A, ε)
//!                Γ, x : A ⊢ N ⇐ F^ε A    Γ, p : A_op, k : U(F^ε B_op → F^ε A) ⊢ N_op ⇐ F^ε A
//!   Scope       ──────────────────────────────────────────────────────────────────────────
//!                Γ ⊢ scope c : I in M with { return x ↦ N; op p k ↦ N_op } ⇐ F^ε A
//!
//!                M reaches φ    N reaches ψ    φ ⋈ ψ
//!   Separate    ─────────────────────────────────────────
//!                Γ ⊢ fork (x : S) { M } as y; N ⇐ F^ε A
//!
//!   φ ⋈ ψ  iff  every operation φ(I) ∪ ψ(I) holds only reads the host,
//!               for each interface I that both φ and ψ reach
//! ```
//!
//! - **Introduction at the entry.** A declaration with a signature and no body
//!   whose type is a held capability is a hypothesis the host supplies; the
//!   ledger owes it like every hole. Under a grant, [`CheckingContext::grant`],
//!   one claiming authority the grant does not hold is
//!   [`CheckRefusal::CapabilityUngranted`].
//! - **No forgery.** No term former introduces `Cap`. A value checked at a
//!   capability type that is neither a capability hypothesis nor a hole is
//!   [`CheckRefusal::CapabilityForged`], whether it synthesised another type or
//!   is a checking form such as a thunk or a tuple.
//! - **Attenuate** is subsumption, decided by conversion: authority narrows by
//!   inclusion on grant atoms and a region may only shorten. Widening is
//!   [`CheckRefusal::CapabilityAmplified`]; a region ending before the one
//!   expected is [`CheckRefusal::CapabilityEscaped`].
//! - **Exercise** synthesises. An operation the authority does not grant is
//!   [`CheckRefusal::CapabilityOutsideAuthority`]; a value of another type in
//!   capability position is a shape mismatch wanting a capability.
//! - **Scope** checks, as a deep handler does, and introduces its capability in
//!   the region one deeper than every scope around it. Its answer may not
//!   mention that region or a deeper one: [`CheckRefusal::CapabilityEscaped`]
//!   at the scope.
//! - **Separate** is the premise of a fork, whose halves run as peers. Each
//!   half's footprint, [`Footprint`], is the host operations the names it
//!   mentions let it perform: a held capability at its authority, a returner's
//!   row at each interface it names, and an operation performed by name. The
//!   halves share an interface only where every operation either holds on it
//!   only reads ([`gandr_core_term::effect::host::access`]); otherwise
//!   [`CheckRefusal::FootprintsOverlap`] at the fork, naming both footprints
//!   and what they share. A nested fork's footprints join their enclosing
//!   half's.
//!
//! # Decisions
//!
//! - **The exercise's row is the interface.** The result row of `c.op v` names
//!   the interface `I` the operation belongs to, whole, rather than the
//!   capability's authority. A row entry is a whole interface, and a handler
//!   discharges one by name; a restricted entry would never equal the
//!   interface's own entry at a handler or a row inclusion. Authority is
//!   checked at the exercise, against the capability's type, and the row only
//!   records which handler answers. Reversal: rows whose entries are grant
//!   atoms, when a handler may discharge part of an interface.
//! - **Regions are depths, and escape is refused twice.** A scope's region is
//!   its nesting depth, so no region is ever named and two sibling scopes share
//!   one depth without meeting. The capability escapes through a value boundary
//!   — returned, passed, stored — only by subsumption to a region it does not
//!   outlive, which conversion refuses; the side condition `ρ ∉ (A, ε)` refuses
//!   an answer type that mentions the region outright. The alternative, a
//!   region variable per scope and region polymorphism, is the second-class
//!   capabilities of Brachthäuser, Schuster and Ostermann (_Effects as
//!   capabilities: effect handlers and lightweight effect polymorphism_, OOPSLA
//!   2020). Reversal: when a function must accept a capability of its caller's
//!   scope, which a held parameter type refuses.
//! - **A scoped capability is exercised where it was introduced.** Every
//!   source-spelled `Cap` is held, so a scoped capability cannot be passed to a
//!   function or stored in a declaration: it is used lexically, within its
//!   scope's subject. That is the region rule, not a separate restriction.
//! - **One handler per interface.** Rows are keyed by interface, so a scope
//!   over `I` answers every operation of `I` its subject requests, including
//!   one exercised through an outer capability of `I`. The authority check
//!   still runs against the outer capability, so this narrows who answers an
//!   operation, never what may be requested. Reversal: rows tagged by region,
//!   so a request names the scope that answers it.
//! - **Durable only.** A consumable capability is refused at formation by
//!   [`CheckRefusal::CapabilityConsumable`]: the linear zone it belongs in
//!   admits no binder, so checking it as durable would let it be exercised
//!   twice. Revocation is the end of the region; nothing revokes a capability
//!   mid-run.
//! - **A footprint is read, not recorded.** A closure's type already records
//!   the summaries a footprint is made of, a held capability's authority and a
//!   returner's row, so a half's footprint is read off the types of the names
//!   it mentions and no type gains a summary. It is keyed by interface, since
//!   two capabilities over one interface reach one host, and counts a row entry
//!   whole, by the first decision: a helper that only reads `Fs` counts as
//!   changing it. A scoped capability is answered by its scope's handler, not
//!   by the host, and adds nothing. A row's tail adds nothing either: a tail is
//!   instantiated only by a thunk the half mentions, whose own type is read.
//!   Reversal: a row entry attenuated to operations (#2878), and a footprint
//!   keyed finer than an interface when the host's state is partitioned, such
//!   as a path within the file system.
//! - **Nothing persists.** The kernel admits no effectful former, so the bridge
//!   refuses a capability type, an exercise and a scope by name, as it refuses
//!   a request and a handler. Authority is decided here, completely, and an
//!   exercise carries no evidence beyond the operation it names. Reversal: when
//!   the kernel admits effectful computations.
//!
//! # References
//!
//! - `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: the Separate rule,
//!   two closures over one durable capability under a fork refused and their
//!   read-only twin accepted (try-first 1).
//! - Yichen Xu, Oliver Bračevac, Cao Nguyen Pham, Yaoyu Zhao and Martin
//!   Odersky. "System Capybara: Tracking Capabilities for Separation and
//!   Freshness." 2026. `arXiv:2607.09383`, § 4.5: two footprints are separate
//!   when every location they share is read-only in both, read here at an
//!   interface.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderPrecedence;
use gandr_core_term::CompType;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectLabel;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionBinder;
use gandr_core_term::effect::capability::RegionOrder;
use gandr_core_term::effect::host::AuthorityError;
use gandr_core_term::effect::host::HostAccess;
use gandr_core_term::effect::host::HostSignatures;
use gandr_core_term::effect::host::access;
use gandr_core_term::row::RowInclusion;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::ValueTypeView;
use crate::view::value_type_view;
use crate::worlds::Entry;
use crate::worlds::HostEntry;
use crate::worlds::WorldName;

/// The authority the host grants a module's held capabilities at the
/// checker's entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Grants
{
    /// No grant is named: every held capability is a hypothesis the ledger
    /// owes.
    Unbounded,
    /// Every held capability's authority falls within this one.
    Within(EffectRow),
}

/// The host operations a run grants and the entry it enters every
/// declaration at, by name: what a driver states before any arena holds the
/// types those operations carry or any source declares the worlds.
///
/// # Specification
/// - ensures: every operation a grant names is one the host declares, checked
///   when the grant is formed; [`HostGrant::grants`] mints it into a module's
///   own arena as the [`Grants`] its checking context is bounded by, and
///   [`HostGrant::entry`] reads its worlds against the ones a module declares
///   as the [`HostEntry`] its checking context enters at.
///
/// # Adequacy
/// - hypothesis: L3 — a grant of host operations bounds a held capability
///   within it and refuses one beyond it; an undeclared operation is refused
///   when the grant is formed; the unbounded grant bounds nothing; a named
///   entry reads as the module's worlds, or as undeclared where the module
///   declares one of them nowhere.
/// - witness: `capability::tests::a_named_grant_bounds_the_held_capabilities`
/// - witness: `capability::tests::a_named_entry_reads_as_the_declared_worlds`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HostGrant
{
    /// The host operations every held capability is bounded by.
    operations: Named,
    /// The worlds of the host's entry, its home first and then the world of
    /// each capability: none for no entry.
    worlds: Vec<WorldName>,
}

/// What a [`HostGrant`] names.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Named
{
    /// No grant: [`Grants::Unbounded`].
    Unbounded,
    /// Exactly these host operations, each declared by the host.
    Within(BTreeSet<OperationName>),
}

impl HostGrant
{
    /// No grant and no entry: every held capability is a hypothesis the
    /// ledger owes, and every declaration stands where it states.
    pub const UNBOUNDED: Self = Self {
        operations: Named::Unbounded,
        worlds: Vec::new(),
    };

    /// The grant of exactly `operations`, each the host's.
    ///
    /// # Specification
    /// - ensures: a grant naming the operations, a repeated one once, and no
    ///   entry.
    /// - fails: an operation no host interface offers.
    /// - panics: none.
    ///
    /// # Errors
    /// [`AuthorityError::Undeclared`] for the first operation the host does
    /// not declare; [`AuthorityError::Conflict`] never, for the host's own
    /// table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostGrant`].
    /// - witness: `capability::tests::a_named_grant_bounds_the_held_capabilities`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |grant| {
        matches!(grant.operations, Named::Within(_)) && grant.worlds.is_empty()
    }))]
    #[inline]
    pub fn within<'name, Operations>(operations: Operations) -> Result<Self, AuthorityError>
    where
        Operations: IntoIterator<Item = &'name OperationName>,
    {
        let named: BTreeSet<OperationName> = operations.into_iter().cloned().collect();
        let host = HostSignatures::new(&mut CoreArena::new()).map_err(AuthorityError::Conflict)?;
        let _authority = host.authority(&named)?;
        Ok(Self {
            operations: Named::Within(named),
            worlds: Vec::new(),
        })
    }

    /// This grant, entering every declaration at `worlds`: its home first,
    /// then the world of each capability, as an `entry` attribute names
    /// them.
    ///
    /// # Specification
    /// - ensures: the same operations, and the entry `worlds` names in order;
    ///   no entry for no world.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostGrant::entry`].
    /// - witness: `capability::tests::a_named_entry_reads_as_the_declared_worlds`
    #[spec(captures: count = worlds.len(), ensures: |ret| ret.worlds.len() == count)]
    #[inline]
    #[must_use]
    pub fn entering(
        self,
        worlds: Vec<WorldName>,
    ) -> Self
    {
        Self {
            operations: self.operations,
            worlds,
        }
    }

    /// The grant as a checking context's bound, minted into `arena`.
    ///
    /// # Specification
    /// - ensures: no bound for the unbounded grant, minting nothing; otherwise
    ///   the authority granting exactly the named operations over the host's
    ///   interfaces minted into `arena`.
    /// - fails: never: the names were checked against this table when the grant
    ///   was formed, and a table that refused them here would grant nothing,
    ///   closing the bound rather than opening it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostGrant`].
    /// - witness: `capability::tests::a_named_grant_bounds_the_held_capabilities`
    #[spec(ensures: |ret| matches!(ret, Grants::Unbounded) == matches!(self.operations, Named::Unbounded))]
    #[inline]
    #[must_use]
    pub fn grants(
        &self,
        arena: &mut CoreArena,
    ) -> Grants
    {
        let Named::Within(ref named) = self.operations
        else {
            return Grants::Unbounded;
        };
        let authority = match HostSignatures::new(arena) {
            Ok(host) => match host.authority(named) {
                Ok(authority) => authority,
                Err(_refused) => EffectRow::EMPTY,
            },
            Err(_conflict) => EffectRow::EMPTY,
        };
        Grants::Within(authority)
    }

    /// The grant's entry as a checking context's, read against the worlds a
    /// module declares by name.
    ///
    /// # Specification
    /// - ensures: [`HostEntry::Unbounded`] for a grant naming no world;
    ///   [`HostEntry::Undeclared`] when a world it names is not in `declared`;
    ///   otherwise [`HostEntry::Within`] the entry at the first world's
    ///   declaration, holding one capability per later world's, in order.
    /// - fails: never — an undeclared world is an answer, refused where a
    ///   declaration is judged at it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no world, declared worlds and a world the module does
    ///   not declare separate the three answers.
    /// - witness: `capability::tests::a_named_entry_reads_as_the_declared_worlds`
    #[spec(ensures: |ret| match ret {
        HostEntry::Unbounded => self.worlds.is_empty(),
        HostEntry::Undeclared => !self.worlds.is_empty(),
        HostEntry::Within(ref entry) => entry.capabilities().len() == self.worlds.len().saturating_sub(1),
    })]
    #[inline]
    #[must_use]
    pub fn entry(
        &self,
        declared: &BTreeMap<WorldName, ConstantIndex>,
    ) -> HostEntry
    {
        let mut worlds = Vec::with_capacity(self.worlds.len());
        for world in &self.worlds {
            let Some(&constant) = declared.get(world)
            else {
                return HostEntry::Undeclared;
            };
            worlds.push(constant);
        }
        match Entry::declared(&worlds) {
            Maybe::Present(entry) => HostEntry::Within(entry),
            Maybe::Absent(_) => HostEntry::Unbounded,
        }
    }
}

/// Whether a type mentions a region that ends too soon.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reach
{
    /// Nothing in the type lives in such a region.
    Clear,
    /// A capability in the type lives in such a region.
    Mentions,
    /// A value in the type is kept in such a region.
    Keeps,
}

/// Decide whether the capability `capability`, of type `classifier` whose weak
/// head is `head`, grants the operation `operation` of `signature` that the
/// exercise `at` requests.
///
/// # Specification
/// - requires: `operation` is an operation of `signature`.
/// - ensures: success when `head` is a capability whose authority grants the
///   operation with the interface's own payload and reply types, and when
///   `head` is the unknown type, which grants every operation.
/// - fails: [`CheckRefusal::CapabilityOutsideAuthority`] for a capability that
///   does not grant it; [`CheckRefusal::ShapeMismatch`] at `capability`,
///   wanting [`ExpectedShape::Capability`], for a type of another former;
///   [`CheckRefusal::UnknownOperation`] for an operation outside `signature`.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a granted operation, one the authority withholds and a
///   string in capability position, each asserted as the exact answer.
/// - witness: `capability::tests::an_operation_is_exercised_only_within_the_authority`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::CapabilityOutsideAuthority { at: named, capability: found }) => named == at && found == classifier,
    | Err(CheckRefusal::ShapeMismatch { at: named, wanted, .. }) => named == TermNode::Value(capability) && wanted == ExpectedShape::Capability,
    | Ok(()) | Err(_) => true,
})]
pub fn authorise(
    arena: &CoreArena,
    at: ComputationId,
    capability: ValueId,
    classifier: ValueTypeId,
    head: ValueTypeId,
    signature: &EffectSig,
    operation: &OperationName,
) -> Result<(), CheckRefusal>
{
    match value_type_view(arena, head)? {
        ValueTypeView::Capability { authority, .. } => {
            let requested = signature
                .restrict([operation])
                .map_err(|_unknown| CheckRefusal::UnknownOperation { at })?;
            match EffectRow::singleton(requested).grants_within(authority, arena) {
                RowInclusion::Included => Ok(()),
                RowInclusion::Excluded => Err(CheckRefusal::CapabilityOutsideAuthority {
                    at,
                    capability: classifier,
                }),
            }
        },
        ValueTypeView::Unknown => Ok(()),
        ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Bridge { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Sum(..)
        | ValueTypeView::List(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(..)
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Session(_)
        | ValueTypeView::Abstract(_)
        | ValueTypeView::World(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Row
        | ValueTypeView::RowTail(_) => Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(capability),
            wanted: ExpectedShape::Capability,
            found: TypeNode::Value(classifier),
        }),
    }
}

/// Whether the type `root` mentions a region that ends while `outside` is
/// still live: the scope rule's side condition `ρ ∉ (A, ε)`, read from the
/// region around the scope, and the capture rule's, read from the region the
/// captor is kept in.
///
/// # Specification
/// - ensures: [`Reach::Mentions`] when a capability type reachable through
///   `root`'s type formers lives in a region that does not outlive `outside`,
///   and [`Reach::Keeps`] when a kept type there is kept in such a region,
///   whichever the walk meets first; [`Reach::Clear`] otherwise. Every region
///   outlives itself, so a type that names only `outside` and the regions
///   around it is clear. A data type's quoted arguments are read; a code is not
///   decoded.
/// - fails: [`CheckRefusal::DanglingNode`] for a reachable type that does not
///   resolve.
/// - panics: none.
/// - executable: none — the walk is the specification; [`first_region`] states
///   the walk.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — an answer returning the scope's own capability, one whose
///   row carries it, and one returning a held capability, each asserted as
///   refused or checked; a thunk kept at the scope's region returned from it is
///   refused, and one kept at a region its definition abstracts is not.
/// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
/// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
/// - witness: `capability::tests::a_bound_region_outlives_every_scope_and_no_held_one_1221`
#[inline]
pub fn reaches(
    arena: &CoreArena,
    root: TypeNode,
    outside: Region,
) -> Result<Reach, CheckRefusal>
{
    first_region(arena, root, |region| {
        region.outlives(outside) == RegionOrder::EndsFirst
    })
}

/// How the type `root` reaches a region its definition abstracts, `A at r`
/// under `@[r : Region]`, anywhere a region stands in it.
///
/// # Specification
/// - ensures: what [`first_region`] answers choosing every [`Region::Bound`]:
///   [`Reach::Clear`] exactly when the type names no region binder, without a
///   walk for a type minted before its arena's first binder.
/// - fails: [`CheckRefusal::DanglingNode`] for a reachable type that does not
///   resolve.
/// - panics: none.
/// - executable: none — as [`reaches`].
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a function type keeping its parameter at a bound region
///   names one, and the same type at a scope's region names none.
/// - witness: `capability::tests::a_bound_region_outlives_every_scope_and_no_held_one_1221`
#[inline]
pub fn abstracts(
    arena: &CoreArena,
    root: TypeNode,
) -> Result<Reach, CheckRefusal>
{
    if binder_precedence(arena, root) == BinderPrecedence::Before {
        return Ok(Reach::Clear);
    }
    first_region(arena, root, |region| matches!(region, Region::Bound(_)))
}

/// Where the type `root` stands against its arena's first type naming a region
/// binder.
///
/// # Specification
/// trivial.
#[inline]
pub fn binder_precedence(
    arena: &CoreArena,
    root: TypeNode,
) -> BinderPrecedence
{
    match root {
        TypeNode::Value(at) => arena.value_type_binder_precedence(at),
        TypeNode::Computation(at) => arena.comp_type_binder_precedence(at),
    }
}

/// The region binders the type `root` names, `A at r` under `@[r : Region]`,
/// wherever a region stands in it, each once, in ascending order.
///
/// # Specification
/// - ensures: exactly the binders of the [`Region::Bound`] regions
///   [`first_region`] meets, read through every capability and kept type; none,
///   without a walk, for a type minted before its arena's first binder.
/// - fails: [`CheckRefusal::DanglingNode`] for a reachable type that does not
///   resolve.
/// - panics: none.
/// - executable: none — as [`reaches`].
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a function type keeping one value at each of two binders,
///   one of them twice, names both once.
/// - witness: `regioned::tests::a_call_places_each_binder_at_the_shortest_region_shown_1221`
#[inline]
pub fn binders(
    arena: &CoreArena,
    root: TypeNode,
) -> Result<alloc::collections::BTreeSet<RegionBinder>, CheckRefusal>
{
    let mut named = alloc::collections::BTreeSet::new();
    if binder_precedence(arena, root) == BinderPrecedence::Before {
        return Ok(named);
    }
    let _clear = first_region(arena, root, |region| {
        if let Region::Bound(binder) = region {
            let _first = named.insert(binder);
        }
        false
    })?;
    Ok(named)
}

/// The first capability or kept type the type `root` reaches through its
/// formers whose region `chosen` picks: [`Reach::Mentions`] for a capability,
/// [`Reach::Keeps`] for a kept type, [`Reach::Clear`] for none.
///
/// # Specification
/// - ensures: a capability or kept type whose region `chosen` passes over is
///   read through, its authority's types and its kept value; a data type's and
///   a codata type's quoted arguments are read; a code is not decoded.
/// - fails: [`CheckRefusal::DanglingNode`] for a reachable type that does not
///   resolve.
/// - panics: none.
/// - executable: none — the answer is the walk itself; a clause restating it
///   would walk the type again.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each node is popped once
///   per path that reaches it, and the arena is acyclic.
/// - measure: the paths under `root` not yet popped.
///
/// # Adequacy
/// - hypothesis: L3 — as [`reaches`] and [`abstracts`].
/// - witness: `capability::tests::a_bound_region_outlives_every_scope_and_no_held_one_1221`
/// - witness: `capability::tests::a_binder_is_named_through_every_former`
fn first_region<Chosen>(
    arena: &CoreArena,
    root: TypeNode,
    mut chosen: Chosen,
) -> Result<Reach, CheckRefusal>
where
    Chosen: FnMut(Region) -> bool,
{
    let mut pending = alloc::vec![root];
    while let Some(node) = pending.pop() {
        if let TypeNode::Value(at) = node {
            let found = arena.value_type(at).ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Type(node),
            })?;
            if let ValueType::Capability { region, .. } = *found
                && chosen(region)
            {
                return Ok(Reach::Mentions);
            }
            if let ValueType::Kept { region, .. } = *found
                && chosen(region)
            {
                return Ok(Reach::Keeps);
            }
        }
        successors(arena, node, &mut pending)?;
    }
    Ok(Reach::Clear)
}

/// Push onto `pending` every type the type `node` names through its own
/// former: a capability's authority's types, a kept type's value, a data or
/// codata type's quoted arguments, a returner's result and row, and each
/// component, domain and codomain. A code is not decoded.
///
/// # Specification
/// - ensures: `pending` grows by the types `node`'s former names, and by
///   nothing for a leaf.
/// - fails: [`CheckRefusal::DanglingNode`] for a `node` that does not resolve.
/// - panics: none.
/// - executable: none — the answer is the former's own children; a clause
///   restating it would match the former again.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`first_region`] and [`Footprint::reach`], which walk
///   every former through it.
/// - witness: `capability::tests::a_binder_is_named_through_every_former`
/// - witness: `capability::tests::a_footprint_reads_held_authority_and_rows_through_every_former`
fn successors(
    arena: &CoreArena,
    node: TypeNode,
    pending: &mut Vec<TypeNode>,
) -> Result<(), CheckRefusal>
{
    let dangling = CheckRefusal::DanglingNode {
        node: CoreNode::Type(node),
    };
    match node {
        TypeNode::Value(at) => match *arena.value_type(at).ok_or(dangling)? {
            ValueType::Capability { ref authority, .. } => {
                pending.extend(authority.types().map(TypeNode::Value));
            },
            ValueType::Kept { value, .. } => pending.push(TypeNode::Value(value)),
            ValueType::Data { ref arguments, .. } => {
                pending.extend(quoted(arena, arguments));
            },
            ValueType::Record(ref fields) => {
                pending.extend(fields.values().copied().map(TypeNode::Value));
            },
            ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                pending.extend(components.iter().copied().map(TypeNode::Value));
            },
            ValueType::List(inner)
            | ValueType::Lift { inner, .. }
            | ValueType::Path { carrier: inner, .. }
            | ValueType::Bridge { carrier: inner, .. }
            | ValueType::Flow { carrier: inner, .. }
            | ValueType::Staged { base: inner, .. } => pending.push(TypeNode::Value(inner)),
            ValueType::Thunk(body) => pending.push(TypeNode::Computation(body)),
            ValueType::StaticPi { domain, codomain }
            | ValueType::Sigma {
                first: domain,
                second: codomain,
            } => {
                pending.extend([TypeNode::Value(domain), TypeNode::Value(codomain)]);
            },
            ValueType::Stack { input, output } => {
                pending.extend([TypeNode::Computation(input), TypeNode::Computation(output)]);
            },
            ValueType::Session(ref session) => {
                pending.extend(session.payloads().iter().copied().map(TypeNode::Value));
            },
            ValueType::World(ref world) => {
                pending.extend(world.types().map(TypeNode::Value));
            },
            ValueType::PathUniverse(..)
            | ValueType::Run(_)
            | ValueType::Prefix(_)
            | ValueType::Dialogue(_)
            | ValueType::Web
            | ValueType::Base(_)
            | ValueType::Universe { .. }
            | ValueType::Element { .. }
            | ValueType::Abstract(_)
            | ValueType::Unknown
            | ValueType::Buffer
            | ValueType::Row
            | ValueType::RowTail(_) => {},
        },
        TypeNode::Computation(at) => match *arena.comp_type(at).ok_or(dangling)? {
            CompType::Returner {
                result,
                ref effects,
            } => {
                pending.push(TypeNode::Value(result));
                pending.extend(effects.types().map(TypeNode::Value));
            },
            CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => {
                pending.extend([TypeNode::Value(domain), TypeNode::Computation(codomain)]);
            },
            CompType::With(ref components) => {
                pending.extend(components.iter().copied().map(TypeNode::Computation));
            },
            CompType::Codata { ref arguments, .. } => {
                pending.extend(quoted(arena, arguments));
            },
            CompType::Element { .. } | CompType::Unknown => {},
        },
    }
    Ok(())
}

/// The types a data or codata type's arguments quote, in order: a value
/// argument that quotes no type names none.
///
/// # Specification
/// trivial.
fn quoted<'arena>(
    arena: &'arena CoreArena,
    arguments: &'arena [ValueId],
) -> impl Iterator<Item = TypeNode> + 'arena
{
    arguments
        .iter()
        .filter_map(|&argument| match arena.value(argument) {
            Some(&Value::Quote(quoted)) => Some(TypeNode::Value(quoted)),
            Some(&Value::QuoteComputation(quoted)) => Some(TypeNode::Computation(quoted)),
            Some(_) | None => None,
        })
}

/// What one half of a fork may do to the host: each interface it may use,
/// with the operations it may perform there. A half's footprint is read off
/// the types of the names it mentions and the operations it performs by
/// name, so a closure's footprint is the summary its type already records:
/// a held capability's authority, and the row of each returner it reaches.
/// Two halves are separate when no interface is in both footprints, or every
/// operation either performs on a shared one only reads the host
/// ([`gandr_core_term::effect::host::access`]).
///
/// # Specification
/// - ensures: one entry per interface, holding each operation once with the
///   payload and reply types its interface gives it.
///
/// # Adequacy
/// - hypothesis: L3 — two children over one capability granting `read` and
///   `write` are refused naming both footprints; two holding `read` only are
///   accepted; a scoped capability and a row's tail add nothing.
/// - witness: `capability::tests::a_footprint_reads_held_authority_and_rows_through_every_former`
/// - witness: `judgement::session::tests::two_halves_share_a_capability_only_to_read_through_it_2789`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Footprint(BTreeMap<EffectName, BTreeMap<OperationName, EffectOp>>);

impl Footprint
{
    /// Add every operation the type `root` lets a holder perform on the
    /// host: each held capability's authority, and each interface of each
    /// returner's row, through every former [`successors`] walks. A
    /// capability a scope introduces is answered by the scope, not the host,
    /// and a row's tail names no interface; neither adds anything.
    ///
    /// # Specification
    /// - ensures: every operation already held is still held.
    /// - fails: [`CheckRefusal::DanglingNode`] for a reachable type that does
    ///   not resolve.
    /// - panics: none.
    /// - executable: none — the clause frames the footprint as it was before
    ///   the call, which a predicate would copy whole.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `while let` worklist, not recursion; each node is popped
    ///   once per path that reaches it, and the arena is acyclic.
    /// - measure: the paths under `root` not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held capability inside a thunk's domain, a
    ///   returner's row, a scoped capability and a row tail, each read.
    /// - witness: `capability::tests::a_footprint_reads_held_authority_and_rows_through_every_former`
    pub(crate) fn reach(
        &mut self,
        arena: &CoreArena,
        root: TypeNode,
    ) -> Result<(), CheckRefusal>
    {
        let mut pending = alloc::vec![root];
        while let Some(node) = pending.pop() {
            match node {
                TypeNode::Value(at) => {
                    if let Some(&ValueType::Capability {
                        ref authority,
                        region: Region::Held,
                        ..
                    }) = arena.value_type(at)
                    {
                        self.signatures(authority.instances());
                    }
                },
                TypeNode::Computation(at) => {
                    if let Some(&CompType::Returner { ref effects, .. }) = arena.comp_type(at) {
                        self.signatures(effects.instances());
                    }
                },
            }
            successors(arena, node, &mut pending)?;
        }
        Ok(())
    }

    /// Add every operation of each signature an interface's default label
    /// carries; an instance a scope introduces is skipped.
    ///
    /// # Specification
    /// trivial.
    fn signatures<'row>(
        &mut self,
        entries: impl Iterator<Item = (&'row EffectLabel, &'row EffectSig)>,
    )
    {
        for (label, signature) in entries {
            if matches!(*label, EffectLabel::Interface(_)) {
                let held = self.0.entry(signature.name().clone()).or_default();
                for operation in signature.operations() {
                    held.entry(operation.name.clone())
                        .or_insert_with(|| operation.clone());
                }
            }
        }
    }

    /// Add the operation `operation` of `signature`, performed by name.
    ///
    /// # Specification
    /// - ensures: the operation is held when `signature` declares it; nothing
    ///   changes otherwise.
    /// - panics: none.
    /// - executable: none — as [`Self::reach`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reach`]: a half performing an operation by
    ///   name holds it.
    /// - witness: `judgement::session::tests::two_halves_share_a_capability_only_to_read_through_it_2789`
    pub(crate) fn perform(
        &mut self,
        signature: &EffectSig,
        operation: &OperationName,
    )
    {
        if let Maybe::Present(declared) = signature.operation(operation) {
            self.0
                .entry(signature.name().clone())
                .or_default()
                .entry(operation.clone())
                .or_insert_with(|| declared.clone());
        }
    }

    /// Add every operation `other` holds.
    ///
    /// # Specification
    /// - ensures: every operation either footprint held is held.
    /// - panics: none.
    /// - executable: none — as [`Self::reach`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reach`]: an inner fork's halves both count
    ///   toward the half around it.
    /// - witness: `judgement::session::tests::two_halves_share_a_capability_only_to_read_through_it_2789`
    pub(crate) fn absorb(
        &mut self,
        other: Self,
    )
    {
        for (interface, operations) in other.0 {
            let held = self.0.entry(interface).or_default();
            for (name, operation) in operations {
                held.entry(name).or_insert(operation);
            }
        }
    }

    /// The interfaces both footprints use where either may change the host,
    /// each with the operations both sides hold there; `None` exactly when
    /// the two are separate.
    ///
    /// # Specification
    /// - ensures: an interface is kept only when both footprints hold it and
    ///   one of its operations either holds does not only read the host; an
    ///   overlap holds at least one interface.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `read` on both sides is separate; `read` beside
    ///   `write` is not; two interfaces apart are separate.
    /// - witness: `judgement::session::tests::two_halves_share_a_capability_only_to_read_through_it_2789`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|shared| !shared.0.is_empty() && shared.0.keys().all(|interface| self.0.contains_key(interface) && other.0.contains_key(interface))))]
    pub(crate) fn overlap(
        &self,
        other: &Self,
    ) -> Option<Self>
    {
        let mut shared = Self::default();
        for (interface, mine) in &self.0 {
            let Some(theirs) = other.0.get(interface)
            else {
                continue;
            };
            let changes = mine
                .keys()
                .chain(theirs.keys())
                .any(|operation| access(interface, operation) == HostAccess::Changes);
            if changes {
                let mut both = mine.clone();
                for (name, operation) in theirs {
                    both.entry(name.clone())
                        .or_insert_with(|| operation.clone());
                }
                shared.0.insert(interface.clone(), both);
            }
        }
        if shared.0.is_empty() {
            None
        }
        else {
            Some(shared)
        }
    }

    /// The footprint as the type of a durable capability the host holds,
    /// whose authority is exactly the footprint: how a refusal names it.
    ///
    /// # Specification
    /// - ensures: a held, durable capability type granting each held operation.
    /// - fails: [`CheckRefusal::MachineInvariant`] never, for a footprint
    ///   holding each operation once per interface.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::MachineInvariant`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the refused children's footprints, each named as the
    ///   capability granting what the half holds.
    /// - witness: `judgement::session::tests::two_halves_share_a_capability_only_to_read_through_it_2789`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&id| matches!(arena.value_type(id), Some(&ValueType::Capability { grade: CapabilityGrade::Durable, region: Region::Held, .. }))))]
    pub(crate) fn capability(
        &self,
        arena: &mut CoreArena,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let signatures = self
            .0
            .iter()
            .map(|(interface, operations)| {
                EffectSig::new(interface.clone(), operations.values().cloned())
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_conflict| CheckRefusal::MachineInvariant)?;
        let authority = EffectRow::authority(&signatures)
            .map_err(|_conflict| CheckRefusal::MachineInvariant)?;
        Ok(arena.value_type_capability(authority, CapabilityGrade::Durable, Region::Held))
    }
}

/// Admit the declaration `constant`, owed at `declared`, as a capability the
/// host holds, when it is one: the introduction at the checker's entry.
///
/// # Specification
/// - ensures: success for a type that is no held capability at its weak head,
///   and for every type when the context names no grant.
/// - fails: [`CheckRefusal::CapabilityUngranted`] for a held capability whose
///   authority does not fall within the context's grant; the weak head's
///   refusal when it does not unfold.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a held capability within the grant, one beyond it, and
///   both with no grant, each asserted as owed or refused.
/// - witness: `capability::tests::a_held_capability_enters_only_within_the_grant`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::CapabilityUngranted { constant: named, declared: ty }) => named == constant && ty == declared.id(),
    | Ok(()) | Err(_) => true,
})]
pub fn held(
    context: &mut CheckingContext<'_>,
    constant: ConstantIndex,
    declared: FormedValueType,
) -> Result<(), CheckRefusal>
{
    if *context.grants() == Grants::Unbounded {
        return Ok(());
    }
    let head = context.whnf_value_type(declared.id())?;
    let Grants::Within(ref grants) = *context.grants()
    else {
        return Ok(());
    };
    if let ValueTypeView::Capability {
        authority,
        region: Region::Held,
        ..
    } = value_type_view(context.arena(), head)?
        && authority.grants_within(grants, context.arena()) == RowInclusion::Excluded
    {
        return Err(CheckRefusal::CapabilityUngranted {
            constant,
            declared: declared.id(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests;
