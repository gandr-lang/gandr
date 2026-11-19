//! The support every node carries, built from its children's when it is
//! minted.
//!
//! A node's support is what it names itself — a variable its index, a session
//! action its endpoint, a memory form its resident slot — together with what
//! each child selects past the binders between them, lowered by them. The
//! children and the binders each stands under are the former's scoping, which
//! [`crate::children`] states once.
//!
//! A child is read through the support it carries, so minting a node is one
//! union over its children rather than a walk below them; a dangling child
//! adds nothing, as a dangling child resolves to nothing everywhere else. The
//! union is kept as one slot in the node's row, its wide words in the arena's
//! word arena.

use quenchant_shape::shape::Maybe;

use super::ArenaIndex;
use super::CoreArena;
use super::id_offset;
use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::children;
use crate::children::Visit;
use crate::support::Crossing;
use crate::support::Slot;
use crate::support::ThinningRef;
use crate::support::Union;
use crate::syntax::CompType;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

/// The union a node about to be minted collects: each child's carried support,
/// read past the binders the former opens over it.
struct Carry<'arena>
{
    /// The arena the children are minted in.
    arena: &'arena CoreArena,
    /// The support collected so far.
    union: Union,
}

impl Visit for Carry<'_>
{
    /// Add a value child's support, read past `crossing`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn value(
        &mut self,
        child: ValueId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.arena.values.get(id_offset(ArenaIndex(child.0))) {
            self.union
                .stored_child(row.support, &self.arena.words, crossing);
        }
    }

    /// Add a computation child's support, read past `crossing`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn computation(
        &mut self,
        child: ComputationId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.arena.computations.get(id_offset(ArenaIndex(child.0))) {
            self.union
                .stored_child(row.support, &self.arena.words, crossing);
        }
    }

    /// Add a value-type child's support, read past `crossing`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn value_type(
        &mut self,
        child: ValueTypeId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.arena.value_types.get(id_offset(ArenaIndex(child.0))) {
            self.union
                .stored_child(row.support, &self.arena.words, crossing);
        }
    }

    /// Add a computation-type child's support, read past `crossing`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn comp_type(
        &mut self,
        child: CompTypeId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.arena.comp_types.get(id_offset(ArenaIndex(child.0))) {
            self.union
                .stored_child(row.support, &self.arena.words, crossing);
        }
    }
}

impl CoreArena
{
    /// A collection over no child yet, reading children in this arena.
    ///
    /// # Specification
    /// trivial.
    fn carry(&self) -> Carry<'_>
    {
        Carry {
            arena: self,
            union: Union::new(),
        }
    }

    /// The support a value about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `value` is minted in this arena.
    /// - ensures: the variable's own index for a variable; otherwise the union
    ///   of the children's carried supports, each past the binders the former
    ///   opens over it ([`children::of_value`]).
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which
    ///   [`crate::children`] states once; a predicate would restate it beside
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every binder former with a body that reads and one
    ///   that ignores its bound variable separates a crossing from none, and a
    ///   variable in each zone separates the zones. Beyond this crate,
    ///   `gandr-core-sequent`'s property suite holds every node of every
    ///   generated term to the free indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn value_carried(
        &mut self,
        value: &Value,
    ) -> Slot
    {
        let mut carry = self.carry();
        if let Value::Variable { zone, index } = *value {
            carry.union.name(zone, index);
        }
        children::of_value(value, &mut carry);
        let union = carry.union;
        self.words.store_union(union)
    }

    /// The support a computation about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `computation` is minted in this arena.
    /// - ensures: the union of what the computation names itself — a session
    ///   action's endpoint, a memory form's resident, each linear — and the
    ///   children's carried supports, each past the binders the former opens
    ///   over it ([`children::of_computation`]).
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which
    ///   [`crate::children`] states once; a predicate would restate it beside
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every binder former with a body that reads and one
    ///   that ignores its bound variable separates a crossing from none and the
    ///   zones from each other. Beyond this crate, `gandr-core-sequent`'s
    ///   property suite holds every node of every generated term to the free
    ///   indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn computation_carried(
        &mut self,
        computation: &Computation,
    ) -> Slot
    {
        let mut carry = self.carry();
        if let Computation::Session(ref action) = *computation
            && let Maybe::Present(endpoint) = action.endpoint()
        {
            carry.union.name(Zone::Linear, endpoint);
        }
        if let Computation::Memory(ref form) = *computation
            && let Maybe::Present(resident) = form.resident()
        {
            carry.union.name(Zone::Linear, resident);
        }
        children::of_computation(computation, &mut carry);
        let union = carry.union;
        self.words.store_union(union)
    }

    /// The support a value type about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `value_type` is minted in this arena.
    /// - ensures: the union of the children's carried supports, each past the
    ///   binders the former opens over it ([`children::of_value_type`]).
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which
    ///   [`crate::children`] states once; a predicate would restate it beside
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a Σ whose second factor reads its binder and one that
    ///   reads past it separate the crossing from none. Beyond this crate,
    ///   `gandr-core-sequent`'s property suite holds every node of every
    ///   generated term to the free indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn value_type_carried(
        &mut self,
        value_type: &ValueType,
    ) -> Slot
    {
        let mut carry = self.carry();
        children::of_value_type(value_type, &mut carry);
        let union = carry.union;
        self.words.store_union(union)
    }

    /// The support a computation type about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `comp_type` is minted in this arena.
    /// - ensures: the union of the children's carried supports, each past the
    ///   binders the former opens over it ([`children::of_comp_type`]).
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which
    ///   [`crate::children`] states once; a predicate would restate it beside
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a Π whose codomain reads its binder beside an arrow
    ///   over the same codomain separates the crossing from none. Beyond this
    ///   crate, `gandr-core-sequent`'s property suite holds every node of every
    ///   generated term to the free indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn comp_type_carried(
        &mut self,
        comp_type: &CompType,
    ) -> Slot
    {
        let mut carry = self.carry();
        children::of_comp_type(comp_type, &mut carry);
        let union = carry.union;
        self.words.store_union(union)
    }

    /// The support `slot` keeps, read in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) fn support_of(
        &self,
        slot: Slot,
    ) -> ThinningRef<'_>
    {
        match self.words.read(slot) {
            Maybe::Present(support) => support,
            // reason: every handle a row holds names words this arena wrote,
            // and a truncation drops the row with them.
            Maybe::Absent(_) => ThinningRef::empty(),
        }
    }
}
