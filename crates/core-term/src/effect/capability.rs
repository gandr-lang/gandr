//! The capability former's leaves: the authority a capability carries, the
//! region it lives for, and its grade.
//!
//! # A capability is a hypothesis carrying authority
//!
//! `Cap E` classifies a context hypothesis that carries the authority `E`, and
//! no term forms one: a capability enters a context only as a hypothesis the
//! host holds at the checker's entry or as the binder a capability scope
//! introduces over its body. That is the object-capability rule "only
//! connectivity begets connectivity" (Mark S. Miller, _Robust Composition_,
//! doctoral thesis, Johns Hopkins University, 2006, § 9.2.5) stated as a typing
//! invariant, and the checker refuses a term in capability position that is not
//! such a hypothesis.
//!
//! # The authority is a set of grant atoms
//!
//! An authority is an [`EffectRow`] whose interfaces are restrictions: each
//! names an interface and the operations of it the capability grants, with
//! their payload and reply types, so a grant atom is an (interface, operation)
//! pair. `Cap {read, write}` over the host's `Fs` interface carries `Fs`
//! restricted to `read` and `write`. Attenuation is inclusion on grant atoms,
//! [`EffectRow::grants_within`]: `Cap E` stands where `Cap E′` is expected when
//! every atom of `E′` is an atom of `E`, so authority only narrows. The
//! alternative was interface-granular authority read through
//! [`EffectRow::is_subset`], which cannot attenuate `Fs` to its reads; it
//! returns if interfaces are ever split so that one interface is one grant.
//!
//! # A region bounds a scoped capability
//!
//! A capability the host holds lives for the whole run, [`Region::Held`]. One a
//! scope introduces lives until the scope's body ends, [`Region::Scoped`] at
//! the scope's nesting depth, counted from one at the outermost scope; depth
//! zero is the definition's own body, which every scope in it nests inside. A
//! region a scope opens is named by its depth rather than by a fresh name, so
//! two scopes at one depth are siblings whose capabilities never meet. A
//! definition may abstract over a region its caller holds, `@[r : Region]`:
//! [`Region::Bound`] names that binder by its ordinal, and each call
//! instantiates it at a region of the caller's. A bound region is live
//! throughout the call, so it outlives the body and every scope in it, and
//! the held region outlives it; two bound regions are ordered by nothing the
//! definition states. A longer region stands where a shorter one is
//! expected, [`Region::outlives`], never the reverse, which is what keeps a
//! scoped capability from passing where a held one is promised.
//!
//! # The grade
//!
//! A [`CapabilityGrade::Durable`] capability sits in the intuitionistic zone at
//! grade ω: it may be exercised any number of times and dropped. A
//! [`CapabilityGrade::Consumable`] capability belongs in the linear zone, spent
//! by its one exercise and neither dropped nor duplicated; no former binds into
//! that zone, so the checker refuses the consumable grade by name rather than
//! check it as durable.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::EffectConflict;
use super::EffectOp;
use super::EffectRow;
use super::EffectSig;
use super::OperationName;
use super::Signature;
use super::UnknownOperation;
use crate::row::Label;
use crate::row::RowInclusion;

/// How many capability scopes enclose a region, counting the one that
/// introduced it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RegionDepth(u32);

impl From<u32> for RegionDepth
{
    /// Wraps a nesting count as a region depth.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: u32) -> Self
    {
        Self(depth)
    }
}

impl From<RegionDepth> for u32
{
    /// Unwraps a region depth to its nesting count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: RegionDepth) -> Self
    {
        depth.0
    }
}

/// The ordinal of a region binder in its definition's telescope, counted
/// from zero over the binders of sort `Region` in written order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RegionBinder(u32);

impl From<u32> for RegionBinder
{
    /// Wraps an ordinal as a region binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(ordinal: u32) -> Self
    {
        Self(ordinal)
    }
}

impl From<RegionBinder> for u32
{
    /// Unwraps a region binder to its ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(binder: RegionBinder) -> Self
    {
        binder.0
    }
}

/// The extent a capability is valid for, or a value is kept in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Region
{
    /// Held by the host from the checker's entry, valid for the whole run.
    Held,
    /// Introduced by the capability scope or hold at this depth, valid until
    /// that scope's body ends; depth zero is the definition's own body.
    Scoped(RegionDepth),
    /// The caller's region the definition's region binder at this ordinal
    /// abstracts, valid throughout the call.
    Bound(RegionBinder),
}

/// Whether one region lasts at least as long as another.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RegionOrder
{
    /// The first region is live wherever the second is.
    Outlives,
    /// The first region ends while the second is still live.
    EndsFirst,
}

impl Region
{
    /// Whether `self` is live wherever `other` is.
    ///
    /// # Specification
    /// - ensures: the held region outlives every region; a bound region
    ///   outlives itself and every scoped region, and neither the held region
    ///   nor another bound one; a scoped region outlives exactly the scoped
    ///   regions at its own depth or deeper.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the held region against itself and a scoped one in
    ///   both orders, two scoped regions one depth apart in both orders and at
    ///   equal depth, and a bound region against itself, another bound one, the
    ///   held region and the body in both orders, each asserted exactly.
    /// - witness: `effect::capability::tests::a_region_outlives_only_regions_nested_in_it`
    #[spec(ensures: |ret| (ret == RegionOrder::Outlives) == match (self, other) {
        (Self::Held, _) | (Self::Bound(_), Self::Scoped(_)) => true,
        (Self::Bound(this), Self::Bound(that)) => this == that,
        (Self::Bound(_) | Self::Scoped(_), Self::Held) | (Self::Scoped(_), Self::Bound(_)) => false,
        (Self::Scoped(outer), Self::Scoped(inner)) => outer <= inner,
    })]
    #[inline]
    #[must_use]
    pub fn outlives(
        self,
        other: Self,
    ) -> RegionOrder
    {
        let outlives = match (self, other) {
            (Self::Held, _) | (Self::Bound(_), Self::Scoped(_)) => true,
            (Self::Bound(this), Self::Bound(that)) => this == that,
            (Self::Bound(_) | Self::Scoped(_), Self::Held) | (Self::Scoped(_), Self::Bound(_)) => {
                false
            },
            (Self::Scoped(outer), Self::Scoped(inner)) => outer <= inner,
        };
        if outlives {
            RegionOrder::Outlives
        }
        else {
            RegionOrder::EndsFirst
        }
    }
}

/// How often a capability may be exercised, and the zone it resides in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CapabilityGrade
{
    /// Grade ω in the intuitionistic zone: exercised any number of times, and
    /// droppable.
    Durable,
    /// Resident in the linear zone: spent by its one exercise, and neither
    /// dropped nor duplicated.
    Consumable,
}

quenchant_shape::reason_enum! {
    /// Why an authority grants no operation by a given name.
    pub mod grant {
        /// The reason an authority lookup answered no operation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The authority names no restriction of the interface.
            Interface,
            /// The authority restricts the interface, and the operation is not
            /// among the operations it grants.
            Operation,
        }
    }
}

/// Why a restriction of an interface could not be formed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RestrictionError
{
    /// The operation is not one of the interface's.
    Unknown(OperationName),
    /// The operation was named twice.
    Repeated(OperationName),
}

impl EffectSig
{
    /// The interface restricted to the named operations, each with the
    /// payload and reply types the interface gives it.
    ///
    /// # Specification
    /// - ensures: the restriction keeps the interface's name and exactly the
    ///   named operations, with their types.
    /// - fails: a name outside the interface, or one named twice.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`RestrictionError::Unknown`]: the first name the interface lacks.
    /// - [`RestrictionError::Repeated`]: the first name given twice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two of the host filesystem's operations in either
    ///   order, an operation outside it and a repeated one, each asserted as
    ///   the exact restriction or refusal.
    /// - witness: `effect::capability::tests::a_restriction_keeps_exactly_the_named_operations`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|restricted| restricted.name() == self.name() && restricted.operations().all(|operation| self.operation(&operation.name) == Maybe::Present(operation))) || ret.is_err())]
    #[inline]
    pub fn restrict<'name, Names>(
        &self,
        names: Names,
    ) -> Result<Self, RestrictionError>
    where
        Names: IntoIterator<Item = &'name OperationName>,
    {
        let mut operations = BTreeMap::new();
        for name in names {
            let Maybe::Present(operation) = self.operation(name)
            else {
                return Err(RestrictionError::Unknown(name.clone()));
            };
            if operations.insert(name.clone(), operation.clone()).is_some() {
                return Err(RestrictionError::Repeated(name.clone()));
            }
        }
        Ok(Self(Arc::new(Signature {
            name: self.name().clone(),
            operations,
        })))
    }
}

impl EffectRow
{
    /// Whether every grant atom of `self` is a grant atom of `authority`: each
    /// restricted interface is restricted in `authority` too, and each of its
    /// operations is granted there with structurally equal payload and reply
    /// types.
    ///
    /// # Specification
    /// - ensures: inclusion on (interface, operation) atoms; the empty
    ///   authority is included in every authority.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `{read}` within `{read, write}` and not the reverse,
    ///   an atom of another interface, an atom whose reply type differs, and
    ///   the empty authority, each asserted exactly.
    /// - witness: `effect::capability::tests::attenuation_is_inclusion_on_grant_atoms`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body looks every operation this row restricts up in the authority and compares its two types once; the check makes the same lookups and comparisons once more"
        )
    )]
    #[spec(ensures: |ret| (ret == RowInclusion::Included) == self.instances().all(|(label, restricted)| restricted.operations().all(|operation| matches!(authority.granted(label, &operation.name), Maybe::Present(held) if crate::syntax::equal_type_syntax(arena, held.payload, operation.payload) == crate::CertificateEquality::Equal && crate::syntax::equal_type_syntax(arena, held.reply, operation.reply) == crate::CertificateEquality::Equal))))]
    #[inline]
    #[must_use]
    pub fn grants_within(
        &self,
        authority: &Self,
        arena: &crate::CoreArena,
    ) -> RowInclusion
    {
        for (label, restricted) in self.instances() {
            for operation in restricted.operations() {
                let Maybe::Present(held) = authority.granted(label, &operation.name)
                else {
                    return RowInclusion::Excluded;
                };
                if crate::syntax::equal_type_syntax(arena, held.payload, operation.payload)
                    != crate::CertificateEquality::Equal
                    || crate::syntax::equal_type_syntax(arena, held.reply, operation.reply)
                        != crate::CertificateEquality::Equal
                {
                    return RowInclusion::Excluded;
                }
            }
        }
        RowInclusion::Included
    }

    /// The operation `operation` of the instance labelled `interface`, when
    /// this authority grants it.
    ///
    /// # Specification
    /// - provides: [`grant::Absent::Interface`] when the authority restricts no
    ///   interface of that name, and [`grant::Absent::Operation`] when it
    ///   restricts the interface without granting the operation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a granted operation, an operation of the restricted
    ///   interface the authority withholds, and an interface it does not
    ///   restrict, each asserted exactly.
    /// - witness: `effect::capability::tests::attenuation_is_inclusion_on_grant_atoms`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(held) => &held.name == operation,
        Maybe::Absent(grant::Absent::Interface) => self.contains(interface) == super::EffectPresence::Absent,
        Maybe::Absent(grant::Absent::Operation) => self.contains(interface) == super::EffectPresence::Present,
    })]
    #[inline]
    pub fn granted(
        &self,
        interface: &Label,
        operation: &OperationName,
    ) -> Maybe<&EffectOp, grant::Absent>
    {
        let Some(restricted) = self.entries().get(interface)
        else {
            return Maybe::Absent(grant::Absent::Interface);
        };
        match restricted.operation(operation) {
            Maybe::Present(held) => Maybe::Present(held),
            Maybe::Absent(UnknownOperation) => Maybe::Absent(grant::Absent::Operation),
        }
    }
}

impl EffectRow
{
    /// The authority holding exactly the given restrictions.
    ///
    /// # Specification
    /// - ensures: one restriction per interface name, in canonical order.
    /// - fails: two restrictions of one interface; they are merged by the
    ///   caller, never here.
    /// - panics: none.
    ///
    /// # Errors
    /// [`EffectConflict::Signature`] for the first interface restricted twice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — restrictions of two interfaces build one authority
    ///   granting both, and two restrictions of one interface are refused.
    /// - witness: `effect::capability::tests::attenuation_is_inclusion_on_grant_atoms`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|authority| authority.signatures().len() <= restrictions.len()))]
    #[inline]
    pub fn authority(restrictions: &[EffectSig]) -> Result<Self, EffectConflict>
    {
        Self::from_signatures(restrictions.iter().cloned())
    }
}

impl crate::CoreArena
{
    /// Mint the type of a capability carrying `authority` for `region` at
    /// `grade`.
    ///
    /// # Specification
    /// - requires: every type the authority's operations name resolves in this
    ///   arena.
    /// - ensures: keeps the authority, grade and region as given.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substituting into an authority whose operation names
    ///   a free variable rewrites that operation's type and keeps the grade and
    ///   region; importing it into another arena reads back equal.
    /// - witness: `control::tests::a_capability_scope_binds_its_subject_once`
    #[spec(requires: authority.types().all(|ty| self.value_type(ty).is_some()), ensures: |ret| matches!(self.value_type(ret), Some(crate::ValueType::Capability { grade: kept, region: lives, .. }) if *kept == grade && *lives == region))]
    #[inline]
    pub fn value_type_capability(
        &mut self,
        authority: EffectRow,
        grade: CapabilityGrade,
        region: Region,
    ) -> crate::ValueTypeId
    {
        self.alloc_value_type(crate::ValueType::Capability {
            authority,
            grade,
            region,
        })
    }

    /// Mint the type of a value of `value` kept in `region`.
    ///
    /// # Specification
    /// - requires: `value` resolves in this arena.
    /// - ensures: keeps the value type and the region as given.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a kept type over a value that mentions a binder and
    ///   one over a closed value, each substituted into: the first rewrites its
    ///   value and keeps its region, the second stays the same node.
    /// - witness: `effect::capability::tests::a_kept_type_keeps_its_region_across_substitution`
    #[spec(requires: self.value_type(value).is_some(), ensures: |ret| matches!(self.value_type(ret), Some(&crate::ValueType::Kept { value: kept, region: lives }) if kept == value && lives == region))]
    #[inline]
    pub fn value_type_kept(
        &mut self,
        value: crate::ValueTypeId,
        region: Region,
    ) -> crate::ValueTypeId
    {
        self.alloc_value_type(crate::ValueType::Kept { value, region })
    }
}

#[cfg(test)]
mod tests;
