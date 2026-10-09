//! Both closure spaces, and the environment they close over.
//!
//! # Two spaces, one entry operation
//!
//! The core language has two term families, so a suspended body is one of two
//! things:
//!
//! - [`ValueClosure`] suspends a **value** body: the shape a code standing
//!   under a binder takes.
//! - [`CompClosure`] suspends a **computation** body: the shape a lambda, a
//!   thunk, a bind continuation and a case branch all take.
//!
//! No former in the core vocabulary produces a value closure. Both spaces close
//! over the same [`Environment`], so entering a closure is one operation over
//! either, for the same reason the two faces of [the domain] are named on one
//! type.
//!
//! # The environment mirrors the context's two zones
//!
//! A closure captures what its free variables stand for, and a free variable
//! names a zone as well as an index, so the environment carries the same two
//! flat stacks the typing context does. Mirroring is forced rather than
//! preferred: an environment with one stack could not answer a linear
//! occurrence at all, and reconstructing which stack an index meant from a
//! depth comparison is exactly the ambiguity the zone on the occurrence exists
//! to remove.
//!
//! Entries are domain value ids, so an environment is two flat vectors of
//! `Copy` ids and capturing one is a vector clone rather than a graph walk.
//!
//! [the domain]: crate::domain

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use crate::arena::DomainValueId;

/// The offset of one entry within a zone of the environment.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct EntryOffset(usize);

/// The number of entries one zone of an environment holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EnvironmentDepth(usize);

impl From<usize> for EnvironmentDepth
{
    /// Read a `usize` as a zone depth.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: usize) -> Self
    {
        Self(depth)
    }
}

impl From<EnvironmentDepth> for usize
{
    /// Read the depth back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: EnvironmentDepth) -> Self
    {
        depth.0
    }
}

/// What a closure's free variables stand for: two flat stacks of domain value
/// ids, one per zone, innermost binding last.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Environment
{
    /// The intuitionistic zone's bindings.
    intuitionistic: Vec<DomainValueId>,
    /// The linear zone's bindings.
    linear: Vec<DomainValueId>,
}

impl Environment
{
    /// The empty environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The number of bindings a zone holds.
    ///
    /// # Specification
    /// - requires: nothing; both zones answer, and an unbound zone answers
    ///   zero.
    /// - ensures: the number of bindings that zone holds, which is one more
    ///   than the greatest index bound in it.
    /// - provides: the bound `entry_offset` resolves an index against, and the
    ///   level a readback counts a fresh variable from.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn depth(
        &self,
        zone: Zone,
    ) -> EnvironmentDepth
    {
        EnvironmentDepth(match zone {
            | Zone::Intuitionistic => self.intuitionistic.len(),
            | Zone::Linear => self.linear.len(),
        })
    }

    /// Extend a zone with one binding.
    ///
    /// # Specification
    /// - requires: `bound` resolves in the domain arena this environment is
    ///   read against; the environment stores the id and never dereferences it.
    /// - ensures: the zone's depth is one greater, index zero of that zone
    ///   names `bound`, every previously bound index of that zone is reachable
    ///   at one more than it was, and the other zone is untouched.
    /// - provides: the binder-entering half of every rule that goes under a
    ///   binder, and the counterpart of the typing context's own binder
    ///   opening. The clause states the extended zone's depth, the new
    ///   innermost binding, the shift of the previously innermost one, and the
    ///   other zone's depth; the shift of every deeper index and the other
    ///   zone's contents would need owned entry snapshots, which the pinned
    ///   expansion evaluates even in a non-enforcing build.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is which zone is pushed,
    ///   separated by extending each zone with the other's depth asserted
    ///   unmoved, and by the shift of an already-bound index in the extended
    ///   zone.
    /// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
    /// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
    #[inline]
    #[spec(
        captures: [
            entry_intuitionistic = self.intuitionistic.len(),
            entry_linear = self.linear.len(),
            entry_innermost = match zone {
                | Zone::Intuitionistic => self.intuitionistic.last().copied(),
                | Zone::Linear => self.linear.last().copied(),
            },
        ],
        ensures: match zone {
            | Zone::Intuitionistic => {
                self.intuitionistic.len() == entry_intuitionistic.saturating_add(1_usize)
                    && self.intuitionistic.last() == Some(&bound)
                    && self.intuitionistic.iter().rev().nth(1_usize).copied() == entry_innermost
                    && self.linear.len() == entry_linear
            },
            | Zone::Linear => {
                self.linear.len() == entry_linear.saturating_add(1_usize)
                    && self.linear.last() == Some(&bound)
                    && self.linear.iter().rev().nth(1_usize).copied() == entry_innermost
                    && self.intuitionistic.len() == entry_intuitionistic
            },
        }
    )]
    pub fn extend(
        &mut self,
        zone: Zone,
        bound: DomainValueId,
    )
    {
        match zone {
            | Zone::Intuitionistic => self.intuitionistic.push(bound),
            | Zone::Linear => self.linear.push(bound),
        }
    }

    /// What a bound occurrence stands for.
    ///
    /// The index counts binders outward from the use site within its own zone,
    /// so index zero names the innermost binding of that zone.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range index is admissible input.
    /// - ensures: the id the named binding holds.
    /// - provides: the variable rule of an evaluator, and the one place the two
    ///   zones' index spaces are read.
    /// - fails: returns `None` when the index counts past the zone's bindings,
    ///   which an evaluator turns into a fresh neutral rather than a panic.
    /// - panics: none — the index arithmetic is checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the zone selection and the
    ///   index arithmetic, separated by the innermost and an outer binding of a
    ///   two-deep zone, the first index past the depth, and one index resolved
    ///   in each zone with the other zone holding a different id at the same
    ///   index.
    /// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
    /// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| [
        ret.is_some()
            == usize::try_from(u32::from(index)).is_ok_and(|counted| counted < self.depth(zone).0),
        ret == entry_offset(self.depth(zone), index).and_then(|offset| match zone {
            | Zone::Intuitionistic => self.intuitionistic.get(offset.0).copied(),
            | Zone::Linear => self.linear.get(offset.0).copied(),
        }),
    ])]
    pub fn lookup(
        &self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Option<DomainValueId>
    {
        let offset = entry_offset(self.depth(zone), index)?;
        match zone {
            | Zone::Intuitionistic => self.intuitionistic.get(offset.0).copied(),
            | Zone::Linear => self.linear.get(offset.0).copied(),
        }
    }

    /// Every binding one zone holds, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn bindings(
        &self,
        zone: Zone,
    ) -> &[DomainValueId]
    {
        match zone {
            | Zone::Intuitionistic => &self.intuitionistic,
            | Zone::Linear => &self.linear,
        }
    }
}

/// Resolve a de Bruijn index against a zone of `depth` bindings.
///
/// # Specification
/// - requires: nothing — every index and every depth is admissible input.
/// - ensures: the stack offset of the named binding, `depth - index - 1`,
///   exactly when the index counts within `depth`.
/// - provides: the one arithmetic both zones' lookups share.
/// - fails: returns `None` when the index counts past the zone's bindings.
/// - panics: none — both subtractions are checked.
///
/// # Adequacy
/// - hypothesis: L3 — the two decision surfaces are the two checked
///   subtractions, separated by the innermost binding of a two-deep zone, an
///   outer binding, the first index past the depth, and an index read against
///   an empty zone, each observed through the lookup that reports on it.
/// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
/// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
#[inline]
#[spec(ensures: |ret| match (usize::try_from(u32::from(index)), ret) {
    | (Ok(counted), Some(offset)) => offset.0.checked_add(counted) == depth.0.checked_sub(1_usize),
    | (Ok(counted), None) => counted >= depth.0,
    | (Err(_), offset) => offset.is_none(),
})]
fn entry_offset(
    depth: EnvironmentDepth,
    index: DeBruijnIndex,
) -> Option<EntryOffset>
{
    let index = usize::try_from(u32::from(index)).ok()?;
    let remaining = depth.0.checked_sub(index)?;
    let offset = remaining.checked_sub(1_usize)?;
    Some(EntryOffset(offset))
}

/// A suspended **value** body with the environment its free variables stand in.
///
/// No former in the core vocabulary produces one; it is named beside
/// [`CompClosure`] so that entering a closure is one operation over both term
/// families.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueClosure
{
    /// The core value body, unevaluated.
    body: ValueId,
    /// What the body's free variables stand for.
    environment: Environment,
}

impl ValueClosure
{
    /// Close `body` over `environment`.
    ///
    /// # Specification
    /// - requires: `environment` binds every occurrence free in `body` in the
    ///   zone that occurrence names; a body and an environment carry no shared
    ///   provenance, so the pairing is the caller's claim.
    /// - ensures: the closure carries exactly the body and environment offered,
    ///   unevaluated.
    /// - provides: the delayed substitution a value binder is represented by,
    ///   which is why the constructor is crate-private: the arena is the one
    ///   producer that pairs the two.
    /// - fails: never — an environment too shallow for the body surfaces where
    ///   the body is entered, not here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) fn new(
        body: ValueId,
        environment: Environment,
    ) -> Self
    {
        Self { body, environment }
    }

    /// The suspended body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn body(&self) -> ValueId
    {
        self.body
    }

    /// The captured environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn environment(&self) -> &Environment
    {
        &self.environment
    }
}

/// A suspended **computation** body with the environment its free variables
/// stand in: what a lambda, a thunk, a bind continuation and a case branch all
/// become.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompClosure
{
    /// The core computation body, unevaluated.
    body: ComputationId,
    /// What the body's free variables stand for.
    environment: Environment,
}

impl CompClosure
{
    /// Close `body` over `environment`.
    ///
    /// # Specification
    /// - requires: `environment` binds every occurrence free in `body` in the
    ///   zone that occurrence names; the pairing is the caller's claim.
    /// - ensures: the closure carries exactly the body and environment offered,
    ///   unevaluated.
    /// - provides: the one shape a lambda, a thunk, a bind continuation and a
    ///   case branch all become, which is why the constructor is crate-private.
    /// - fails: never — an environment too shallow for the body surfaces where
    ///   the body is entered, not here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) fn new(
        body: ComputationId,
        environment: Environment,
    ) -> Self
    {
        Self { body, environment }
    }

    /// The suspended body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn body(&self) -> ComputationId
    {
        self.body
    }

    /// The captured environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn environment(&self) -> &Environment
    {
        &self.environment
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;

    use super::Environment;
    use super::EnvironmentDepth;
    use crate::arena::DomainArena;
    use crate::domain::TermFace;

    #[test]
    fn the_zones_resolve_one_index_to_two_bindings()
    {
        let mut arena = DomainArena::new();
        let outer = arena.value_unit(TermFace::Reduced);
        let structural = arena.value_unit(TermFace::Reduced);
        let linear = arena.value_unit(TermFace::Reduced);
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, outer);
        environment.extend(Zone::Intuitionistic, structural);
        environment.extend(Zone::Linear, linear);

        assert_eq!(
            Some(structural),
            environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            "index zero names the innermost binding of its own zone"
        );
        assert_eq!(
            Some(outer),
            environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
            "and one out names the one before it"
        );
        assert_eq!(
            Some(linear),
            environment.lookup(Zone::Linear, DeBruijnIndex::from(0_u32)),
            "the same index in the other zone names a different binding"
        );
        assert_eq!(
            EnvironmentDepth::from(2_usize),
            environment.depth(Zone::Intuitionistic),
            "the zones count separately"
        );
        assert_eq!(
            EnvironmentDepth::from(1_usize),
            environment.depth(Zone::Linear)
        );
    }

    #[test]
    fn an_index_past_the_depth_resolves_to_nothing()
    {
        let mut arena = DomainArena::new();
        let bound = arena.value_unit(TermFace::Reduced);
        let mut environment = Environment::new();
        assert!(
            environment
                .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
                .is_none(),
            "an empty zone binds no index"
        );
        environment.extend(Zone::Intuitionistic, bound);
        assert!(
            environment
                .lookup(Zone::Intuitionistic, DeBruijnIndex::from(1_u32))
                .is_none(),
            "the first index past the depth resolves to nothing rather than wrapping"
        );
        assert!(
            environment
                .lookup(Zone::Linear, DeBruijnIndex::from(0_u32))
                .is_none(),
            "and extending one zone did not populate the other"
        );
    }
}
