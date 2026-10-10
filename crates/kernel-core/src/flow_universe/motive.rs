//! Term-structural covariance checking for directed elimination motives.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;

use super::Allowance;
use super::FlowError;
use super::Variance;
use crate::replay::ReplayBudget;

/// A motive's fixed source endpoint or its moving target endpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Endpoint
{
    /// The source remains fixed while transport moves the target.
    Fixed,
    /// The target endpoint may occur only covariantly.
    Moving,
}

/// A motive node's index in constructor-ordered syntax.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MotiveId(usize);

/// First-order motive syntax used by the directed formation side condition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Motive
{
    /// Elements of the endpoint code.
    El(Endpoint),
    /// Directed certificates: contravariant source, covariant target.
    Flow(Endpoint, Endpoint),
    /// Arrow domain reverses variance; codomain preserves it.
    Arrow(MotiveId, MotiveId),
    /// Both product positions preserve variance.
    Product(MotiveId, MotiveId),
    /// Both summands preserve variance.
    Sum(MotiveId, MotiveId),
}

/// Raw motive syntax, independent of certificate and term arenas.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Motives(Vec<Motive>);

impl Motives
{
    /// Create an empty motive arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self(Vec::new())
    }

    /// Append a motive whose children precede it.
    ///
    /// # Specification
    /// - ensures: the syntax remains acyclic, without deciding covariance.
    /// - fails: `UnknownMotive` for a missing child; insertion is atomic.
    /// - panics: none.
    ///
    /// # Errors
    /// `FlowError::UnknownMotive`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested arrows preserve variance parity, including one
    ///   shared subtree visited at both signs.
    /// - witness: `flow_universe::tests::symmetry_motive_is_refused_structurally`
    #[spec(
        captures: before = self.0.len(),
        ensures: |ret| match ret {
            Ok(id) => id.0 == before && self.0.get(id.0) == Some(&motive) && self.0.len() == before.saturating_add(1),
            Err(FlowError::UnknownMotive(id)) => self.0.len() == before && id.0 >= before,
            Err(_) => false,
        },
    )]
    #[inline]
    pub fn push(
        &mut self,
        motive: Motive,
    ) -> Result<MotiveId, FlowError>
    {
        match motive {
            | Motive::Arrow(left, right)
            | Motive::Product(left, right)
            | Motive::Sum(left, right) => {
                self.get(left)?;
                self.get(right)?;
            },
            | Motive::El(_) | Motive::Flow(..) => {},
        }
        let id = MotiveId(self.0.len());
        self.0.push(motive);
        Ok(id)
    }

    /// Resolve a motive node without erasing a missing-reference refusal.
    ///
    /// # Specification
    /// - ensures: returns exactly the node stored at `id`.
    /// - fails: `UnknownMotive` if `id` is out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// `FlowError::UnknownMotive`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed motive references refuse before traversal.
    /// - witness: `flow_universe::tests::symmetry_motive_is_refused_structurally`
    #[spec(ensures: |ret| match ret {
        Ok(node) => self.0.get(id.0) == Some(&node),
        Err(FlowError::UnknownMotive(named)) => named == id && id.0 >= self.0.len(),
        Err(_) => false,
    })]
    fn get(
        &self,
        id: MotiveId,
    ) -> Result<Motive, FlowError>
    {
        self.0
            .get(id.0)
            .copied()
            .ok_or(FlowError::UnknownMotive(id))
    }
}

/// Elaborate a directed motive's covariance side condition.
///
/// This is a formation judgement for the displayed grammar, not a general J
/// evaluator. Value transport uses its canonical motive `El(Moving)`.
///
/// # Specification
/// - ensures: no moving endpoint occurs at negative variance; arrow domains and
///   Flow sources each reverse variance, with products and sums preserving it.
/// - fails: `NonCovariantMotive` at a negative moving occurrence,
///   `UnknownMotive` for missing syntax, or `Budget` on exhausted traversal.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — symmetry `Flow(Moving, Fixed)` refuses, migration
///   `El(Fixed) -> El(Moving)` admits, and double reversal admits while shared
///   subtrees visited under opposite signs still refuse.
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_structurally`
#[spec(ensures: |ret| match ret {
    Ok(()) => u64::from(budget) > 0 && motives.get(root).is_ok() && !matches!(motives.get(root), Ok(Motive::Flow(Endpoint::Moving, _))),
    Err(FlowError::NonCovariantMotive(id)) => matches!(motives.get(id), Ok(Motive::El(Endpoint::Moving) | Motive::Flow(Endpoint::Moving, _) | Motive::Flow(_, Endpoint::Moving))),
    Err(FlowError::UnknownMotive(id)) => motives.0.get(id.0).is_none(),
    Err(FlowError::Budget) => true,
    Err(_) => false,
})]
#[inline]
pub fn check_motive(
    motives: &Motives,
    root: MotiveId,
    budget: ReplayBudget,
) -> Result<(), FlowError>
{
    let mut pending = Vec::from([(root, Variance::Covariant)]);
    let mut seen = BTreeSet::new();
    let mut allowance = Allowance(u64::from(budget));
    while let Some((id, variance)) = pending.pop() {
        allowance.charge()?;
        if !seen.insert((id, variance == Variance::Covariant)) {
            continue;
        }
        let occurrences = match motives.get(id)? {
            | Motive::El(endpoint) => [(endpoint, variance), (Endpoint::Fixed, variance)],
            | Motive::Flow(source, target) => [(source, variance.reverse()), (target, variance)],
            | Motive::Arrow(source, target) => {
                pending.push((target, variance));
                pending.push((source, variance.reverse()));
                continue;
            },
            | Motive::Product(left, right) | Motive::Sum(left, right) => {
                pending.push((right, variance));
                pending.push((left, variance));
                continue;
            },
        };
        if occurrences.contains(&(Endpoint::Moving, Variance::Contravariant)) {
            return Err(FlowError::NonCovariantMotive(id));
        }
    }
    Ok(())
}
