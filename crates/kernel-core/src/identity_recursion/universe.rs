//! The universe clause reuses native paths; its next identity is a higher
//! record.

use anodized::spec;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

use super::Fiber;
use super::Fibers;
use super::Index;
use super::IndexId;
use super::RelationError;
use crate::higher_field::CertificateIdentity;
use crate::higher_field::HigherError;
use crate::replay::ReplayBudget;

impl Fibers
{
    /// Expose the native values of two computed index expressions.
    ///
    /// # Specification
    /// - ensures: preserves both endpoints; unresolved projections are not
    ///   replaced by guessed native values.
    /// - fails: `Arena` for an invalid index or `NeutralFiber` for a
    ///   projection.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested universe retains its native path fibre,
    ///   while an open product projection remains neutral.
    /// - witness: `path_universe::tests::universe_fold_tests::universe_clause_is_native`
    #[spec(ensures: |ret| match ret {
        Ok((a, b)) => matches!((self.get_index(left), self.get_index(right)), (Ok(Index::Value(x)), Ok(Index::Value(y))) if a == x && b == y),
        Err(RelationError::NeutralFiber) => matches!(self.get_index(left), Ok(Index::First(_) | Index::Second(_))) || matches!(self.get_index(right), Ok(Index::First(_) | Index::Second(_))),
        Err(RelationError::Arena) => self.get_index(left).is_err() || self.get_index(right).is_err(),
        Err(_) => false,
    })]
    pub(super) fn native_indices(
        &self,
        left: IndexId,
        right: IndexId,
    ) -> Result<(ValueId, ValueId), RelationError>
    {
        match (self.get_index(left)?, self.get_index(right)?) {
            | (Index::Value(left), Index::Value(right)) => Ok((left, right)),
            | _ => Err(RelationError::NeutralFiber),
        }
    }

    /// Unfold the next identity into the existing four higher record fields.
    ///
    /// # Specification
    /// - requires: endpoints retain their original live arena addresses.
    /// - ensures: rechecks both native equivalences and exposes pointwise
    ///   forward/backward identity and both round-trip coherence obligations.
    ///   No field is observed and no whole certificate equality is decided.
    /// - fails: `Relation(Classifier)` outside a certificate fibre; existing
    ///   native checking, endpoint, neutral-index and non-record refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`; field observations retain their own replay budgets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fold's certificate fibre exposes the same
    ///   obligations as native higher unfolding, not an inhabited Unit.
    /// - witness: `path_universe::tests::universe_fold_tests::universe_clause_is_native`
    #[spec(ensures: |ret| match ret {
        Ok(_) => matches!(self.get(self.root()), Ok(Fiber::Certificate(..))),
        Err(HigherError::Relation(RelationError::Classifier)) => !matches!(self.get(self.root()), Ok(Fiber::Certificate(..))),
        Err(_) => true,
    })]
    #[inline]
    pub fn certificate(
        &self,
        arena: &mut TermArena,
        budget: ReplayBudget,
    ) -> Result<CertificateIdentity, HigherError>
    {
        let Fiber::Certificate(left, right) = self.get(self.root())?
        else {
            return Err(RelationError::Classifier.into());
        };
        let (left, right) = self.native_indices(left, right)?;
        crate::higher_field::unfold(arena, left, right, budget)
    }
}
