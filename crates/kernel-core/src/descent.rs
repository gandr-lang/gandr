//! **The descent skeleton**: one replay for the certificates the kernel
//! checks.
//!
//! A certificate is a descent datum. Its cover groups positions into classes.
//! A local checker glues each class once, and each position agrees with the
//! gluing of its class. [`Descent`] names a datum's local checker, and
//! [`replay`] drives any datum through the skeleton: it glues the class once,
//! binds the gluing once and agrees each position in order. The first refusal
//! ends the replay. The skeleton is generic over the local checker and
//! monomorphised, so a replay costs what its local checker costs.
//!
//! # Items
//!
//! The kernel replays two certificate shapes through [`replay`].
//!
//! | Certificate | Class | Gluing | Positions |
//! | --- | --- | --- | --- |
//! | A conversion trace | the claimed goal | [`crate::replay::replay`] | none: the trivial cover |
//! | A guarded family with its rows | the [`Proposal`] | [`Schema::check`], bound once by [`Schema::bind`] | each member under its row, by [`Schema::substitute`] and [`Substitution::admit`] |
//!
//! A spinal catalogue or ladder trace is a conversion trace. The spinal stance
//! shares inside the engine and leaves no mark on its certificate. A
//! conversion trace holds no overlap, because the engine emits a shared
//! derivation once under each parent. A cover with several positions in one
//! class needs a back-reference in the decision vocabulary.
//!
//! # Boundaries
//!
//! A cover is a computed relation. A class is a goal or a schema that the
//! kernel checks, never a table that asserts sameness. Hash-consing has no
//! instance, because its coverage is asserted, not computed. The skeleton adds
//! no premise to a local checker and drops none, so it certifies exactly what
//! the local checker does. The datum's producer stays outside the trusted
//! base.
//!
//! # References
//!
//! - `vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa` — exemplar: sharing as
//!   descent (§ sharing-rule-descent, § sharing-rule-specialisations, §
//!   sharing-rule-probe) — positions, a cover, a gluing done once and the
//!   certificate the kernel replays, with hash-consing's asserted coverage
//!   banned.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel
//!   re-assessment's design (§ kernel-reassessment-design item 7) — one
//!   skeleton for every certificate, generic over the local checker and
//!   monomorphised.
//!
//! [`Proposal`]: crate::admission::Proposal
//! [`Schema::check`]: crate::admission::Schema::check
//! [`Schema::bind`]: crate::admission::Schema::bind
//! [`Schema::substitute`]: crate::admission::Schema::substitute
//! [`Substitution::admit`]: crate::admission::Substitution::admit

/// A certificate's local checker, read as a descent datum over classes of
/// type `Class`.
///
/// # Specification
/// - requires: [`Descent::glue`] checks a class's whole local obligation.
///   [`Descent::bind`] prepares a gluing for reading and decides nothing that a
///   position owes. [`Descent::agree`] checks one position against the bound
///   gluing alone.
/// - ensures: [`replay`] certifies a class and its positions exactly when the
///   local checker does.
/// - provides: the local checker that the skeleton is generic over.
/// - panics: none.
/// - executable: none — a predicate on the declaration changes the methods an
///   implementor owes, and each instance's methods state their own clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a recording datum observes each call the skeleton makes,
///   and the kernel's two instances keep their verdicts and refusals. This
///   separates a skeleton that glues per position, reorders positions or reads
///   past a refusal.
/// - witness: `descent::tests::a_class_is_glued_once_and_its_positions_agreed_in_order`
/// - witness: `descent::tests::the_first_refusal_ends_the_replay`
/// - witness: `admission::tests::a_family_replays_through_the_descent_skeleton`
pub trait Descent<Class>
{
    /// What gluing a class yields: the evidence its positions agree with.
    type Gluing;

    /// A gluing prepared for reading, which may borrow it.
    type Bound<'glued>
    where
        Self: 'glued;

    /// One position of the cover.
    type Position;

    /// Why the local checker refuses a class or a position.
    type Refusal;

    /// Glue `class` once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the gluing exactly when the class meets its local obligation;
    ///   otherwise the refusal.
    /// - fails: the class's refusal.
    /// - panics: none.
    /// - executable: none — a predicate on the declaration changes the methods
    ///   an implementor owes.
    ///
    /// # Errors
    /// Returns the refusal of the class.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused class ends the replay before any bind or
    ///   agreement.
    /// - witness: `descent::tests::the_first_refusal_ends_the_replay`
    fn glue(
        &mut self,
        class: Class,
    ) -> Result<Self::Gluing, Self::Refusal>;

    /// Prepare `gluing` for the agreement of its positions.
    ///
    /// # Specification
    /// - requires: `gluing` is the gluing [`Descent::glue`] answered.
    /// - ensures: a reading of `gluing` that decides nothing a position owes;
    ///   otherwise the refusal.
    /// - fails: the binding's refusal.
    /// - panics: none.
    /// - executable: none — a predicate on the declaration changes the methods
    ///   an implementor owes.
    ///
    /// # Errors
    /// Returns the refusal of the binding.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the skeleton binds once, before the first position.
    /// - witness: `descent::tests::a_class_is_glued_once_and_its_positions_agreed_in_order`
    fn bind<'glued>(
        &mut self,
        gluing: &'glued Self::Gluing,
    ) -> Result<Self::Bound<'glued>, Self::Refusal>;

    /// Check that `position` agrees with the bound gluing of its class.
    ///
    /// # Specification
    /// - requires: `bound` is the binding [`Descent::bind`] answered.
    /// - ensures: success exactly when the position meets its local obligation
    ///   against the gluing; otherwise the refusal.
    /// - fails: the position's refusal.
    /// - panics: none.
    /// - executable: none — a predicate on the declaration changes the methods
    ///   an implementor owes.
    ///
    /// # Errors
    /// Returns the refusal of the position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused member of a family ends its replay, and the
    ///   positions before it agree.
    /// - witness: `descent::tests::the_first_refusal_ends_the_replay`
    /// - witness: `admission::tests::a_family_replays_through_the_descent_skeleton`
    fn agree(
        &mut self,
        bound: &Self::Bound<'_>,
        position: Self::Position,
    ) -> Result<(), Self::Refusal>;
}

/// Replay one class of a descent datum: glue it once, bind the gluing once
/// and agree each of `positions` with it, in order.
///
/// # Specification
/// - requires: `positions` are the positions the cover puts in `class`.
/// - ensures: the gluing exactly when [`Descent::glue`] answers `class`,
///   [`Descent::bind`] answers the gluing and [`Descent::agree`] answers every
///   position; otherwise the first refusal in that order. The class is glued
///   once and bound once, and no position after a refusal is read.
/// - fails: the local checker's first refusal.
/// - panics: none.
/// - executable: none — the laws count the calls to the datum's methods, and a
///   predicate over the result does not see them.
///
/// # Errors
/// Returns the first refusal of the datum's local checker.
///
/// # Adequacy
/// - hypothesis: L3 — a recording datum observes the calls on an accepted
///   class, on an empty cover, on a refused class and on a refused position.
///   The kernel's two instances replay their accepted and refused certificates
///   through this function.
/// - witness: `descent::tests::a_class_is_glued_once_and_its_positions_agreed_in_order`
/// - witness: `descent::tests::the_first_refusal_ends_the_replay`
/// - witness: `admission::tests::a_family_replays_through_the_descent_skeleton`
/// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
#[inline]
pub fn replay<Class, Datum, Positions>(
    datum: &mut Datum,
    class: Class,
    positions: Positions,
) -> Result<Datum::Gluing, Datum::Refusal>
where
    Datum: Descent<Class>,
    Positions: IntoIterator<Item = Datum::Position>,
{
    let gluing = datum.glue(class)?;
    {
        let bound = datum.bind(&gluing)?;
        for position in positions {
            datum.agree(&bound, position)?;
        }
    }
    Ok(gluing)
}

#[cfg(test)]
mod tests;
