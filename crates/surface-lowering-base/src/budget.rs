//! The work one lowering may spend: the allowance a caller gives, the tank
//! every charged pass spends from, and the most cells a face poset holds.

use core::fmt;

use anodized::spec;

use crate::error::LoweringRefusal;

/// The work one lowering may spend before it refuses.
///
/// One step is charged per node visited, per binder frame walked, per module
/// child and per attribute, so the allowance bounds the whole lowering rather
/// than any single sweep.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The limit is shared across the lowering run rather than renewed
///   for each pass.
/// - provides: A nominal bound on charged work, including the zero allowance.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The value has no work history to inspect; `Fuel::new`
///   and `Fuel::spend` check initialization and consumption.
///
/// # Adequacy
/// - hypothesis: L3 — the last allowed charge succeeds and the next charge
///   names the original limit.
/// - witness: `budget::tests::the_last_step_of_an_allowance_is_spendable`
/// - witness: `budget::tests::a_step_past_the_allowance_is_refused`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LoweringBudget(usize);

impl LoweringBudget
{
    /// The allowance a caller with no reason to bound the walk takes.
    pub const DEFAULT: Self = Self(1_000_000_usize);
}

impl From<usize> for LoweringBudget
{
    /// The allowance of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: usize) -> Self
    {
        Self(steps)
    }
}

impl From<LoweringBudget> for usize
{
    /// The number of steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: LoweringBudget) -> Self
    {
        budget.0
    }
}

impl fmt::Display for LoweringBudget
{
    /// Writes the number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// One lowering's remaining allowance.
///
/// # Specification
/// - requires: Instances are created by new and changed only by spend.
/// - ensures: The remaining allowance never exceeds its original budget, and an
///   exhausted tank remains exhausted.
/// - provides: The shared state of all charged passes.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Type-level invariant expansion is unavailable in the
///   enabled specification facade; new and spend carry the executable state
///   relation.
///
/// # Adequacy
/// - hypothesis: L3 — initialization and the last-success/first-refusal
///   boundary distinguish off-by-one charging and preserve the reported
///   allowance.
/// - witness: `budget::tests::the_last_step_of_an_allowance_is_spendable`
/// - witness: `budget::tests::a_step_past_the_allowance_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fuel
{
    /// How many steps are left.
    remaining: usize,
    /// The allowance the caller set, carried so a refusal can name it.
    budget: LoweringBudget,
}

impl Fuel
{
    /// A full tank at `budget`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance equals the supplied budget, whose
    ///   original value is retained.
    /// - provides: a shared tank for every charged pass.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last permitted charge and first excess charge
    ///   distinguish initialization from an off-by-one allowance.
    /// - witness: `budget::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `budget::tests::a_step_past_the_allowance_is_refused`
    #[spec(
        ensures: |ret| ret.remaining == budget.0 && ret.budget.0 == budget.0,
    )]
    #[inline]
    #[must_use]
    pub const fn new(budget: LoweringBudget) -> Self
    {
        Self {
            remaining: budget.0,
            budget,
        }
    }

    /// How many steps are left.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn remaining(&self) -> usize
    {
        self.remaining
    }

    /// The allowance the caller set, which a refusal names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn budget(&self) -> LoweringBudget
    {
        self.budget
    }

    /// Charge one step of work.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance is one lower on success, so a caller
    ///   that charges once per unit of work cannot outrun the allowance by more
    ///   than the unit it was charged for.
    /// - provides: the one place the allowance is spent, so no sweep can walk
    ///   uncharged.
    /// - fails: [`LoweringRefusal::BudgetExceeded`], naming the allowance the
    ///   caller set, once nothing remains; the tank stays empty, so every later
    ///   charge refuses alike.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance is spent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one checked subtraction, separated by the
    ///   boundary pair of the last successful charge and the first refused one
    ///   over an allowance of one, with the exact refusal variant and its
    ///   allowance asserted.
    /// - witness: `budget::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `budget::tests::a_step_past_the_allowance_is_refused`
    #[spec(
        captures: before = (self.remaining, self.budget),
        ensures: |ret| {
            self.budget == before.1
                && self.remaining == before.0.saturating_sub(1)
                && ret
                    == if before.0 == 0 {
                        Err(LoweringRefusal::BudgetExceeded { budget: before.1 })
                    }
                    else {
                        Ok(())
                    }
        },
    )]
    #[inline]
    pub fn spend<'refusal>(&mut self) -> Result<(), LoweringRefusal<'refusal>>
    {
        let Some(remaining) = self.remaining.checked_sub(1_usize)
        else {
            return Err(LoweringRefusal::BudgetExceeded {
                budget: self.budget,
            });
        };
        self.remaining = remaining;

        Ok(())
    }
}

/// The most cells a record type's face poset holds: its faces and their new
/// meets. Each row of the order keeps one word for each 64 cells, so a poset
/// at the budget keeps 64 words for each cell.
pub const FACE_CELLS: usize = 4_096;

#[cfg(test)]
mod tests
{
    use super::Fuel;
    use super::LoweringBudget;
    use crate::error::LoweringRefusal;

    #[test]
    fn the_last_step_of_an_allowance_is_spendable()
    {
        let mut fuel = Fuel::new(LoweringBudget::from(1_usize));

        assert_eq!(fuel.spend(), Ok(()), "an allowance of one admits one step");
    }

    #[test]
    fn a_step_past_the_allowance_is_refused()
    {
        let budget = LoweringBudget::from(1_usize);
        let mut fuel = Fuel::new(budget);
        let _first = fuel.spend();

        assert_eq!(
            fuel.spend(),
            Err(LoweringRefusal::BudgetExceeded { budget }),
            "the step past the allowance is refused, naming the allowance"
        );
    }
}
