//! The level context's admission against the landmark poset's loop-checking.
//!
//! `LevelContext::admit` asks the potential maintenance of
//! `theory-dynamic-graphs` for a model of a declaration's difference
//! constraints, and the poset validates that model before it admits. A
//! constraint `x + k ≤ y + j`, each side one variable with an offset, is a
//! difference constraint. The suite offers every set of one, two or three
//! distinct difference constraints over [`VARIABLES`] variables, each offset
//! below [`OFFSETS`], to the level context and to the poset's loop-checking.
//! The two verdicts agree on every set, and both verdicts occur. A constraint
//! whose right side takes a maximum of several variables is outside the
//! fragment, and the context admits or refuses it by loop-checking.

use gandr_kernel_core::KernelError;
use gandr_kernel_core::LevelContext;
use gandr_kernel_strata::AdmissionOutcome;
use gandr_kernel_strata::LandmarkConstraint;
use gandr_kernel_strata::LandmarkPoset;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::LevelParamCount;

/// The variables a constraint names.
const VARIABLES: u32 = 3;

/// One past the largest offset a side carries.
const OFFSETS: u64 = 2;

/// One side of a difference constraint: a variable with an offset.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Side
{
    /// The variable's index.
    variable: u32,
    /// The offset added to it.
    offset: u64,
}

/// A difference constraint `left ≤ right`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Difference
{
    /// The smaller side.
    left: Side,
    /// The larger side.
    right: Side,
}

/// Whether a set of constraints has a model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict
{
    /// Some valuation in the naturals satisfies every constraint.
    Consistent,
    /// No valuation satisfies them: a positive cycle forces a variable above
    /// itself.
    Looping,
}

impl Side
{
    /// This side as a level.
    ///
    /// # Specification
    /// trivial.
    fn level(self) -> Level
    {
        let mut level = Level::var(LevelVar::new(LevelVarIndex::from(self.variable)));
        for _step in 0 .. self.offset {
            level = level.succ().expect("a small offset stays representable");
        }
        level
    }
}

impl Difference
{
    /// This constraint as the poset reads it.
    ///
    /// # Specification
    /// trivial.
    fn landmark(self) -> LandmarkConstraint
    {
        LandmarkConstraint::leq(self.left.level(), self.right.level())
            .expect("a variable on each side is well formed")
    }
}

/// The level context's verdict on `constraints`.
///
/// # Specification
/// trivial.
fn context(constraints: Vec<LandmarkConstraint>) -> Verdict
{
    match LevelContext::admit(LevelParamCount::from(VARIABLES), constraints) {
        Ok(_context) => Verdict::Consistent,
        Err(KernelError::InconsistentLevelConstraints(_)) => Verdict::Looping,
        Err(other) => panic!("a set in scope is admitted or loops: {other:?}"),
    }
}

/// The poset's loop-checking verdict on `constraints`.
///
/// # Specification
/// trivial.
fn loop_checking(constraints: Vec<LandmarkConstraint>) -> Verdict
{
    match LandmarkPoset::admit(constraints).expect("a small system does not overflow") {
        AdmissionOutcome::Admitted(_) => Verdict::Consistent,
        AdmissionOutcome::Loop(_) => Verdict::Looping,
    }
}

/// Every difference constraint over [`VARIABLES`] variables, each offset
/// below [`OFFSETS`].
///
/// # Specification
/// trivial.
fn differences() -> Vec<Difference>
{
    let sides: Vec<Side> = (0 .. VARIABLES)
        .flat_map(|variable| (0 .. OFFSETS).map(move |offset| Side { variable, offset }))
        .collect();
    sides
        .iter()
        .flat_map(|&left| sides.iter().map(move |&right| Difference { left, right }))
        .collect()
}

#[test]
fn admission_agrees_with_loop_checking_on_difference_constraints()
{
    let all = differences();
    let mut verdicts = [0_usize; 2];
    let mut decide = |read: &[Difference]| {
        let landmarks = || {
            read.iter()
                .map(|&difference| difference.landmark())
                .collect()
        };
        let verdict = context(landmarks());
        assert_eq!(verdict, loop_checking(landmarks()), "{read:?}");
        let slot = verdicts
            .get_mut(usize::from(verdict == Verdict::Looping))
            .expect("two verdicts");
        *slot = slot.saturating_add(1);
    };
    // Each set of one, two or three distinct constraints, by ascending index.
    for (first, &one) in all.iter().enumerate() {
        decide(&[one]);
        for (second, &two) in all.iter().enumerate().skip(first.saturating_add(1)) {
            decide(&[one, two]);
            for &three in all.iter().skip(second.saturating_add(1)) {
                decide(&[one, two, three]);
            }
        }
    }
    // Both verdicts occur, so the agreement is not the agreement of a
    // constant answer.
    assert!(verdicts.iter().all(|&count| count > 0), "{verdicts:?}");
}

#[test]
fn a_maximum_on_the_right_is_admitted_by_loop_checking()
{
    let variable = |index: u32| Level::var(LevelVar::new(LevelVarIndex::from(index)));
    let joined = variable(1).max(&variable(2));
    // `x ≤ max(y, z)` holds at x = y = z = 0, and `x + 1 ≤ max(x, x)` has no
    // model. Neither is a difference constraint.
    let admits = LandmarkConstraint::leq(variable(0), joined).expect("variable-only sides");
    let successor = variable(0).succ().expect("one successor is representable");
    let loops = LandmarkConstraint::leq(successor, variable(0).max(&variable(0)))
        .expect("variable-only sides");
    assert_eq!(context(vec![admits.clone()]), Verdict::Consistent);
    assert_eq!(context(vec![admits, loops]), Verdict::Looping);
}
