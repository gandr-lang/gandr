//! The grades of the core language read as ordered semirings through the law
//! checker of the ordered-algebras crate.
//!
//! A [`HoldGrade`] or a [`CapabilityGrade`] counts uses: one, or any number.
//! Neither enum has a zero, and neither states an operation. The suite
//! adjoins the zero, `None`, and reads each enum in the semiring of usages. A
//! sum of two single uses is many. A product with zero is zero, and a product
//! with one is the other factor. The order puts zero and one below many and
//! leaves them apart, because a linear use is neither dropped nor duplicated.

use core::fmt::Debug;

use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::memory::HoldGrade;
use gandr_theory_ordered_algebras::Carrier;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::InstanceName;
use gandr_theory_ordered_algebras::Law;
use gandr_theory_ordered_algebras::LawFailure;
use gandr_theory_ordered_algebras::OrderedSemiring;
use gandr_theory_ordered_algebras::Outside;
use gandr_theory_ordered_algebras::Reach;
use gandr_theory_ordered_algebras::check;

/// A two-point grade of the core language: one use, or any number.
trait Usage: Copy + Debug + Eq
{
    /// The instance's name.
    const NAME: &'static str;
    /// The grade of one use.
    const ONE: Self;
    /// The grade of any number of uses.
    const MANY: Self;
}

impl Usage for HoldGrade
{
    const MANY: Self = Self::Many;
    const NAME: &'static str = "hold grades";
    const ONE: Self = Self::One;
}

impl Usage for CapabilityGrade
{
    const MANY: Self = Self::Durable;
    const NAME: &'static str = "capability grades";
    const ONE: Self = Self::Consumable;
}

/// The semiring of usages on a two-point grade, with `None` as the zero.
#[repr(transparent)]
struct Usages<G>
{
    /// Zero, one and many.
    carrier: [Option<G>; 3],
}

impl<G> Usages<G>
where
    G: Usage,
{
    /// The semiring on the grade's two points and the adjoined zero.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            carrier: [None, Some(G::ONE), Some(G::MANY)],
        }
    }
}

impl<G> OrderedSemiring for Usages<G>
where
    G: Usage,
{
    type Element = Option<G>;

    /// The grade's name.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from(G::NAME)
    }

    /// Zero, one and many: the whole carrier.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, Option<G>>
    {
        Carrier::Whole(&self.carrier)
    }

    /// The adjoined zero.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> Option<G>
    {
        None
    }

    /// One use.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> Option<G>
    {
        Some(G::ONE)
    }

    /// Zero adds nothing, and any two uses are many.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        left: &Option<G>,
        right: &Option<G>,
    ) -> Result<Option<G>, Outside>
    {
        Ok(match (*left, *right) {
            (None, other) | (other, None) => other,
            (Some(_), Some(_)) => Some(G::MANY),
        })
    }

    /// Zero annihilates, one is the unit, and many times many is many.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &Option<G>,
        right: &Option<G>,
    ) -> Result<Option<G>, Outside>
    {
        Ok(match (*left, *right) {
            (None, _) | (_, None) => None,
            (Some(first), Some(second)) if first == G::ONE => Some(second),
            (Some(first), Some(_)) => Some(first),
        })
    }

    /// Each grade below itself and below many.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &Option<G>,
        upper: &Option<G>,
    ) -> Comparison
    {
        if lower == upper || *upper == Some(G::MANY) {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

/// The two points of a grade alone, with one use standing for the zero the
/// enum lacks.
#[repr(transparent)]
struct TwoPoints<G>
{
    /// One and many.
    carrier: [G; 2],
}

impl<G> OrderedSemiring for TwoPoints<G>
where
    G: Usage,
{
    type Element = G;

    /// The grade's name.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from(G::NAME)
    }

    /// One and many.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, G>
    {
        Carrier::Whole(&self.carrier)
    }

    /// One use, the least grade the enum holds.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> G
    {
        G::ONE
    }

    /// One use.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> G
    {
        G::ONE
    }

    /// Any two uses are many.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        _left: &G,
        _right: &G,
    ) -> Result<G, Outside>
    {
        Ok(G::MANY)
    }

    /// One is the unit, and many times many is many.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &G,
        right: &G,
    ) -> Result<G, Outside>
    {
        Ok(if *left == G::ONE { *right } else { *left })
    }

    /// Each grade below itself and below many.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &G,
        upper: &G,
    ) -> Comparison
    {
        if lower == upper || *upper == G::MANY {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

#[test]
fn hold_grades_pass_every_law_with_a_zero_adjoined()
{
    let decided = check(&Usages::<HoldGrade>::new()).expect("every law holds");
    assert_eq!(decided.reach(), Reach::Whole);
    assert_eq!(usize::from(decided.tuples()), 6 * 3 + 2 * 9 + 8 * 27);
}

#[test]
fn capability_grades_pass_every_law_with_a_zero_adjoined()
{
    let decided = check(&Usages::<CapabilityGrade>::new()).expect("every law holds");
    assert_eq!(decided.reach(), Reach::Whole);
    assert_eq!(usize::from(decided.laws()), 16);
}

#[test]
fn without_the_zero_a_grade_breaks_the_unit_of_addition()
{
    // The least grade the enum holds is one use, and one use plus one use is
    // many, so no point of the enum is a unit of addition.
    let points = TwoPoints {
        carrier: [HoldGrade::One, HoldGrade::Many],
    };
    match check(&points) {
        Err(LawFailure::Broken(counterexample)) => {
            assert_eq!(counterexample.law(), Law::AdditionUnit);
            assert_eq!(counterexample.elements(), &[HoldGrade::One]);
        },
        verdict => panic!("two points pass as a semiring: {verdict:?}"),
    }
}
