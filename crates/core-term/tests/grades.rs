//! The usage semiring of the core language, read as an ordered semiring
//! through the law checker of the ordered-algebras crate.
//!
//! [`Usage`] is zero, one or many uses. A [`HoldGrade`] or a
//! [`CapabilityGrade`] is the bound on the uses of its value: one use, or
//! many. The suite decides the sixteen laws on the three usages. It also
//! shows that a grade's two points alone break the unit of addition: the
//! least grade is one use, and one use plus one use is many.

use core::mem::size_of;

use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::usage::Usage;
use gandr_theory_ordered_algebras::Carrier;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::InstanceName;
use gandr_theory_ordered_algebras::Law;
use gandr_theory_ordered_algebras::LawFailure;
use gandr_theory_ordered_algebras::OrderedSemiring;
use gandr_theory_ordered_algebras::Outside;
use gandr_theory_ordered_algebras::Reach;
use gandr_theory_ordered_algebras::check;

/// The usage semiring on its three points.
#[repr(transparent)]
struct Usages
{
    /// Zero, one and many.
    carrier: [Usage; 3],
}

impl OrderedSemiring for Usages
{
    type Element = Usage;

    /// `usages`.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from("usages")
    }

    /// Zero, one and many: the whole carrier.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, Usage>
    {
        Carrier::Whole(&self.carrier)
    }

    /// No use.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> Usage
    {
        Usage::Zero
    }

    /// One use.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> Usage
    {
        Usage::One
    }

    /// The core language's addition.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        left: &Usage,
        right: &Usage,
    ) -> Result<Usage, Outside>
    {
        Ok(left.add(*right))
    }

    /// The core language's multiplication.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &Usage,
        right: &Usage,
    ) -> Result<Usage, Outside>
    {
        Ok(left.multiply(*right))
    }

    /// The core language's order.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &Usage,
        upper: &Usage,
    ) -> Comparison
    {
        if lower <= upper {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

/// The two points of the hold grade alone, with one use standing for the
/// zero that the grade lacks.
#[repr(transparent)]
struct TwoPoints
{
    /// One and many.
    carrier: [HoldGrade; 2],
}

impl OrderedSemiring for TwoPoints
{
    type Element = HoldGrade;

    /// `hold grades`.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from("hold grades")
    }

    /// One and many.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, HoldGrade>
    {
        Carrier::Whole(&self.carrier)
    }

    /// One use, the least grade.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> HoldGrade
    {
        HoldGrade::One
    }

    /// One use.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> HoldGrade
    {
        HoldGrade::One
    }

    /// Any two uses are many.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        _left: &HoldGrade,
        _right: &HoldGrade,
    ) -> Result<HoldGrade, Outside>
    {
        Ok(HoldGrade::Many)
    }

    /// One is the unit, and many times many is many.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &HoldGrade,
        right: &HoldGrade,
    ) -> Result<HoldGrade, Outside>
    {
        Ok(if *left == HoldGrade::One {
            *right
        }
        else {
            *left
        })
    }

    /// Each grade below itself and below many.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &HoldGrade,
        upper: &HoldGrade,
    ) -> Comparison
    {
        if lower == upper || *upper == HoldGrade::Many {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

#[test]
fn the_usage_semiring_passes_every_law()
{
    let usages = Usages {
        carrier: [Usage::Zero, Usage::One, Usage::Many],
    };
    let decided = check(&usages).expect("every law holds");
    assert_eq!(decided.reach(), Reach::Whole);
    assert_eq!(usize::from(decided.laws()), 16);
    assert_eq!(usize::from(decided.tuples()), 6 * 3 + 2 * 9 + 8 * 27);
}

#[test]
fn a_grade_admits_a_second_use_only_at_many()
{
    let copied = Usage::One.add(Usage::One);
    for (bound, many) in [
        (HoldGrade::Many.usage(), true),
        (HoldGrade::One.usage(), false),
        (CapabilityGrade::Durable.usage(), true),
        (CapabilityGrade::Consumable.usage(), false),
    ] {
        assert!(Usage::One <= bound, "every grade admits one use");
        assert_eq!(copied <= bound, many, "a second use at {bound:?}");
        assert_eq!(Usage::Zero <= bound, many, "a drop at {bound:?}");
    }
}

#[test]
fn a_usage_and_each_grade_fit_one_byte()
{
    assert_eq!(size_of::<Usage>(), 1);
    assert_eq!(size_of::<HoldGrade>(), 1);
    assert_eq!(size_of::<CapabilityGrade>(), 1);
}

#[test]
fn without_the_zero_a_grade_breaks_the_unit_of_addition()
{
    // The least grade is one use, and one use plus one use is many, so no
    // point of the grade is a unit of addition.
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
