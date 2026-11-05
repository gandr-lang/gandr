//! The law checker against instances that pass and instances built to fail.
//!
//! The Boolean semiring is the finite reference: the disjunction adds, the
//! conjunction multiplies, and false lies below true. Each fault below breaks
//! one operation of it, and the checker names the first law the fault breaks
//! with the elements that break it.

use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_ordered_algebras::Arity;
use gandr_theory_ordered_algebras::Carrier;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::Distance;
use gandr_theory_ordered_algebras::InstanceName;
use gandr_theory_ordered_algebras::Law;
use gandr_theory_ordered_algebras::LawFailure;
use gandr_theory_ordered_algebras::Lawvere;
use gandr_theory_ordered_algebras::MaxPlus;
use gandr_theory_ordered_algebras::OrderedSemiring;
use gandr_theory_ordered_algebras::Outside;
use gandr_theory_ordered_algebras::Reach;
use gandr_theory_ordered_algebras::Tropical;
use gandr_theory_ordered_algebras::check;
use gandr_theory_ordered_algebras::check_law;
use num_bigint::BigInt;

/// The two truth values.
const TRUTHS: [Truth; 2] = [Truth::False, Truth::True];

/// A truth value of the Boolean semiring.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Truth
{
    /// False, the zero.
    False,
    /// True, the one.
    True,
}

/// One operation of the Boolean semiring that a test breaks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fault
{
    /// Nothing is broken.
    None,
    /// The zero is true.
    ZeroIsTrue,
    /// The multiplication is the disjunction.
    ProductIsDisjunction,
    /// Every element lies below every other.
    OrderIsTotal,
    /// The multiplication leaves the represented elements at true times true.
    ProductLeaves,
}

/// The Boolean semiring with at most one fault.
#[repr(transparent)]
struct Boolean(Fault);

impl OrderedSemiring for Boolean
{
    type Element = Truth;

    /// `boolean`.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from("boolean")
    }

    /// Both truth values.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, Truth>
    {
        Carrier::Whole(&TRUTHS)
    }

    /// False, or true under its fault.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> Truth
    {
        if self.0 == Fault::ZeroIsTrue {
            Truth::True
        }
        else {
            Truth::False
        }
    }

    /// True.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> Truth
    {
        Truth::True
    }

    /// The disjunction.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        left: &Truth,
        right: &Truth,
    ) -> Result<Truth, Outside>
    {
        Ok(if *left == Truth::True || *right == Truth::True {
            Truth::True
        }
        else {
            Truth::False
        })
    }

    /// The conjunction, or the fault's operation.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &Truth,
        right: &Truth,
    ) -> Result<Truth, Outside>
    {
        match self.0 {
            Fault::ProductIsDisjunction => self.add(left, right),
            Fault::ProductLeaves if *left == Truth::True && *right == Truth::True => Err(Outside),
            Fault::None | Fault::ZeroIsTrue | Fault::OrderIsTotal | Fault::ProductLeaves => {
                Ok(if *left == Truth::True && *right == Truth::True {
                    Truth::True
                }
                else {
                    Truth::False
                })
            },
        }
    }

    /// False below true, or every pair under its fault.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &Truth,
        upper: &Truth,
    ) -> Comparison
    {
        if self.0 == Fault::OrderIsTotal || lower == upper || *lower == Truth::False {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

/// The max-plus semiring with `0` for its zero in place of `−∞`.
#[repr(transparent)]
struct NoughtForZero(Tropical);

impl OrderedSemiring for NoughtForZero
{
    type Element = MaxPlus;

    /// `max-plus with zero 0`.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from("max-plus with zero 0")
    }

    /// The generated elements of the semiring it wraps.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, MaxPlus>
    {
        self.0.carrier()
    }

    /// The dyadic zero, the fault.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> MaxPlus
    {
        MaxPlus::Finite(Dyadic::ZERO)
    }

    /// The semiring's one.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> MaxPlus
    {
        self.0.one()
    }

    /// The semiring's maximum.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        left: &MaxPlus,
        right: &MaxPlus,
    ) -> Result<MaxPlus, Outside>
    {
        self.0.add(left, right)
    }

    /// The semiring's sum.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &MaxPlus,
        right: &MaxPlus,
    ) -> Result<MaxPlus, Outside>
    {
        self.0.multiply(left, right)
    }

    /// The semiring's order.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &MaxPlus,
        upper: &MaxPlus,
    ) -> Comparison
    {
        self.0.compare(lower, upper)
    }
}

/// The dyadic `mantissa · 2^exponent`.
///
/// # Specification
/// trivial.
fn dyadic(
    mantissa: BigInt,
    exponent: Exponent,
) -> Dyadic
{
    Dyadic::new(mantissa, exponent).expect("a dyadic in range")
}

/// The dyadic one half.
///
/// # Specification
/// trivial.
fn half() -> Dyadic
{
    dyadic(BigInt::from(1), Exponent::from(-1))
}

/// The max-plus semiring on `−∞` and the dyadics from minus one to three in
/// halves and wholes.
///
/// # Specification
/// trivial.
fn tropical() -> Tropical
{
    Tropical::generated(vec![
        MaxPlus::NegativeInfinity,
        MaxPlus::Finite(Dyadic::from(-1_i64)),
        MaxPlus::Finite(dyadic(BigInt::from(-1), Exponent::from(-1))),
        MaxPlus::Finite(Dyadic::ZERO),
        MaxPlus::Finite(half()),
        MaxPlus::Finite(Dyadic::from(1_i64)),
        MaxPlus::Finite(Dyadic::from(3_i64)),
    ])
}

/// The Lawvere quantale on `∞` and the distances from zero to four in halves
/// and wholes.
///
/// # Specification
/// trivial.
fn lawvere() -> Lawvere
{
    let finite = |value: Dyadic| Distance::finite(value).expect("a distance at or above zero");
    Lawvere::generated(vec![
        Distance::INFINITY,
        finite(Dyadic::ZERO),
        finite(half()),
        finite(Dyadic::from(1_i64)),
        finite(dyadic(BigInt::from(3), Exponent::from(-1))),
        finite(Dyadic::from(4_i64)),
    ])
}

/// The law and the elements of a broken law, or the checker's verdict when
/// the law is not broken.
///
/// # Specification
/// trivial.
fn broken<A>(algebra: &A) -> (Law, Vec<A::Element>)
where
    A: OrderedSemiring,
{
    match check(algebra) {
        Err(LawFailure::Broken(counterexample)) => {
            assert_eq!(counterexample.instance(), algebra.name());
            (counterexample.law(), counterexample.elements().to_vec())
        },
        verdict => panic!("{} is not broken: {verdict:?}", algebra.name()),
    }
}

#[test]
fn the_max_plus_semiring_passes_every_law()
{
    let decided = check(&tropical()).expect("every law holds");
    assert_eq!(usize::from(decided.laws()), 16);
    assert_eq!(decided.reach(), Reach::Generated);
    // Six laws of one variable, two of two and eight of three over seven
    // elements.
    assert_eq!(usize::from(decided.tuples()), 6 * 7 + 2 * 49 + 8 * 343);
}

#[test]
fn the_lawvere_quantale_passes_every_law()
{
    let decided = check(&lawvere()).expect("every law holds");
    assert_eq!(usize::from(decided.laws()), 16);
    assert_eq!(decided.reach(), Reach::Generated);
    assert_eq!(usize::from(decided.tuples()), 6 * 6 + 2 * 36 + 8 * 216);
    // The reverse order puts `∞` least and zero greatest, so the minimum is
    // the join.
    let quantale = lawvere();
    let zero = Distance::finite(Dyadic::ZERO).expect("zero is a distance");
    assert_eq!(
        quantale.compare(&Distance::INFINITY, &zero),
        Comparison::Below
    );
    assert_eq!(
        quantale.compare(&zero, &Distance::INFINITY),
        Comparison::NotBelow
    );
}

#[test]
fn the_boolean_semiring_passes_every_law_on_its_whole_carrier()
{
    let decided = check(&Boolean(Fault::None)).expect("every law holds");
    assert_eq!(decided.reach(), Reach::Whole);
    assert_eq!(usize::from(decided.tuples()), 6 * 2 + 2 * 4 + 8 * 8);
}

#[test]
fn a_broken_instance_yields_its_counterexample()
{
    // Each fault breaks a different law first, at the least elements in the
    // carrier's order.
    assert_eq!(
        broken(&Boolean(Fault::ZeroIsTrue)),
        (Law::AdditionUnit, vec![Truth::False])
    );
    assert_eq!(
        broken(&Boolean(Fault::ProductIsDisjunction)),
        (Law::MultiplicationUnitLeft, vec![Truth::False])
    );
    assert_eq!(
        broken(&Boolean(Fault::OrderIsTotal)),
        (Law::OrderAntisymmetric, vec![Truth::False, Truth::True])
    );
    // `max(0, −∞)` is `0`, so the first generated element breaks the unit.
    assert_eq!(
        broken(&NoughtForZero(tropical())),
        (Law::AdditionUnit, vec![MaxPlus::NegativeInfinity])
    );
    // An operation that leaves the represented elements leaves its law
    // undecided, apart from a broken one.
    match check(&Boolean(Fault::ProductLeaves)) {
        Err(LawFailure::Undecided(counterexample)) => {
            assert_eq!(counterexample.law(), Law::MultiplicationAssociative);
            assert_eq!(counterexample.elements(), &[
                Truth::False,
                Truth::True,
                Truth::True
            ]);
        },
        verdict => panic!("the product's refusal is not reported: {verdict:?}"),
    }
}

#[test]
fn each_law_reads_n_to_its_arity_tuples()
{
    let boolean = Boolean(Fault::None);
    for law in Law::ALL {
        let tuples = check_law(&boolean, law).expect("every law holds");
        let expected = match law.arity() {
            Arity::One => 2,
            Arity::Two => 4,
            Arity::Three => 8,
        };
        assert_eq!(usize::from(tuples), expected, "{law:?}");
    }
    // A failure names the law it was asked for.
    match check_law(&Boolean(Fault::OrderIsTotal), Law::OrderTransitive) {
        Ok(tuples) => assert_eq!(usize::from(tuples), 8),
        Err(failure) => panic!("transitivity holds in a total order: {failure}"),
    }
}

#[test]
fn a_negative_distance_is_refused()
{
    assert!(Distance::finite(Dyadic::from(-1_i64)).is_err());
    let zero = Distance::finite(Dyadic::ZERO).expect("zero is a distance");
    assert_eq!(zero.value(), Some(&Dyadic::ZERO));
    assert_eq!(Distance::INFINITY.value(), None);
}
