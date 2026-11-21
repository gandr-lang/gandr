//! The exact amplitudes: their canonical form, the ring laws on generated
//! elements, the refusal past the 128-bit integers, and the state of `H T H`
//! on `|0⟩` with its squared moduli.

use gandr_theory_ordered_algebras::Amplitude;
use gandr_theory_ordered_algebras::Amplitudes;
use gandr_theory_ordered_algebras::Carrier;
use gandr_theory_ordered_algebras::CommutativeRing;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::Gate;
use gandr_theory_ordered_algebras::InstanceName;
use gandr_theory_ordered_algebras::Law;
use gandr_theory_ordered_algebras::LawFailure;
use gandr_theory_ordered_algebras::OrderedSemiring;
use gandr_theory_ordered_algebras::Outside;
use gandr_theory_ordered_algebras::QubitCount;
use gandr_theory_ordered_algebras::QubitIndex;
use gandr_theory_ordered_algebras::Reach;
use gandr_theory_ordered_algebras::RealAmplitude;
use gandr_theory_ordered_algebras::RealAmplitudes;
use gandr_theory_ordered_algebras::RingLaw;
use gandr_theory_ordered_algebras::State;
use gandr_theory_ordered_algebras::check_ring;
use gandr_theory_ordered_algebras::check_ring_law;
use proptest::prelude::*;

/// Eight amplitudes: zero, one, minus one, `i`, `ω`, `1/√2`, and two with
/// every coefficient set.
///
/// # Specification
/// trivial.
fn generated() -> Vec<Amplitude>
{
    vec![
        Amplitude::ZERO,
        Amplitude::ONE,
        amplitude!(-1, 0, 0, 0; 0),
        Amplitude::I,
        Amplitude::OMEGA,
        Amplitude::SQRT_HALF,
        amplitude!(2, 1, 0, 1; 2),
        amplitude!(3, -5, 7, 2; 3),
    ]
}

/// An amplitude with coefficients from `-64` to `64` and a scale up to six.
///
/// # Specification
/// trivial.
fn small() -> impl Strategy<Value = Amplitude>
{
    (
        -64_i128 ..= 64,
        -64_i128 ..= 64,
        -64_i128 ..= 64,
        -64_i128 ..= 64,
        0_u32 ..= 6,
    )
        .prop_map(|(a, b, c, d, k)| amplitude!(a, b, c, d; k))
}

/// One operation of the amplitudes that a test breaks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fault
{
    /// The product returns its left operand.
    LeftProduct,
    /// The negation returns its operand.
    SelfNegation,
}

/// The amplitudes with one operation broken.
struct Broken
{
    /// The ring whose operations the others keep.
    ring: Amplitudes,
    /// The broken operation.
    fault: Fault,
}

impl OrderedSemiring for Broken
{
    type Element = Amplitude;

    /// The ring's name.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        self.ring.name()
    }

    /// The ring's generated elements.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, Amplitude>
    {
        self.ring.carrier()
    }

    /// The ring's zero.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> Amplitude
    {
        self.ring.zero()
    }

    /// The ring's one.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> Amplitude
    {
        self.ring.one()
    }

    /// The ring's sum.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        left: &Amplitude,
        right: &Amplitude,
    ) -> Result<Amplitude, Outside>
    {
        self.ring.add(left, right)
    }

    /// The ring's product, or the left operand under its fault.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &Amplitude,
        right: &Amplitude,
    ) -> Result<Amplitude, Outside>
    {
        match self.fault {
            Fault::LeftProduct => Ok(*left),
            Fault::SelfNegation => self.ring.multiply(left, right),
        }
    }

    /// The ring's discrete order.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &Amplitude,
        upper: &Amplitude,
    ) -> Comparison
    {
        self.ring.compare(lower, upper)
    }
}

impl CommutativeRing for Broken
{
    /// The ring's negation, or the operand under its fault.
    ///
    /// # Specification
    /// trivial.
    fn negate(
        &self,
        element: &Amplitude,
    ) -> Result<Amplitude, Outside>
    {
        match self.fault {
            Fault::LeftProduct => self.ring.negate(element),
            Fault::SelfNegation => Ok(*element),
        }
    }
}

#[test]
fn the_amplitudes_pass_every_ring_law()
{
    let decided = check_ring(&Amplitudes::generated(generated())).expect("every law holds");
    assert_eq!(usize::from(decided.laws()), 18);
    assert_eq!(decided.reach(), Reach::Generated);
    // Seven laws of one variable, three of two and eight of three over eight
    // elements.
    assert_eq!(usize::from(decided.tuples()), 7 * 8 + 3 * 64 + 8 * 512);
}

#[test]
fn the_real_amplitudes_pass_every_ring_law()
{
    let ring = RealAmplitudes::generated(vec![
        RealAmplitude::ZERO,
        RealAmplitude::ONE,
        real!(-1, 0; 0),
        real!(0, 1; 1),
        real!(2, 1; 2),
        real!(3, -5; 3),
    ]);
    let decided = check_ring(&ring).expect("every law holds");
    assert_eq!(usize::from(decided.laws()), 18);
    assert_eq!(decided.reach(), Reach::Generated);
}

#[test]
fn a_broken_ring_yields_its_counterexample()
{
    let elements = vec![Amplitude::ZERO, Amplitude::ONE, Amplitude::I];
    // The left projection is associative and keeps the unit on the left, so
    // only the commutativity of the product names it; zero and one are the
    // first pair in which the order matters.
    let product = Broken {
        ring: Amplitudes::generated(elements.clone()),
        fault: Fault::LeftProduct,
    };
    match check_ring_law(&product, RingLaw::MultiplicationCommutative) {
        Err(LawFailure::Broken(counterexample)) => {
            assert_eq!(counterexample.law(), RingLaw::MultiplicationCommutative);
            assert_eq!(counterexample.elements(), [Amplitude::ZERO, Amplitude::ONE]);
        },
        verdict => panic!("the left projection commutes: {verdict:?}"),
    }
    // A negation that returns its operand keeps every other law, and zero is
    // its own negation, so one is the first element that breaks the inverse.
    let negation = Broken {
        ring: Amplitudes::generated(elements),
        fault: Fault::SelfNegation,
    };
    match check_ring(&negation) {
        Err(LawFailure::Broken(counterexample)) => {
            assert_eq!(counterexample.instance(), InstanceName::from("amplitudes"));
            assert_eq!(counterexample.law(), RingLaw::AdditionInverse);
            assert_eq!(counterexample.elements(), [Amplitude::ONE]);
        },
        verdict => panic!("the identity negates: {verdict:?}"),
    }
}

#[test]
fn the_added_laws_read_n_to_their_arity_tuples()
{
    let ring = Amplitudes::generated(vec![Amplitude::ZERO, Amplitude::ONE, Amplitude::I]);
    let commutative = check_ring_law(&ring, RingLaw::MultiplicationCommutative).expect("it holds");
    let inverse = check_ring_law(&ring, RingLaw::AdditionInverse).expect("it holds");
    assert_eq!(usize::from(commutative), 9);
    assert_eq!(usize::from(inverse), 3);
}

#[test]
fn a_coefficient_past_128_bits_is_refused()
{
    let most = amplitude!(i128::MAX, 0, 0, 0; 0);
    assert_eq!(most.add(&Amplitude::ONE), Err(Outside));
    assert_eq!(most.multiply(&amplitude!(2, 0, 0, 0; 0)), Err(Outside));
    assert_eq!(amplitude!(i128::MIN, 0, 0, 0; 0).negate(), Err(Outside));
    assert_eq!(amplitude!(0, 0, i128::MIN, 0; 0).conjugate(), Err(Outside));
    // A sum with `1/√2` lifts `most` to scale one, which doubles it.
    assert_eq!(most.add(&Amplitude::SQRT_HALF), Err(Outside));
    // The checker reads the refusal as an undecided law, never as a broken
    // one: the first law sums `most` with itself.
    match check_ring(&Amplitudes::generated(vec![most])) {
        Err(LawFailure::Undecided(counterexample)) => {
            assert_eq!(
                counterexample.law(),
                RingLaw::Semiring(Law::AdditionAssociative)
            );
            assert_eq!(counterexample.elements(), [most, most, most]);
        },
        verdict => panic!("the sum of the greatest coefficient is not refused: {verdict:?}"),
    }
}

#[test]
fn forms_with_every_coefficient_even_reduce()
{
    assert_eq!(amplitude!(2, 0, 0, 0; 1), Amplitude::ONE);
    assert_eq!(amplitude!(0, 2, 0, 2; 2), Amplitude::OMEGA);
    assert_eq!(amplitude!(4, 0, 4, 0; 2), amplitude!(1, 0, 1, 0; 0));
    // An odd coefficient stops the reduction.
    let half_root = amplitude!(0, 1, 0, 0; 1);
    assert_eq!(u32::from(half_root.scale()), 1);
}

#[test]
fn zero_at_any_scale_is_zero()
{
    for scale in [0_u32, 1, 127, u32::MAX] {
        assert_eq!(amplitude!(0, 0, 0, 0; scale), Amplitude::ZERO);
        assert_eq!(real!(0, 0; scale), RealAmplitude::ZERO);
    }
}

#[test]
fn the_state_of_h_t_h_on_zero_is_exact()
{
    let expected = [amplitude!(2, 1, 0, 1; 2), amplitude!(2, -1, 0, -1; 2)];
    let mut state = State::ground(QubitCount::from(1)).expect("one qubit");
    for gate in [Gate::HADAMARD, Gate::T, Gate::HADAMARD] {
        state
            .apply_one(&gate, QubitIndex::from(0))
            .expect("an exact step");
    }
    assert_eq!(state.amplitudes(), expected);
    // The matrices act on `|0⟩` to the same amplitudes.
    let mut vector = [Amplitude::ONE, Amplitude::ZERO];
    for gate in [Gate::HADAMARD, Gate::T, Gate::HADAMARD] {
        vector = gate.act(&vector).expect("an exact action");
    }
    assert_eq!(vector, expected);
}

#[test]
fn the_squared_moduli_of_h_t_h_sum_to_one()
{
    let [first, second] = [amplitude!(2, 1, 0, 1; 2), amplitude!(2, -1, 0, -1; 2)]
        .map(|amplitude| amplitude.squared_modulus().expect("an exact square"));
    assert_eq!(first, real!(2, 1; 2));
    assert_eq!(second, real!(2, -1; 2));
    assert_eq!(first.add(&second), Ok(RealAmplitude::ONE));
    assert_eq!(Amplitude::SQRT_HALF.squared_modulus(), Ok(real!(1, 0; 1)));
    assert_eq!(Amplitude::OMEGA.squared_modulus(), Ok(RealAmplitude::ONE));
    // The real amplitude reads back as an amplitude with no imaginary part.
    assert_eq!(Amplitude::from(real!(1, 0; 1)), amplitude!(1, 0, 0, 0; 1));
}

proptest! {
    /// A form lifted by any shift, every coefficient times `2^shift` at the
    /// scale plus `shift`, reduces back to the form itself, and the form's
    /// scale is the least: at a positive scale, a coefficient is odd.
    #[test]
    fn a_scaled_form_reduces_to_its_own(
        a in -1024_i128 ..= 1024,
        b in -1024_i128 ..= 1024,
        c in -1024_i128 ..= 1024,
        d in -1024_i128 ..= 1024,
        k in 0_u32 ..= 8,
        shift in 0_u32 ..= 8,
    ) {
        let form = amplitude!(a, b, c, d; k);
        let factor = 1_i128.checked_shl(shift).expect("a small shift");
        let [a, b, c, d] = [a, b, c, d].map(|coefficient| coefficient.checked_mul(factor).expect("a small product"));
        let lifted = amplitude!(a, b, c, d; k.checked_add(shift).expect("a small scale"));
        prop_assert_eq!(lifted, form);
        let odd = form
            .coefficients()
            .iter()
            .any(|coefficient| i128::from(*coefficient) & 1 != 0);
        prop_assert!(u32::from(form.scale()) == 0 || odd);
    }

    /// Every set of up to four small amplitudes passes the eighteen laws.
    #[test]
    fn generated_amplitudes_pass_every_ring_law(elements in prop::collection::vec(small(), 1 ..= 4)) {
        let laws = check_ring(&Amplitudes::generated(elements)).map(|decided| usize::from(decided.laws()));
        prop_assert_eq!(laws, Ok(18));
    }
}
