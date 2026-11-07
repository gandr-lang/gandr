//! The gates as matrices over exact amplitudes: each one unitary, every word
//! of them unitary, a register that agrees with the matrix of its circuit and
//! returns to `|0…0⟩` under the circuit's inverse, and a refused step that
//! leaves the register as it was.

use gandr_theory_ordered_algebras::Amplitude;
use gandr_theory_ordered_algebras::CircuitRefusal;
use gandr_theory_ordered_algebras::Gate;
use gandr_theory_ordered_algebras::QubitCount;
use gandr_theory_ordered_algebras::QubitIndex;
use gandr_theory_ordered_algebras::State;
use proptest::prelude::*;

/// `CNOT` with the second qubit the control: it swaps `|01⟩` and `|11⟩`.
const CNOT_REVERSED: Gate<4> = Gate::new([
    [
        Amplitude::ONE,
        Amplitude::ZERO,
        Amplitude::ZERO,
        Amplitude::ZERO,
    ],
    [
        Amplitude::ZERO,
        Amplitude::ZERO,
        Amplitude::ZERO,
        Amplitude::ONE,
    ],
    [
        Amplitude::ZERO,
        Amplitude::ZERO,
        Amplitude::ONE,
        Amplitude::ZERO,
    ],
    [
        Amplitude::ZERO,
        Amplitude::ONE,
        Amplitude::ZERO,
        Amplitude::ZERO,
    ],
]);

/// A gate on one qubit.
#[derive(Clone, Copy, Debug)]
enum Single
{
    /// `H`.
    Hadamard,
    /// `S`.
    Phase,
    /// `T`.
    Eighth,
}

impl Single
{
    /// The gate's matrix.
    ///
    /// # Specification
    /// trivial.
    const fn gate(self) -> Gate<2>
    {
        match self {
            Self::Hadamard => Gate::HADAMARD,
            Self::Phase => Gate::PHASE,
            Self::Eighth => Gate::T,
        }
    }
}

/// One step of a circuit: a gate on one qubit at its place, or `CNOT` from a
/// control to a target.
#[derive(Clone, Copy, Debug)]
enum Step
{
    /// A gate on one qubit.
    One(Single, QubitIndex),
    /// `CNOT`, the control first.
    Two(QubitIndex, QubitIndex),
}

/// A gate on one qubit.
///
/// # Specification
/// trivial.
fn single() -> impl Strategy<Value = Single>
{
    prop_oneof![
        Just(Single::Hadamard),
        Just(Single::Phase),
        Just(Single::Eighth)
    ]
}

/// A step on a register of `qubits` qubits, at least two.
///
/// # Specification
/// trivial.
fn step(qubits: QubitCount) -> impl Strategy<Value = Step>
{
    let count = u32::from(qubits);
    let place = move || (0 .. count).prop_map(QubitIndex::from);
    prop_oneof![
        (single(), place()).prop_map(|(gate, target)| Step::One(gate, target)),
        (place(), 1 .. count).prop_map(move |(control, offset)| {
            let target = u32::from(control)
                .checked_add(offset)
                .expect("a small place")
                .checked_rem(count)
                .expect("a register of qubits");
            Step::Two(control, QubitIndex::from(target))
        }),
    ]
}

/// `gate · gate†`.
///
/// # Specification
/// trivial.
fn times_adjoint<const SIDE: usize>(gate: &Gate<SIDE>) -> Gate<SIDE>
{
    gate.multiply(&gate.adjoint().expect("an exact adjoint"))
        .expect("an exact product")
}

/// The matrix of a step on a register of two qubits.
///
/// # Specification
/// trivial.
fn matrix(step: Step) -> Gate<4>
{
    let identity = Gate::<2>::identity();
    match step {
        Step::One(gate, target) if u32::from(target) == 0 => gate.gate().tensor(&identity),
        Step::One(gate, _) => identity.tensor(&gate.gate()),
        Step::Two(control, _) if u32::from(control) == 0 => Ok(Gate::CNOT),
        Step::Two(..) => Ok(CNOT_REVERSED),
    }
    .expect("an exact tensor product")
}

/// Applies `step` to `state`.
///
/// # Specification
/// trivial.
fn apply(
    state: &mut State,
    step: Step,
)
{
    match step {
        Step::One(gate, target) => state.apply_one(&gate.gate(), target),
        Step::Two(control, target) => state.apply_two(&Gate::CNOT, control, target),
    }
    .expect("an exact step");
}

#[test]
fn each_gate_is_unitary()
{
    for gate in [Gate::HADAMARD, Gate::PHASE, Gate::T] {
        assert_eq!(times_adjoint(&gate), Gate::identity(), "{gate:?}");
    }
    assert_eq!(times_adjoint(&Gate::CNOT), Gate::identity());
    assert_eq!(times_adjoint(&CNOT_REVERSED), Gate::identity());
    // `H` and `CNOT` are their own inverses; `T` is not its own adjoint, and
    // `T²` is `S`.
    assert_eq!(
        Gate::HADAMARD.multiply(&Gate::HADAMARD),
        Ok(Gate::identity())
    );
    assert_eq!(Gate::CNOT.multiply(&Gate::CNOT), Ok(Gate::identity()));
    assert_ne!(Gate::T.adjoint(), Ok(Gate::T));
    assert_eq!(Gate::T.multiply(&Gate::T), Ok(Gate::PHASE));
}

#[test]
fn a_refused_step_leaves_the_state()
{
    let wide = QubitCount::from(21);
    assert_eq!(
        State::ground(wide),
        Err(CircuitRefusal::Wide { qubits: wide })
    );
    let two = QubitCount::from(2);
    let mut state = State::ground(two).expect("two qubits");
    state
        .apply_one(&Gate::HADAMARD, QubitIndex::from(0))
        .expect("an exact step");
    let before = state.clone();
    assert_eq!(
        state.apply_one(&Gate::T, QubitIndex::from(2)),
        Err(CircuitRefusal::Absent {
            qubit: QubitIndex::from(2),
            qubits: two
        })
    );
    assert_eq!(state, before);
    assert_eq!(
        state.apply_two(&Gate::CNOT, QubitIndex::from(1), QubitIndex::from(1)),
        Err(CircuitRefusal::Repeated {
            qubit: QubitIndex::from(1)
        })
    );
    assert_eq!(state, before);
    // A step that passes the integers at its second pair, after it wrote the
    // first, leaves the state as it was: the register holds the greatest
    // coefficient at `|10⟩` alone, and the step squares it.
    let most = amplitude!(i128::MAX, 0, 0, 0; 0);
    let flip = Gate::new([[Amplitude::ZERO, Amplitude::ONE], [
        Amplitude::ONE,
        Amplitude::ZERO,
    ]]);
    let scale = Gate::new([[Amplitude::ONE, Amplitude::ZERO], [Amplitude::ZERO, most]]);
    let square = Gate::new([[most, Amplitude::ZERO], [Amplitude::ZERO, most]]);
    let mut state = State::ground(two).expect("two qubits");
    state
        .apply_one(&flip, QubitIndex::from(0))
        .expect("an exact flip");
    state
        .apply_one(&scale, QubitIndex::from(0))
        .expect("an exact scale");
    let before = state.clone();
    assert_eq!(state.amplitudes(), [
        Amplitude::ZERO,
        Amplitude::ZERO,
        most,
        Amplitude::ZERO
    ]);
    assert_eq!(
        state.apply_one(&square, QubitIndex::from(1)),
        Err(CircuitRefusal::Outside)
    );
    assert_eq!(state, before);
}

proptest! {
    /// Every word of up to 32 gates on one qubit, and of up to 16 steps on two,
    /// multiplies to a unitary matrix.
    #[test]
    fn every_word_of_gates_is_unitary(
        singles in prop::collection::vec(single(), 0 ..= 32),
        steps in prop::collection::vec(step(QubitCount::from(2)), 0 ..= 16),
    ) {
        let mut word = Gate::<2>::identity();
        for gate in singles {
            word = gate.gate().multiply(&word).expect("an exact product");
        }
        prop_assert_eq!(times_adjoint(&word), Gate::identity());
        let mut word = Gate::<4>::identity();
        for each in steps {
            word = matrix(each).multiply(&word).expect("an exact product");
        }
        prop_assert_eq!(times_adjoint(&word), Gate::identity());
    }

    /// A register of two qubits after up to 16 steps holds the first column of
    /// the matrix of its circuit.
    #[test]
    fn a_register_agrees_with_the_matrix_of_its_circuit(steps in prop::collection::vec(step(QubitCount::from(2)), 0 ..= 16)) {
        let mut state = State::ground(QubitCount::from(2))?;
        let mut word = Gate::<4>::identity();
        for each in steps {
            apply(&mut state, each);
            word = matrix(each).multiply(&word).expect("an exact product");
        }
        let column = word
            .act(&[Amplitude::ONE, Amplitude::ZERO, Amplitude::ZERO, Amplitude::ZERO])
            .expect("an exact action");
        prop_assert_eq!(state.amplitudes(), column);
    }

    /// A register of four qubits returns to `|0000⟩` after up to 24 steps and
    /// their adjoints in the reverse order, at every stride.
    #[test]
    fn a_circuit_and_its_inverse_return_the_register(steps in prop::collection::vec(step(QubitCount::from(4)), 0 ..= 24)) {
        let four = QubitCount::from(4);
        let mut state = State::ground(four)?;
        for each in &steps {
            apply(&mut state, *each);
        }
        for each in steps.iter().rev() {
            match *each {
                Step::One(gate, target) => state.apply_one(&gate.gate().adjoint().expect("an exact adjoint"), target)?,
                Step::Two(control, target) => state.apply_two(&Gate::CNOT, control, target)?,
            }
        }
        prop_assert_eq!(state, State::ground(four)?);
    }
}
