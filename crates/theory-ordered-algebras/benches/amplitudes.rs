//! The measurement of the exact amplitudes: the sum and the product of random
//! amplitudes, and a circuit of `2^8` random gates on a register of `2^4`
//! qubits.
//!
//! The inputs come from a fixed seed, so each run times the same work.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `add` | one sum of two amplitudes, coefficients below `2^20`, scales below 8 |
//! | `multiply` | one product of two such amplitudes |
//! | `circuit` | `2^8` gates from `H`, `S`, `T` and `CNOT` at random places on 16 qubits, from a fresh register at `\|0…0⟩` |
//!
//! `cargo bench` runs the full measurement and prints one table. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

#[path = "../../theory-exact-reals/benches/support.rs"]
mod support;

use core::hint::black_box;

use gandr_theory_ordered_algebras::Amplitude;
use gandr_theory_ordered_algebras::Coefficient;
use gandr_theory_ordered_algebras::Gate;
use gandr_theory_ordered_algebras::QubitCount;
use gandr_theory_ordered_algebras::QubitIndex;
use gandr_theory_ordered_algebras::Scale;
use gandr_theory_ordered_algebras::State;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// One draw of the generator.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Draw(u64);

impl Draw
{
    /// The draw's remainder below `span`, which is positive.
    ///
    /// # Specification
    /// trivial.
    fn below(
        self,
        span: Self,
    ) -> Self
    {
        Self(self.0.checked_rem(span.0).expect("a positive span"))
    }
}

/// A xorshift generator, so each run reads the same inputs.
#[repr(transparent)]
struct Seed(u64);

impl Seed
{
    /// The next draw.
    ///
    /// # Specification
    /// trivial.
    fn draw(&mut self) -> Draw
    {
        self.0 ^= self.0.wrapping_shl(13);
        self.0 ^= self.0.wrapping_shr(7);
        self.0 ^= self.0.wrapping_shl(17);
        Draw(self.0)
    }

    /// A coefficient from `-2^20` to `2^20`.
    ///
    /// # Specification
    /// trivial.
    fn coefficient(&mut self) -> Coefficient
    {
        let drawn = i128::from(self.draw().below(Draw(1_u64.wrapping_shl(21))).0);
        Coefficient::from(
            drawn
                .checked_sub(1_i128.wrapping_shl(20))
                .expect("a small coefficient"),
        )
    }

    /// An amplitude with four random coefficients and a scale below 8.
    ///
    /// # Specification
    /// trivial.
    fn amplitude(&mut self) -> Amplitude
    {
        let [a, b, c, d] = [(); 4].map(|()| self.coefficient());
        let scale = u32::try_from(self.draw().below(Draw(8)).0).expect("a small scale");
        Amplitude::new(a, b, c, d, Scale::from(scale))
    }

    /// A place below `qubits`.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &mut self,
        qubits: QubitCount,
    ) -> QubitIndex
    {
        let drawn = self.draw().below(Draw(u64::from(u32::from(qubits))));
        QubitIndex::from(u32::try_from(drawn.0).expect("a small place"))
    }
}

/// One step of the measured circuit.
#[derive(Clone, Copy)]
enum Step
{
    /// A gate on one qubit.
    One(&'static Gate<2>, QubitIndex),
    /// `CNOT`, the control first.
    Two(QubitIndex, QubitIndex),
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let (batch, samples, runs) = match output {
        Output::Table => (Count(1024), Count(200), Count(20)),
        Output::Silent => (Count(1), Count(1), Count(1)),
    };
    let mut seed = Seed(0x9e37_79b9_7f4a_7c15);
    let pairs: Vec<(Amplitude, Amplitude)> =
        core::iter::repeat_with(|| (seed.amplitude(), seed.amplitude()))
            .take(1024)
            .collect();
    let qubits = QubitCount::from(16);
    let steps: Vec<Step> = core::iter::repeat_with(|| {
        let target = seed.place(qubits);
        match seed.draw().below(Draw(4)).0 {
            0 => Step::One(&Gate::HADAMARD, target),
            1 => Step::One(&Gate::PHASE, target),
            2 => Step::One(&Gate::T, target),
            _ => {
                let mut control = seed.place(qubits);
                while control == target {
                    control = seed.place(qubits);
                }
                Step::Two(control, target)
            },
        }
    })
    .take(256)
    .collect();
    let mut next = 0_usize;
    let mut pair = || {
        let at = next.checked_rem(pairs.len()).expect("a pair to read");
        next = next.wrapping_add(1);
        pairs.get(at).copied().expect("a pair")
    };
    let add = measure(batch, samples, || {
        let (left, right) = pair();
        black_box(black_box(left).add(&black_box(right))).expect("an exact sum");
    });
    let multiply = measure(batch, samples, || {
        let (left, right) = pair();
        black_box(black_box(left).multiply(&black_box(right))).expect("an exact product");
    });
    let circuit = measure(Count(1), runs, || {
        let mut state = State::ground(qubits).expect("sixteen qubits");
        for step in &steps {
            match *step {
                Step::One(gate, target) => state.apply_one(gate, target),
                Step::Two(control, target) => state.apply_two(&Gate::CNOT, control, target),
            }
            .expect("an exact step");
        }
        black_box(state);
    });
    if matches!(output, Output::Table) {
        println!("An amplitude is {} bytes.", size_of::<Amplitude>());
        println!();
        println!("| Row | Work | p50 ns | p99 ns | Allocations |");
        println!("| --- | ---- | ------ | ------ | ----------- |");
        print_row(format_args!("add | one sum"), &add);
        print_row(format_args!("multiply | one product"), &multiply);
        print_row(format_args!("circuit | 2^8 gates on 2^4 qubits"), &circuit);
    }
}
