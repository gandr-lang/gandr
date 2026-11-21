//! The Clifford+T gates as matrices over exact amplitudes, and the state
//! vector of a register that a circuit of them acts on.
//!
//! A gate on `n` qubits is a square matrix of side `2^n` over
//! [`Amplitude`]. The crate states `H`, `S` and `T` on one qubit and `CNOT`
//! on two, each unitary: `U · U† = I` holds exactly. A state holds one
//! amplitude for each basis state of its register. A gate acts on the qubits
//! it names, and the first qubit is the most significant bit of a basis
//! index.

use alloc::boxed::Box;
use alloc::vec;
use core::fmt;

use anodized::spec;

use crate::amplitude::Amplitude;
use crate::signature::Outside;

/// A square matrix over amplitudes of side `SIDE`: `2` for a gate on one
/// qubit, `4` for a gate on two.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Gate<const SIDE: usize>
{
    /// The rows, each from the first column to the last.
    rows: [[Amplitude; SIDE]; SIDE],
}

impl<const SIDE: usize> Gate<SIDE>
{
    /// The gate whose rows are `rows`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(rows: [[Amplitude; SIDE]; SIDE]) -> Self
    {
        Self { rows }
    }

    /// The rows, each from the first column to the last.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rows(&self) -> &[[Amplitude; SIDE]; SIDE]
    {
        &self.rows
    }

    /// The identity of side `SIDE`.
    ///
    /// # Specification
    /// - ensures: one on the diagonal, zero elsewhere.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each gate times its adjoint compares against it.
    /// - witness: `tests::gates::each_gate_is_unitary`
    #[spec(ensures: |ref ret| ret.rows.iter().enumerate().all(|(row, entries)| entries.iter().enumerate().all(|(column, entry)| if row == column {
        *entry == Amplitude::ONE
    } else {
        *entry == Amplitude::ZERO
    })))]
    #[inline]
    #[must_use]
    pub fn identity() -> Self
    {
        Self {
            rows: core::array::from_fn(|row| {
                core::array::from_fn(|column| {
                    if row == column {
                        Amplitude::ONE
                    }
                    else {
                        Amplitude::ZERO
                    }
                })
            }),
        }
    }

    /// The exact product `self · other`.
    ///
    /// # Specification
    /// - ensures: each entry is the sum over `k` of `self[row][k] ·
    ///   other[k][column]`.
    /// - fails: an amplitude past the 128-bit integers is refused.
    /// - panics: none.
    /// - intension: `SIDE³` products of amplitudes, row by row; no allocation.
    ///
    /// # Errors
    /// - [`Outside`]: an entry, or a partial product or sum of one, lies past
    ///   the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `U · U† = I` for each gate and for random words of
    ///   gates; L3 — `H · H = I`.
    /// - witness: `tests::gates::each_gate_is_unitary`
    /// - witness: `tests::gates::every_word_of_gates_is_unitary`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |product| (*other != Self::identity() || product == self)
        && (*self != Self::identity() || product == other)))]
    #[inline]
    pub fn multiply(
        &self,
        other: &Self,
    ) -> Result<Self, Outside>
    {
        let mut rows = [[Amplitude::ZERO; SIDE]; SIDE];
        for (out, left) in rows.iter_mut().zip(&self.rows) {
            for (entry, right) in left.iter().zip(&other.rows) {
                for (slot, factor) in out.iter_mut().zip(right) {
                    *slot = slot.add(&entry.multiply(factor)?)?;
                }
            }
        }
        Ok(Self { rows })
    }

    /// The adjoint `U†`, the conjugate of the transpose.
    ///
    /// # Specification
    /// - ensures: the entry at `(row, column)` is the conjugate of the entry at
    ///   `(column, row)`.
    /// - fails: an imaginary coefficient that is the least 128-bit integer is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: an entry's conjugate lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `U · U† = I` for each gate, where `S` and `T` are not
    ///   their own adjoints.
    /// - witness: `tests::gates::each_gate_is_unitary`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |adjoint| adjoint.rows.iter().enumerate().all(|(row, entries)| entries.iter().enumerate().all(|(column, entry)| {
        self.rows.get(column).and_then(|source| source.get(row)).map(Amplitude::conjugate) == Some(Ok(*entry))
    }))))]
    #[inline]
    pub fn adjoint(&self) -> Result<Self, Outside>
    {
        let mut rows = [[Amplitude::ZERO; SIDE]; SIDE];
        for (column, row) in self.rows.iter().enumerate() {
            for (out, entry) in rows.iter_mut().zip(row) {
                if let Some(slot) = out.get_mut(column) {
                    *slot = entry.conjugate()?;
                }
            }
        }
        Ok(Self { rows })
    }

    /// The exact action `self · vector` on a vector of side `SIDE`.
    ///
    /// # Specification
    /// - ensures: each component is the sum over `k` of `self[row][k] ·
    ///   vector[k]`.
    /// - fails: an amplitude past the 128-bit integers is refused.
    /// - panics: none.
    /// - intension: `SIDE²` products of amplitudes; no allocation.
    ///
    /// # Errors
    /// - [`Outside`]: a component, or a partial product or sum of one, lies
    ///   past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the state of `H T H` on `|0⟩`; L2 — a state after a
    ///   word of gates against the word's matrix on the first basis vector.
    /// - witness: `tests::amplitudes::the_state_of_h_t_h_on_zero_is_exact`
    /// - witness: `tests::gates::a_register_agrees_with_the_matrix_of_its_circuit`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |out| *self != Self::identity() || out == vector))]
    #[inline]
    pub fn act(
        &self,
        vector: &[Amplitude; SIDE],
    ) -> Result<[Amplitude; SIDE], Outside>
    {
        let mut out = [Amplitude::ZERO; SIDE];
        for (slot, row) in out.iter_mut().zip(&self.rows) {
            for (entry, component) in row.iter().zip(vector) {
                *slot = slot.add(&entry.multiply(component)?)?;
            }
        }
        Ok(out)
    }
}

impl Gate<2>
{
    /// The Hadamard gate `H = (1/√2) [[1, 1], [1, −1]]`.
    pub const HADAMARD: Self = Self {
        rows: [[Amplitude::SQRT_HALF, Amplitude::SQRT_HALF], [
            Amplitude::SQRT_HALF,
            Amplitude::MINUS_SQRT_HALF,
        ]],
    };
    /// The phase gate `S = [[1, 0], [0, i]]`.
    pub const PHASE: Self = Self {
        rows: [[Amplitude::ONE, Amplitude::ZERO], [
            Amplitude::ZERO,
            Amplitude::I,
        ]],
    };
    /// The gate `T = [[1, 0], [0, ω]]`, `ω = e^{iπ/4}`.
    pub const T: Self = Self {
        rows: [[Amplitude::ONE, Amplitude::ZERO], [
            Amplitude::ZERO,
            Amplitude::OMEGA,
        ]],
    };

    /// The tensor product `self ⊗ other`, a gate on two qubits with `self` on
    /// the first.
    ///
    /// # Specification
    /// - ensures: the entry at `(2i + k, 2j + l)` is `self[i][j] ·
    ///   other[k][l]`.
    /// - fails: an amplitude past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a product of entries lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — random words of gates on two qubits are unitary, and
    ///   a register agrees with the matrix of its circuit.
    /// - witness: `tests::gates::every_word_of_gates_is_unitary`
    /// - witness: `tests::gates::a_register_agrees_with_the_matrix_of_its_circuit`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |product| *self != Self::identity() || *other != Self::identity() || *product == Gate::<4>::identity()))]
    #[inline]
    pub fn tensor(
        &self,
        other: &Self,
    ) -> Result<Gate<4>, Outside>
    {
        let mut rows = [[Amplitude::ZERO; 4]; 4];
        for (pair, left) in rows.as_chunks_mut::<2>().0.iter_mut().zip(&self.rows) {
            for (out, right) in pair.iter_mut().zip(&other.rows) {
                for (block, entry) in out.as_chunks_mut::<2>().0.iter_mut().zip(left) {
                    for (slot, factor) in block.iter_mut().zip(right) {
                        *slot = entry.multiply(factor)?;
                    }
                }
            }
        }
        Ok(Gate { rows })
    }
}

impl Gate<4>
{
    /// The controlled not, `CNOT`, with the first qubit the control: it swaps
    /// `|10⟩` and `|11⟩`.
    pub const CNOT: Self = Self {
        rows: [
            [
                Amplitude::ONE,
                Amplitude::ZERO,
                Amplitude::ZERO,
                Amplitude::ZERO,
            ],
            [
                Amplitude::ZERO,
                Amplitude::ONE,
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
        ],
    };
}

/// The number of qubits of a register.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct QubitCount(u32);

impl From<u32> for QubitCount
{
    /// The count `qubits`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(qubits: u32) -> Self
    {
        Self(qubits)
    }
}

impl From<QubitCount> for u32
{
    /// The count's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: QubitCount) -> Self
    {
        count.0
    }
}

/// The place of one qubit in a register, from zero; the first qubit is the
/// most significant bit of a basis index.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct QubitIndex(u32);

impl From<u32> for QubitIndex
{
    /// The place `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<QubitIndex> for u32
{
    /// The place's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: QubitIndex) -> Self
    {
        index.0
    }
}

/// Why a register refuses a step of a circuit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CircuitRefusal
{
    /// The register holds more qubits than a state vector admits.
    Wide
    {
        /// The qubits asked for.
        qubits: QubitCount,
    },
    /// A gate names a qubit that the register does not hold.
    Absent
    {
        /// The qubit named.
        qubit: QubitIndex,
        /// The qubits the register holds.
        qubits: QubitCount,
    },
    /// A gate on two qubits names one qubit twice.
    Repeated
    {
        /// The qubit named twice.
        qubit: QubitIndex,
    },
    /// An amplitude of the result lies past the 128-bit integers.
    Outside,
}

impl From<Outside> for CircuitRefusal
{
    /// An amplitude past the 128-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_outside: Outside) -> Self
    {
        Self::Outside
    }
}

impl fmt::Display for CircuitRefusal
{
    /// Names the refusal and the qubits it reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Wide { qubits } => write!(
                f,
                "a register of {} qubits is wider than the {} a state vector admits",
                qubits.0,
                State::MAX_QUBITS.0
            ),
            Self::Absent { qubit, qubits } => write!(
                f,
                "the gate names qubit {}, but the register holds {} qubits",
                qubit.0, qubits.0
            ),
            Self::Repeated { qubit } => {
                write!(f, "the gate on two qubits names qubit {} twice", qubit.0)
            },
            Self::Outside => f.write_str("an amplitude lies past the 128-bit integers"),
        }
    }
}

impl core::error::Error for CircuitRefusal
{
}

/// The distance between the two basis indices that one qubit's value tells
/// apart: `2` to the number of qubits after it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Stride(usize);

/// The state vector of a register of qubits: one amplitude for each of its
/// `2^n` basis states.
///
/// # Specification
/// - ensures: the vector holds `2^n` amplitudes for `n` qubits, and a refused
///   step leaves it unchanged.
/// - panics: none.
/// - executable: none — a type-level block: the invariants are the
///   constructor's and the steps'.
///
/// # Adequacy
/// - hypothesis: L2 — a register after random gates agrees with the matrix of
///   its circuit on the first basis vector; L3 — a refused step leaves the
///   state as it was.
/// - witness: `tests::gates::a_register_agrees_with_the_matrix_of_its_circuit`
/// - witness: `tests::gates::a_refused_step_leaves_the_state`
#[derive(Clone, Debug)]
pub struct State
{
    /// The qubits of the register.
    qubits: QubitCount,
    /// The amplitudes, in the order of the basis indices.
    amplitudes: Box<[Amplitude]>,
    /// The vector a step writes before it takes the place of `amplitudes`.
    scratch: Box<[Amplitude]>,
}

impl PartialEq for State
{
    /// Two states are equal when their registers and their amplitudes are
    /// equal. The scratch vector holds no part of the state, so the relation
    /// does not read it.
    ///
    /// # Specification
    /// - ensures: equality of the qubit counts and of the amplitudes, in the
    ///   order of the basis indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a register after a circuit and its inverse equals a
    ///   fresh register, whose scratch holds other amplitudes.
    /// - witness: `tests::gates::a_circuit_and_its_inverse_return_the_register`
    #[spec(ensures: |ref ret| !*ret || self.amplitudes.len() == other.amplitudes.len())]
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.qubits == other.qubits && self.amplitudes == other.amplitudes
    }
}

impl Eq for State
{
}

impl State
{
    /// The most qubits a state vector admits: `2^20` amplitudes, twice over
    /// for the step's scratch.
    pub const MAX_QUBITS: QubitCount = QubitCount(20);

    /// The register of `qubits` qubits, each at `|0⟩`.
    ///
    /// # Specification
    /// - ensures: the amplitude of the first basis state is one and every other
    ///   is zero.
    /// - fails: more qubits than [`State::MAX_QUBITS`] are refused.
    /// - panics: none.
    /// - intension: two vectors of `2^n` amplitudes, the only allocation of the
    ///   register.
    ///
    /// # Errors
    /// - [`CircuitRefusal::Wide`]: more qubits than [`State::MAX_QUBITS`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — twenty-one qubits are refused, and a register of one
    ///   qubit starts at `|0⟩`.
    /// - witness: `tests::gates::a_refused_step_leaves_the_state`
    /// - witness: `tests::amplitudes::the_state_of_h_t_h_on_zero_is_exact`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(qubits > Self::MAX_QUBITS, |state| state.qubits == qubits
        && state.amplitudes.first() == Some(&Amplitude::ONE)
        && state.amplitudes.iter().skip(1).all(|amplitude| *amplitude == Amplitude::ZERO)
        && state.scratch.len() == state.amplitudes.len()))]
    #[inline]
    pub fn ground(qubits: QubitCount) -> Result<Self, CircuitRefusal>
    {
        if qubits > Self::MAX_QUBITS {
            return Err(CircuitRefusal::Wide { qubits });
        }
        let length = 1_usize
            .checked_shl(qubits.0)
            .ok_or(CircuitRefusal::Wide { qubits })?;
        let mut amplitudes = vec![Amplitude::ZERO; length].into_boxed_slice();
        if let Some(first) = amplitudes.first_mut() {
            *first = Amplitude::ONE;
        }
        Ok(Self {
            qubits,
            scratch: amplitudes.clone(),
            amplitudes,
        })
    }

    /// The qubits of the register.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn qubits(&self) -> QubitCount
    {
        self.qubits
    }

    /// The amplitudes, in the order of the basis indices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn amplitudes(&self) -> &[Amplitude]
    {
        &self.amplitudes
    }

    /// The stride of `qubit`: `2` to the number of qubits after it.
    ///
    /// # Specification
    /// - ensures: `2^(n − 1 − qubit)` for `n` qubits.
    /// - fails: a qubit the register does not hold is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CircuitRefusal::Absent`]: the register does not hold `qubit`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the qubit one past the last is refused.
    /// - witness: `tests::gates::a_refused_step_leaves_the_state`
    #[spec(ensures: |ref ret| ret.is_ok() == (qubit.0 < self.qubits.0))]
    fn stride(
        &self,
        qubit: QubitIndex,
    ) -> Result<Stride, CircuitRefusal>
    {
        let absent = CircuitRefusal::Absent {
            qubit,
            qubits: self.qubits,
        };
        let after = self
            .qubits
            .0
            .checked_sub(qubit.0)
            .and_then(|rest| rest.checked_sub(1))
            .ok_or(absent)?;
        1_usize.checked_shl(after).map(Stride).ok_or(absent)
    }

    /// Applies a gate on one qubit to `target`.
    ///
    /// # Specification
    /// - ensures: each pair of basis states that differ in `target` alone takes
    ///   the gate's action, and the state is replaced at once.
    /// - fails: a qubit the register does not hold, or an amplitude past the
    ///   128-bit integers, is refused, and the state stays as it was.
    /// - panics: none.
    /// - intension: `2^(n−1)` actions of a 2 × 2 matrix; no allocation.
    ///
    /// # Errors
    /// - [`CircuitRefusal::Absent`]: the register does not hold `target`.
    /// - [`CircuitRefusal::Outside`]: an amplitude lies past the 128-bit
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the state of `H T H` on `|0⟩`; L2 — a register after
    ///   random gates against the matrix of its circuit.
    /// - witness: `tests::amplitudes::the_state_of_h_t_h_on_zero_is_exact`
    /// - witness: `tests::gates::a_register_agrees_with_the_matrix_of_its_circuit`
    /// - witness: `tests::gates::a_refused_step_leaves_the_state`
    #[spec(ensures: |ref ret| self.scratch.len() == self.amplitudes.len() && ret.as_ref().err().is_none_or(|refusal| match *refusal {
        CircuitRefusal::Absent { qubit, .. } => qubit == target && target.0 >= self.qubits.0,
        CircuitRefusal::Outside => target.0 < self.qubits.0,
        CircuitRefusal::Wide { .. } | CircuitRefusal::Repeated { .. } => false,
    }))]
    #[inline]
    pub fn apply_one(
        &mut self,
        gate: &Gate<2>,
        target: QubitIndex,
    ) -> Result<(), CircuitRefusal>
    {
        let Stride(stride) = self.stride(target)?;
        let block = stride.checked_mul(2).ok_or(CircuitRefusal::Outside)?;
        for (input, output) in self
            .amplitudes
            .chunks_exact(block)
            .zip(self.scratch.chunks_exact_mut(block))
        {
            let (low, high) = input.split_at(stride);
            let (low_out, high_out) = output.split_at_mut(stride);
            for (((low, high), low_out), high_out) in
                low.iter().zip(high).zip(low_out).zip(high_out)
            {
                let [low_next, high_next] = gate.act(&[*low, *high])?;
                *low_out = low_next;
                *high_out = high_next;
            }
        }
        core::mem::swap(&mut self.amplitudes, &mut self.scratch);
        Ok(())
    }

    /// Applies a gate on two qubits to `first` and `second`, `first` the gate's
    /// first qubit.
    ///
    /// # Specification
    /// - ensures: each four basis states that differ in `first` and `second`
    ///   alone take the gate's action, in the order `|00⟩`, `|01⟩`, `|10⟩`,
    ///   `|11⟩` of the two, and the state is replaced at once.
    /// - fails: a qubit the register does not hold, one qubit named twice, or
    ///   an amplitude past the 128-bit integers, is refused, and the state
    ///   stays as it was.
    /// - panics: none.
    /// - intension: `2^(n−2)` actions of a 4 × 4 matrix; no allocation.
    ///
    /// # Errors
    /// - [`CircuitRefusal::Absent`]: the register does not hold a qubit named.
    /// - [`CircuitRefusal::Repeated`]: `first` and `second` are one qubit.
    /// - [`CircuitRefusal::Outside`]: an amplitude lies past the 128-bit
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a register after random gates, `CNOT` on both orders
    ///   of its qubits, against the matrix of its circuit; L3 — one qubit named
    ///   twice.
    /// - witness: `tests::gates::a_register_agrees_with_the_matrix_of_its_circuit`
    /// - witness: `tests::gates::a_refused_step_leaves_the_state`
    #[spec(ensures: |ref ret| self.scratch.len() == self.amplitudes.len() && ret.as_ref().err().is_none_or(|refusal| match *refusal {
        CircuitRefusal::Absent { qubit, .. } => (qubit == first || qubit == second) && qubit.0 >= self.qubits.0,
        CircuitRefusal::Repeated { qubit } => qubit == first && first == second,
        CircuitRefusal::Outside => first != second && first.0 < self.qubits.0 && second.0 < self.qubits.0,
        CircuitRefusal::Wide { .. } => false,
    }))]
    #[inline]
    pub fn apply_two(
        &mut self,
        gate: &Gate<4>,
        first: QubitIndex,
        second: QubitIndex,
    ) -> Result<(), CircuitRefusal>
    {
        let first_stride = self.stride(first)?;
        let second_stride = self.stride(second)?;
        if first == second {
            return Err(CircuitRefusal::Repeated { qubit: first });
        }
        let first_high = first_stride > second_stride;
        let (Stride(high), Stride(low)) = if first_high {
            (first_stride, second_stride)
        }
        else {
            (second_stride, first_stride)
        };
        let outer = high.checked_mul(2).ok_or(CircuitRefusal::Outside)?;
        let inner = low.checked_mul(2).ok_or(CircuitRefusal::Outside)?;
        for (input, output) in self
            .amplitudes
            .chunks_exact(outer)
            .zip(self.scratch.chunks_exact_mut(outer))
        {
            let (clear, set) = input.split_at(high);
            let (clear_out, set_out) = output.split_at_mut(high);
            let blocks = clear
                .chunks_exact(inner)
                .zip(set.chunks_exact(inner))
                .zip(clear_out.chunks_exact_mut(inner))
                .zip(set_out.chunks_exact_mut(inner));
            for (((clear, set), clear_out), set_out) in blocks {
                let (x00, x01) = clear.split_at(low);
                let (x10, x11) = set.split_at(low);
                let (y00, y01) = clear_out.split_at_mut(low);
                let (y10, y11) = set_out.split_at_mut(low);
                let entries = x00
                    .iter()
                    .zip(x01)
                    .zip(x10)
                    .zip(x11)
                    .zip(y00.iter_mut().zip(y01).zip(y10).zip(y11));
                for ((((a00, a01), a10), a11), (((b00, b01), b10), b11)) in entries {
                    // `aHL`: the high qubit's bit, then the low qubit's.
                    if first_high {
                        let [c00, c01, c10, c11] = gate.act(&[*a00, *a01, *a10, *a11])?;
                        *b00 = c00;
                        *b01 = c01;
                        *b10 = c10;
                        *b11 = c11;
                    }
                    else {
                        let [c00, c01, c10, c11] = gate.act(&[*a00, *a10, *a01, *a11])?;
                        *b00 = c00;
                        *b10 = c01;
                        *b01 = c10;
                        *b11 = c11;
                    }
                }
            }
        }
        core::mem::swap(&mut self.amplitudes, &mut self.scratch);
        Ok(())
    }
}
