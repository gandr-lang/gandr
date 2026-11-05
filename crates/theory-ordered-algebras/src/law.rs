//! The laws of an ordered semiring, and the checker that decides them on the
//! elements an instance's carrier gives.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::signature::Carrier;
use crate::signature::Comparison;
use crate::signature::InstanceName;
use crate::signature::OrderedSemiring;
use crate::signature::Outside;

/// How many elements a law quantifies over.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Arity
{
    /// One element.
    One,
    /// Two elements.
    Two,
    /// Three elements.
    Three,
}

/// One law of an ordered semiring. Each states an equation or an implication
/// over one, two or three elements.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Law
{
    /// `(a + b) + c = a + (b + c)`.
    AdditionAssociative,
    /// `a + b = b + a`.
    AdditionCommutative,
    /// `0 + a = a`.
    AdditionUnit,
    /// `(a · b) · c = a · (b · c)`.
    MultiplicationAssociative,
    /// `1 · a = a`.
    MultiplicationUnitLeft,
    /// `a · 1 = a`.
    MultiplicationUnitRight,
    /// `a · (b + c) = a · b + a · c`.
    DistributionLeft,
    /// `(a + b) · c = a · c + b · c`.
    DistributionRight,
    /// `0 · a = 0`.
    AnnihilationLeft,
    /// `a · 0 = 0`.
    AnnihilationRight,
    /// `a ≤ a`.
    OrderReflexive,
    /// `a ≤ b` and `b ≤ a` give `a = b`.
    OrderAntisymmetric,
    /// `a ≤ b` and `b ≤ c` give `a ≤ c`.
    OrderTransitive,
    /// `a ≤ b` gives `a + c ≤ b + c`.
    AdditionMonotone,
    /// `a ≤ b` gives `c · a ≤ c · b`.
    MultiplicationMonotoneLeft,
    /// `a ≤ b` gives `a · c ≤ b · c`.
    MultiplicationMonotoneRight,
}

impl Law
{
    /// Every law, in the order a check decides them.
    pub const ALL: [Self; 16] = [
        Self::AdditionAssociative,
        Self::AdditionCommutative,
        Self::AdditionUnit,
        Self::MultiplicationAssociative,
        Self::MultiplicationUnitLeft,
        Self::MultiplicationUnitRight,
        Self::DistributionLeft,
        Self::DistributionRight,
        Self::AnnihilationLeft,
        Self::AnnihilationRight,
        Self::OrderReflexive,
        Self::OrderAntisymmetric,
        Self::OrderTransitive,
        Self::AdditionMonotone,
        Self::MultiplicationMonotoneLeft,
        Self::MultiplicationMonotoneRight,
    ];

    /// How many elements the law quantifies over.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arity(self) -> Arity
    {
        match self {
            Self::AdditionUnit
            | Self::MultiplicationUnitLeft
            | Self::MultiplicationUnitRight
            | Self::AnnihilationLeft
            | Self::AnnihilationRight
            | Self::OrderReflexive => Arity::One,
            Self::AdditionCommutative | Self::OrderAntisymmetric => Arity::Two,
            Self::AdditionAssociative
            | Self::MultiplicationAssociative
            | Self::DistributionLeft
            | Self::DistributionRight
            | Self::OrderTransitive
            | Self::AdditionMonotone
            | Self::MultiplicationMonotoneLeft
            | Self::MultiplicationMonotoneRight => Arity::Three,
        }
    }
}

/// A number of laws.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LawCount(usize);

impl From<LawCount> for usize
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: LawCount) -> Self
    {
        count.0
    }
}

/// A number of tuples of elements a check read.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TupleCount(usize);

impl From<TupleCount> for usize
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: TupleCount) -> Self
    {
        count.0
    }
}

/// Which elements a check read.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Reach
{
    /// Every element of a finite carrier: each law holds.
    Whole,
    /// The generated elements of an infinite carrier: each law holds on them.
    Generated,
}

/// What a check decided: how many laws hold, on how many tuples, over which
/// elements.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Decided
{
    /// The laws that hold.
    laws: LawCount,
    /// The tuples of elements read, summed over the laws.
    tuples: TupleCount,
    /// The elements read.
    reach: Reach,
}

impl Decided
{
    /// The laws that hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn laws(&self) -> LawCount
    {
        self.laws
    }

    /// The tuples of elements read, summed over the laws.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tuples(&self) -> TupleCount
    {
        self.tuples
    }

    /// The elements read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reach(&self) -> Reach
    {
        self.reach
    }
}

/// The elements at which a law was not shown, with the instance and the law.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Counterexample<E>
{
    /// The instance the law was checked on.
    instance: InstanceName,
    /// The law.
    law: Law,
    /// The elements, one per variable of the law, in its order.
    elements: Vec<E>,
}

impl<E> Counterexample<E>
{
    /// The instance the law was checked on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn instance(&self) -> InstanceName
    {
        self.instance
    }

    /// The law.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn law(&self) -> Law
    {
        self.law
    }

    /// The elements, one per variable of the law, in its order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn elements(&self) -> &[E]
    {
        &self.elements
    }
}

/// A law a check could not show.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LawFailure<E>
{
    /// The law fails at the counterexample's elements.
    Broken(Counterexample<E>),
    /// An operation the law reads leaves the represented elements at the
    /// counterexample's elements, so the law is not decided there.
    Undecided(Counterexample<E>),
}

impl<E> fmt::Display for LawFailure<E>
{
    /// Names the instance, the law and how many elements break it. The
    /// counterexample holds the elements.
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
            Self::Broken(ref counterexample) => write!(
                f,
                "{}: {} fails at {} elements",
                counterexample.instance,
                counterexample.law,
                counterexample.elements.len()
            ),
            Self::Undecided(ref counterexample) => write!(
                f,
                "{}: {} leaves the represented elements at {} elements",
                counterexample.instance,
                counterexample.law,
                counterexample.elements.len()
            ),
        }
    }
}

impl<E: fmt::Debug> core::error::Error for LawFailure<E>
{
}

impl fmt::Display for Law
{
    /// Names the law.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::AdditionAssociative => "the associativity of addition",
            Self::AdditionCommutative => "the commutativity of addition",
            Self::AdditionUnit => "the unit of addition",
            Self::MultiplicationAssociative => "the associativity of multiplication",
            Self::MultiplicationUnitLeft => "the unit of multiplication on the left",
            Self::MultiplicationUnitRight => "the unit of multiplication on the right",
            Self::DistributionLeft => "the distribution on the left",
            Self::DistributionRight => "the distribution on the right",
            Self::AnnihilationLeft => "the annihilation by zero on the left",
            Self::AnnihilationRight => "the annihilation by zero on the right",
            Self::OrderReflexive => "the reflexivity of the order",
            Self::OrderAntisymmetric => "the antisymmetry of the order",
            Self::OrderTransitive => "the transitivity of the order",
            Self::AdditionMonotone => "the monotonicity of addition",
            Self::MultiplicationMonotoneLeft => "the monotonicity of multiplication on the left",
            Self::MultiplicationMonotoneRight => "the monotonicity of multiplication on the right",
        })
    }
}

/// Whether a law holds at one tuple.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Truth
{
    /// The law holds.
    Holds,
    /// The law fails.
    Fails,
}

impl From<bool> for Truth
{
    /// `Holds` for true.
    ///
    /// # Specification
    /// trivial.
    fn from(holds: bool) -> Self
    {
        if holds { Self::Holds } else { Self::Fails }
    }
}

/// Decides every law on every tuple of the elements `algebra`'s carrier
/// gives.
///
/// # Specification
/// - ensures: on success, all sixteen laws hold on every tuple the carrier
///   gives; on failure, the first law in [`Law::ALL`] that fails or that leaves
///   the represented elements, at the first tuple in lexicographic order.
/// - panics: none.
/// - intension: a law of arity `k` reads `nᵏ` tuples of `n` elements. No
///   allocation but the counterexample's.
///
/// # Errors
/// - [`LawFailure::Broken`]: a law fails at the counterexample's elements.
/// - [`LawFailure::Undecided`]: an operation leaves the represented elements.
///
/// # Adequacy
/// - hypothesis: L2 — the max-plus, the Lawvere and the Boolean instances pass,
///   and five faults each yield the first law they break with the elements that
///   break it.
/// - witness: `tests::laws::the_max_plus_semiring_passes_every_law`
/// - witness: `tests::laws::the_lawvere_quantale_passes_every_law`
/// - witness: `tests::laws::the_boolean_semiring_passes_every_law_on_its_whole_carrier`
/// - witness: `tests::laws::a_broken_instance_yields_its_counterexample`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |decided| decided.laws.0 == Law::ALL.len()))]
#[inline]
pub fn check<A>(algebra: &A) -> Result<Decided, LawFailure<A::Element>>
where
    A: OrderedSemiring,
{
    let carrier = algebra.carrier();
    let reach = match carrier {
        Carrier::Whole(_) => Reach::Whole,
        Carrier::Generated(_) => Reach::Generated,
    };
    let mut tuples = 0_usize;
    for law in Law::ALL {
        tuples = tuples.saturating_add(check_law(algebra, law)?.0);
    }
    Ok(Decided {
        laws: LawCount(Law::ALL.len()),
        tuples: TupleCount(tuples),
        reach,
    })
}

/// Decides one law on every tuple of the elements `algebra`'s carrier gives.
///
/// # Specification
/// - ensures: on success, the law holds on every tuple, and the count is `nᵏ`
///   for `n` elements and a law of arity `k`.
/// - panics: none.
/// - intension: the tuples in lexicographic order, the first failure returned
///   at once.
///
/// # Errors
/// - [`LawFailure::Broken`]: the law fails at the counterexample's elements.
/// - [`LawFailure::Undecided`]: an operation leaves the represented elements.
///
/// # Adequacy
/// - hypothesis: L2 — each law, on an instance built to break it alone, yields
///   that law and its elements; L3 — the tuple counts of a carrier of three
///   elements separate the arities.
/// - witness: `tests::laws::a_broken_instance_yields_its_counterexample`
/// - witness: `tests::laws::each_law_reads_n_to_its_arity_tuples`
#[spec(ensures: |ref ret| ret.is_ok() || ret.as_ref().is_err_and(|failure| match *failure {
    LawFailure::Broken(ref counterexample) | LawFailure::Undecided(ref counterexample) => counterexample.law == law,
}))]
#[inline]
pub fn check_law<A>(
    algebra: &A,
    law: Law,
) -> Result<TupleCount, LawFailure<A::Element>>
where
    A: OrderedSemiring,
{
    let carrier = algebra.carrier();
    let elements = carrier.elements();
    let mut tuples = 0_usize;
    match law.arity() {
        Arity::One => {
            for first in elements {
                at(algebra, law, [first, first, first])?;
                tuples = tuples.saturating_add(1);
            }
        },
        Arity::Two => {
            for first in elements {
                for second in elements {
                    at(algebra, law, [first, second, second])?;
                    tuples = tuples.saturating_add(1);
                }
            }
        },
        Arity::Three => {
            for first in elements {
                for second in elements {
                    for third in elements {
                        at(algebra, law, [first, second, third])?;
                        tuples = tuples.saturating_add(1);
                    }
                }
            }
        },
    }
    Ok(TupleCount(tuples))
}

/// Decides one law at one tuple, and names the instance, the law and the
/// elements when it is not shown there.
///
/// # Specification
/// - ensures: success exactly when the law holds at the tuple.
/// - panics: none.
///
/// # Errors
/// - [`LawFailure::Broken`]: the law fails at the tuple.
/// - [`LawFailure::Undecided`]: an operation leaves the represented elements.
///
/// # Adequacy
/// - hypothesis: L2 — a broken instance yields the law's own variables, one
///   element each, in the law's order.
/// - witness: `tests::laws::a_broken_instance_yields_its_counterexample`
#[spec(ensures: |ref ret| ret.is_ok() || ret.as_ref().is_err_and(|failure| match *failure {
    LawFailure::Broken(ref counterexample) | LawFailure::Undecided(ref counterexample) => counterexample.law == law,
}))]
fn at<A>(
    algebra: &A,
    law: Law,
    tuple: [&A::Element; 3],
) -> Result<(), LawFailure<A::Element>>
where
    A: OrderedSemiring,
{
    let arity = match law.arity() {
        Arity::One => 1_usize,
        Arity::Two => 2,
        Arity::Three => 3,
    };
    let counterexample = || Counterexample {
        instance: algebra.name(),
        law,
        elements: tuple
            .iter()
            .take(arity)
            .map(|element| (*element).clone())
            .collect(),
    };
    match evaluate(algebra, law, tuple) {
        Ok(Truth::Holds) => Ok(()),
        Ok(Truth::Fails) => Err(LawFailure::Broken(counterexample())),
        Err(Outside) => Err(LawFailure::Undecided(counterexample())),
    }
}

/// Evaluates one law at one tuple. An implication's premise is read first,
/// so a tuple outside the premise reads no operation.
///
/// # Specification
/// - ensures: the reflexivity of the order reads no operation, so it never
///   refuses.
/// - panics: none.
///
/// # Errors
/// - [`Outside`]: an operation the law reads leaves the represented elements.
///
/// # Adequacy
/// - hypothesis: L2 — five faults, in the unit, the product, the order and the
///   representation, separate a wrong operation, a lost premise and a refusal
///   read as a failure.
/// - witness: `tests::laws::a_broken_instance_yields_its_counterexample`
#[spec(ensures: |ref ret| law != Law::OrderReflexive || ret.is_ok())]
fn evaluate<A>(
    algebra: &A,
    law: Law,
    tuple: [&A::Element; 3],
) -> Result<Truth, Outside>
where
    A: OrderedSemiring,
{
    let [a, b, c] = tuple;
    let add = |left: &A::Element, right: &A::Element| algebra.add(left, right);
    let multiply = |left: &A::Element, right: &A::Element| algebra.multiply(left, right);
    let below =
        |lower: &A::Element, upper: &A::Element| algebra.compare(lower, upper) == Comparison::Below;
    let holds = match law {
        Law::AdditionAssociative => add(&add(a, b)?, c)? == add(a, &add(b, c)?)?,
        Law::AdditionCommutative => add(a, b)? == add(b, a)?,
        Law::AdditionUnit => add(&algebra.zero(), a)? == *a,
        Law::MultiplicationAssociative => {
            multiply(&multiply(a, b)?, c)? == multiply(a, &multiply(b, c)?)?
        },
        Law::MultiplicationUnitLeft => multiply(&algebra.one(), a)? == *a,
        Law::MultiplicationUnitRight => multiply(a, &algebra.one())? == *a,
        Law::DistributionLeft => {
            multiply(a, &add(b, c)?)? == add(&multiply(a, b)?, &multiply(a, c)?)?
        },
        Law::DistributionRight => {
            multiply(&add(a, b)?, c)? == add(&multiply(a, c)?, &multiply(b, c)?)?
        },
        Law::AnnihilationLeft => multiply(&algebra.zero(), a)? == algebra.zero(),
        Law::AnnihilationRight => multiply(a, &algebra.zero())? == algebra.zero(),
        Law::OrderReflexive => below(a, a),
        Law::OrderAntisymmetric => !(below(a, b) && below(b, a)) || a == b,
        Law::OrderTransitive => !(below(a, b) && below(b, c)) || below(a, c),
        Law::AdditionMonotone => !below(a, b) || below(&add(a, c)?, &add(b, c)?),
        Law::MultiplicationMonotoneLeft => {
            !below(a, b) || below(&multiply(c, a)?, &multiply(c, b)?)
        },
        Law::MultiplicationMonotoneRight => {
            !below(a, b) || below(&multiply(a, c)?, &multiply(b, c)?)
        },
    };
    Ok(Truth::from(holds))
}
