//! A numeral annotated `(n : Nat)`, `Nat` the prelude's, is the binary natural
//! it names: `Zero`, or `Positive` over the positive whose digits are the
//! numeral's in binary, the least outermost, as `(0.5 : f64)` is a float.
//!
//! # A constructor term, not an integer
//!
//! The kernel reads a closed native as an opaque constant, so `2 <= 4` at
//! `Integer` is never `true` by conversion, and no function from `Integer`
//! reaches a constructor. A numeral at `Nat` lowers to the constructor term
//! itself, so an order over the naturals is decided by conversion and replayed
//! by the kernel. The rule is read from the numeral's annotation, as `f64`'s
//! is, and `Nat` is the one type it applies to.
//!
//! # The prelude's `Nat`, by position
//!
//! The annotation's name resolves where it is written, so a binder or a
//! source's own declaration named `Nat` shadows the prelude's and the numeral
//! stays an integer. The prelude's constructors are read by name from its top
//! level, as `==` reads its `eq` ([`crate::prelude`]); a unit with no prelude,
//! which only a test lays, has no binary naturals.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ConstructorTag;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Magnitude;
use quenchant_shape::shape::Maybe;

use super::Lowered;
use super::Lowerer;
use super::Resolved;
use super::Sink;
use super::Site;
use crate::error::LoweringRefusal;
use crate::form::Placed;
use crate::module::Container;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;
use crate::unit::SourceIndex;

#[cfg(test)]
mod tests;

quenchant_shape::reason_enum! {
    /// Why a number names no binary natural.
    pub mod numeral {
        /// The number stays the integer, fixed-width or float its lexeme is.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No annotation types the number.
            Unannotated,
            /// The unit lays no prelude, or a prelude without the naturals.
            Unpreluded,
            /// The annotation names a type other than the prelude's `Nat`.
            OtherType,
        }
    }
}

/// A constructor as the mint reads it: its family's admission position and
/// its tag.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Generator
{
    /// The family's admission position.
    family: ConstantIndex,
    /// The constructor's tag.
    tag: ConstructorTag,
}

/// The prelude's binary naturals: `Nat`'s admission position and the five
/// constructors a numeral at `Nat` mints.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each field is the prelude's declaration of its name.
/// - executable: none — positions into a module this record does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one and a numeral of several digits each mint the
///   prelude's constructors.
/// - witness: `lower::natural::tests::a_numeral_at_nat_is_its_binary_constructor_term_3287`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Naturals
{
    /// `Nat`.
    nat: ConstantIndex,
    /// `Zero`.
    zero: Generator,
    /// `Positive`.
    positive: Generator,
    /// `One`.
    one: Generator,
    /// `Bit0`.
    bit0: Generator,
    /// `Bit1`.
    bit1: Generator,
}

/// A binary digit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Digit
{
    /// Zero.
    Zero,
    /// One.
    One,
}

impl<'source> Lowerer<'_, 'source>
{
    /// The prelude's binary naturals, when the number at `site`, read under
    /// `frame`, is annotated by a name that resolves to the prelude's `Nat`.
    ///
    /// # Specification
    /// - requires: `site` is a number read as a value under `frame`.
    /// - ensures: the naturals exactly when an annotation types the number, the
    ///   unit lays a prelude declaring `Nat`, `Pos` and their five
    ///   constructors, and the annotation's name, resolved where it is written,
    ///   is the prelude's `Nat`; otherwise the absence names which of the three
    ///   does not hold.
    /// - fails: propagates the resolution's refusal of the annotation's name.
    /// - panics: none.
    ///
    /// # Errors
    /// The resolution's [`LoweringRefusal`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a numeral at the prelude's `Nat`, at a source's own
    ///   `Nat`, and with no prelude, each asserted as the term it lowers to.
    /// - witness: `lower::natural::tests::a_numeral_at_nat_is_its_binary_constructor_term_3287`
    /// - witness: `lower::natural::tests::a_numeral_at_a_source_s_own_nat_stays_an_integer_3287`
    #[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Present(_))) || self.classifiers.contains_key(&site.at.node))]
    pub(super) fn annotated_natural(
        &mut self,
        site: Site,
        frame: Frame,
    ) -> Result<Maybe<Naturals, numeral::Absent>, LoweringRefusal<'source>>
    {
        let Some(&written) = self.classifiers.get(&site.at.node)
        else {
            return Ok(Maybe::Absent(numeral::Absent::Unannotated));
        };
        let (Some(node), Some(fragment)) = (self.tree.node(written), self.tree.fragment(written))
        else {
            return Ok(Maybe::Absent(numeral::Absent::Unannotated));
        };
        let Some(prelude) = self.collected.unit.prelude()
        else {
            return Ok(Maybe::Absent(numeral::Absent::Unpreluded));
        };
        let Maybe::Present(naturals) = self.naturals(prelude)
        else {
            return Ok(Maybe::Absent(numeral::Absent::Unpreluded));
        };
        let named = Site {
            at: Placed {
                node: written,
                span: node.span(),
            },
            ..site
        };
        match self.resolve_name(named, frame, SurfaceName::from(fragment))? {
            Maybe::Present(Resolved::Declaration { constant, .. }) if constant == naturals.nat => {
                Ok(Maybe::Present(naturals))
            },
            Maybe::Present(_) | Maybe::Absent(_) => Ok(Maybe::Absent(numeral::Absent::OtherType)),
        }
    }

    /// The binary naturals the prelude at `prelude` declares.
    ///
    /// # Specification
    /// - requires: `prelude` is the unit's prelude.
    /// - ensures: `Nat`'s admission position and each of `Zero`, `Positive`,
    ///   `One`, `Bit0` and `Bit1` as the prelude's top level declares them; the
    ///   unpreluded absence when any is missing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::annotated_natural`].
    /// - witness: `lower::natural::tests::a_numeral_at_nat_is_its_binary_constructor_term_3287`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(numeral::Absent::Unpreluded) | Maybe::Present(_)))]
    fn naturals(
        &self,
        prelude: SourceIndex,
    ) -> Maybe<Naturals, numeral::Absent>
    {
        let generator = |name: &'static str| {
            let constructor = self
                .collected
                .constructors
                .get(&(prelude, SurfaceName::from(name)))?;
            let family = self.collected.slots.get(usize::from(constructor.family))?;
            Some(Generator {
                family: family.constant,
                tag: ConstructorTag::from(constructor.tag),
            })
        };
        let nat = self
            .collected
            .by_name
            .get(&(Container::TopLevel(prelude), SurfaceName::from("Nat")))
            .and_then(|&slot| self.collected.slots.get(usize::from(slot)))
            .map(|slot| slot.constant);
        match (
            nat,
            generator("Zero"),
            generator("Positive"),
            generator("One"),
            generator("Bit0"),
            generator("Bit1"),
        ) {
            (Some(nat), Some(zero), Some(positive), Some(one), Some(bit0), Some(bit1))
                if zero.family == nat && positive.family == nat =>
            {
                Maybe::Present(Naturals {
                    nat,
                    zero,
                    positive,
                    one,
                    bit0,
                    bit1,
                })
            },
            _ => Maybe::Absent(numeral::Absent::Unpreluded),
        }
    }
}

/// Mint `magnitude` as the binary natural `naturals` spells into `sink`, each
/// value at `origin` and each family it classifies by inserted there.
///
/// # Specification
/// - requires: `naturals` are the unit's prelude's.
/// - ensures: `Zero` for zero; otherwise `Positive` over `One` wrapped, from
///   the second-highest digit down to the lowest, in `Bit0` for a zero digit
///   and `Bit1` for a one, so the lowest digit is outermost. Every value the
///   term holds records `origin`, and every family its constructors classify by
///   records it as an inserted classifier.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the digits, not recursion.
/// - measure: the digits left.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one, five and two to the thirty-first, each
///   asserted as its constructor term.
/// - witness: `lower::natural::tests::a_numeral_at_nat_is_its_binary_constructor_term_3287`
#[spec(ensures: |ret| matches!(ret, Lowered::Value(_)))]
pub(super) fn mint_natural(
    naturals: Naturals,
    magnitude: &Magnitude,
    sink: &mut Sink<'_>,
    origin: Origin,
) -> Lowered
{
    let digits = binary_digits(magnitude);
    let Some((_, lower)) = digits.split_last()
    else {
        let zero = generated(sink, naturals.zero, Vec::new(), origin);
        return sink.value(zero, origin);
    };
    let mut positive = generated(sink, naturals.one, Vec::new(), origin);
    sink.origins.record_value(positive, origin);
    for &digit in lower.iter().rev() {
        let wrapping = match digit {
            Digit::Zero => naturals.bit0,
            Digit::One => naturals.bit1,
        };
        positive = generated(sink, wrapping, Vec::from([positive]), origin);
        sink.origins.record_value(positive, origin);
    }
    let natural = generated(sink, naturals.positive, Vec::from([positive]), origin);
    sink.value(natural, origin)
}

/// The constructor `generator` over `fields`, minted into `sink`, its family
/// recorded at `origin` as an inserted classifier.
///
/// # Specification
/// trivial.
fn generated(
    sink: &mut Sink<'_>,
    generator: Generator,
    fields: Vec<ValueId>,
    origin: Origin,
) -> ValueId
{
    let classifier = sink.arena.value_type_data(generator.family, Vec::new());
    sink.origins
        .record_value_type(classifier, origin.inserted(Insertion::Classifier));
    sink.arena
        .value_constructor(classifier, generator.tag, fields)
}

/// The binary digits of `magnitude`, the lowest first; none for zero.
///
/// # Specification
/// - requires: `magnitude` is decimal digits, as [`Magnitude`] holds them.
/// - ensures: the digits whose sum of each one's place is `magnitude`, the last
///   a one; empty exactly for zero.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: each pass halves the decimal digits in place, so their value falls
///   by at least half and reaches zero.
/// - measure: the decimal digits' value.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one, five, ten and two to the thirty-first, each
///   asserted digit by digit.
/// - witness: `lower::natural::tests::a_magnitude_s_binary_digits_are_its_halvings_3287`
#[spec(ensures: |ret| ret.last().is_none_or(|&last| last == Digit::One))]
fn binary_digits(magnitude: &Magnitude) -> Vec<Digit>
{
    let mut decimal: Vec<u8> = magnitude
        .as_ref()
        .bytes()
        .map(|byte| byte.saturating_sub(b'0'))
        .collect();
    let mut digits = Vec::new();
    while decimal.iter().any(|&place| place != 0) {
        let mut carried = 0_u8;
        for place in &mut decimal {
            let held = carried.saturating_mul(10).saturating_add(*place);
            *place = held.checked_div(2).unwrap_or_default();
            carried = held.checked_rem(2).unwrap_or_default();
        }
        digits.push(if carried == 0 {
            Digit::Zero
        }
        else {
            Digit::One
        });
    }
    digits
}
