//! The canonical serialization of a plan, of a certificate and of a
//! checkpoint.
//!
//! A plan crosses a process boundary as bytes, and a later stage keys a
//! cache and a certificate by them. So the bytes of a plan are canonical: two
//! plans of equal structure give equal bytes, and the bytes read back to an
//! equal plan. The writer reads a [`Plan`] in its canonical form and writes
//! each node once, in the plan's order. A child is the position of a node
//! before it. The reader refuses each malformed input by name, and it refuses
//! bytes that decode but differ from the canonical bytes of what they hold.
//! The root is the last node, and its sort says whether the plan encloses a
//! real or decides an open proposition. A [`Certificate`] has canonical bytes
//! of the same convention, its steps in order. So does a checkpoint of the
//! refinement machine: its live obligations with the steps of their
//! certificates.
//!
//! # Boundaries
//!
//! The layout follows the tree's convention for canonical bytes: a one-byte
//! kind before each record, every integer little-endian at a fixed width, a
//! byte payload after its length as a `u64`, and no unknown kind admitted.
//! The reader allocates no more than the bytes hold, whatever count or
//! length they state.
//!
//! | Field | Bytes |
//! | ----- | ----- |
//! | magic | `GXRP` |
//! | version | `u16`, now 1 |
//! | node count | `u64`, at least one |
//! | each node | its kind, then its fields in declaration order |
//!
//! | Field kind | Bytes |
//! | ---------- | ----- |
//! | a child, a de Bruijn index, a power, an evidence reference | `u32` |
//! | an evidence slot | `0x00`, or `0x01` and the reference |
//! | a dyadic | the exponent as `i32`, the mantissa's length as `u64`, then the mantissa as the shortest two's complement, least significant byte first, and no bytes for zero |
//! | an interval | the orientation byte, then the lower and the upper bound |
//! | a bound | the endpoint byte, the dyadic of a finite endpoint, then the closure byte |
//!
//! | Kind | Byte | Kind | Byte | Kind | Byte |
//! | ---- | ---- | ---- | ---- | ---- | ---- |
//! | bound variable | `0x01` | top | `0x10` | interval domain | `0x20` |
//! | constant | `0x02` | bottom | `0x11` | product domain | `0x21` |
//! | sum | `0x03` | less | `0x12` | subdomain | `0x22` |
//! | difference | `0x04` | meet | `0x13` | | |
//! | product | `0x05` | join | `0x14` | | |
//! | quotient | `0x06` | exists | `0x15` | | |
//! | power | `0x07` | forall | `0x16` | | |
//! | cut | `0x08` | | | | |
//!
//! A certificate's layout stands on [`Certificate::encode`], and a
//! checkpoint's on [`crate::dovetail::Dovetail::checkpoint`].

use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;

use anodized::spec;
use num_bigint::BigInt;

use crate::certificate::Certificate;
use crate::certificate::CheckerQuotas;
use crate::certificate::FormatVersion;
use crate::certificate::Side;
use crate::certificate::Step;
use crate::certificate::StepCount;
use crate::certificate::StepId;
use crate::dovetail::Position;
use crate::dovetail::Quantum;
use crate::dovetail::Steps;
use crate::dyadic::BitWidth;
use crate::dyadic::Dyadic;
use crate::dyadic::DyadicError;
use crate::dyadic::Exponent;
use crate::dyadic::InlineMantissa;
use crate::dyadic::MantissaView;
use crate::interval::Bound;
use crate::interval::Closure;
use crate::interval::Endpoint;
use crate::interval::IntervalError;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Cut;
use crate::plan::DeBruijn;
use crate::plan::Domain;
use crate::plan::DomainId;
use crate::plan::Evidence;
use crate::plan::EvidenceSlot;
use crate::plan::Node;
use crate::plan::NodeCount;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::OpenId;
use crate::plan::Plan;
use crate::plan::PlanBuilder;
use crate::plan::PlanError;
use crate::plan::Power;
use crate::plan::Quantifier;
use crate::plan::Real;
use crate::plan::RealId;
use crate::plan::Root;
use crate::plan::Site;
use crate::plan::Sort;
use crate::semidecision::Demand;

/// The four bytes that open an encoded plan.
const MAGIC: [u8; 4] = *b"GXRP";

/// The layout version that this build writes and reads.
const VERSION: u16 = 1;

/// The four bytes that open an encoded certificate.
const CERTIFICATE_MAGIC: [u8; 4] = *b"GXRC";

/// The kind byte of each certificate step.
mod step_kind
{
    use super::Kind;

    /// A witnesses step.
    pub(super) const WITNESSES: Kind = Kind(0x30);
    /// A split step.
    pub(super) const SPLIT: Kind = Kind(0x31);
    /// A constant step.
    pub(super) const CONSTANT: Kind = Kind(0x32);
    /// A below step.
    pub(super) const BELOW: Kind = Kind(0x33);
    /// A not-below step.
    pub(super) const NOT_BELOW: Kind = Kind(0x34);
    /// A variable step.
    pub(super) const VARIABLE: Kind = Kind(0x35);
    /// A sum step.
    pub(super) const SUM: Kind = Kind(0x36);
    /// A difference step.
    pub(super) const DIFFERENCE: Kind = Kind(0x37);
    /// A product step.
    pub(super) const PRODUCT: Kind = Kind(0x38);
    /// A witness step.
    pub(super) const WITNESS: Kind = Kind(0x39);
    /// A cover step.
    pub(super) const COVER: Kind = Kind(0x3a);
    /// A counterexample step.
    pub(super) const COUNTEREXAMPLE: Kind = Kind(0x3b);
    /// A refutation step.
    pub(super) const REFUTATION: Kind = Kind(0x3c);
}

/// A one-byte kind: of a node, or of an interval's orientation, endpoint or
/// closure, or of an evidence slot.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Kind(u8);

impl Kind
{
    /// The bottom proposition.
    const BOTTOM: Self = Self(0x11);
    /// A bound variable.
    const BOUND: Self = Self(0x01);
    /// A dyadic constant.
    const CONSTANT: Self = Self(0x02);
    /// A cut.
    const CUT: Self = Self(0x08);
    /// A quotient.
    const DIV: Self = Self(0x06);
    /// A bounded existential.
    const EXISTS: Self = Self(0x15);
    /// A bounded universal.
    const FORALL: Self = Self(0x16);
    /// An interval domain.
    const INTERVAL: Self = Self(0x20);
    /// A finite join.
    const JOIN: Self = Self(0x14);
    /// A strict comparison.
    const LESS: Self = Self(0x12);
    /// A finite meet.
    const MEET: Self = Self(0x13);
    /// A product of reals.
    const MUL: Self = Self(0x05);
    /// A natural power.
    const POWER: Self = Self(0x07);
    /// A product domain.
    const PRODUCT: Self = Self(0x21);
    /// A difference.
    const SUB: Self = Self(0x04);
    /// A subdomain.
    const SUBDOMAIN: Self = Self(0x22);
    /// A sum.
    const SUM: Self = Self(0x03);
    /// The top proposition.
    const TOP: Self = Self(0x10);
}

/// The byte of a proper interval, a negative infinity, a closed bound or an
/// absent evidence slot.
const FIRST: Kind = Kind(0x00);
/// The byte of a dual interval, a finite endpoint, an open bound or a given
/// evidence slot.
const SECOND: Kind = Kind(0x01);
/// The byte of a positive infinity.
const THIRD: Kind = Kind(0x02);

/// A fixed-width word: a child, a de Bruijn index, a power or an evidence
/// reference.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Word(u32);

/// A count of bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ByteCount(usize);

/// The canonical bytes of a plan.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PlanBytes(Vec<u8>);

impl AsRef<[u8]> for PlanBytes
{
    /// Borrow the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return &self.0;
    }
}

impl From<PlanBytes> for Vec<u8>
{
    /// Take the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: PlanBytes) -> Self
    {
        return bytes.0;
    }
}

/// Bytes that claim to be an encoded plan, not yet read.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EncodedPlan<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for EncodedPlan<'bytes>
{
    /// Read a byte slice as an encoded plan.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        return Self(bytes);
    }
}

impl AsRef<[u8]> for EncodedPlan<'_>
{
    /// Borrow the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return self.0;
    }
}

impl<'bytes> From<&'bytes PlanBytes> for EncodedPlan<'bytes>
{
    /// Read a plan's own bytes as an encoded plan.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes PlanBytes) -> Self
    {
        return Self(&bytes.0);
    }
}

/// A failed decoding: the bytes are malformed, or they are not canonical.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DecodeError
{
    /// The bytes do not open with the magic of their layout.
    Magic,
    /// The bytes name a layout version that this build does not read.
    Version,
    /// The bytes end inside a field.
    Truncated,
    /// A one-byte kind names no kind that its place admits.
    UnknownKind,
    /// A node names a node at or after its own position.
    ForwardReference,
    /// A node names a node of another sort than its slot takes.
    WrongSort,
    /// The bytes hold no node, or no step.
    Empty,
    /// The last node, the root, is a domain.
    DomainRoot,
    /// Bytes follow the last node, or the last step.
    TrailingBytes,
    /// The count of nodes exceeds what a position counts.
    TooManyNodes,
    /// A constant's exponent leaves its range.
    Dyadic(DyadicError),
    /// An interval is malformed.
    Interval(IntervalError),
    /// The bytes decode, but they differ from the canonical bytes of the plan
    /// or the certificate that they hold.
    NotCanonical,
}

impl From<PlanError> for DecodeError
{
    /// The decoding failure that a failed plan operation stands for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: PlanError) -> Self
    {
        return match error {
            PlanError::UnknownNode => Self::ForwardReference,
            PlanError::WrongSort => Self::WrongSort,
            PlanError::TooManyNodes => Self::TooManyNodes,
        };
    }
}

impl fmt::Display for DecodeError
{
    /// Write the failure as one line.
    ///
    /// # Specification
    /// - ensures: writes one fixed phrase per variant, no two alike, and the
    ///   wrapped failure's own line after the phrase of a wrapping variant.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::plan::failures_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match *self {
            Self::Magic => f.write_str("the bytes do not open with the magic of their layout"),
            Self::Version => {
                f.write_str("the bytes name a layout version this build does not read")
            },
            Self::Truncated => f.write_str("the bytes end inside a field"),
            Self::UnknownKind => f.write_str("a kind byte names no kind that its place admits"),
            Self::ForwardReference => {
                f.write_str("a node names a node at or after its own position")
            },
            Self::WrongSort => {
                f.write_str("a node names a node of another sort than its slot takes")
            },
            Self::Empty => f.write_str("the bytes hold no node or no step"),
            Self::DomainRoot => f.write_str("the root is a domain"),
            Self::TrailingBytes => f.write_str("bytes follow the last record"),
            Self::TooManyNodes => f.write_str("the count of nodes exceeds what a position counts"),
            Self::Dyadic(error) => write!(f, "a constant is malformed: {error}"),
            Self::Interval(error) => write!(f, "an interval is malformed: {error}"),
            Self::NotCanonical => {
                f.write_str("the bytes are not the canonical bytes of what they hold")
            },
        };
    }
}

impl core::error::Error for DecodeError
{
}

/// The bytes of one node, or of a whole plan: the writer, and the key under
/// which the canonical walk finds a node of equal structure.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct Entry
{
    /// The bytes written.
    bytes: Vec<u8>,
}

impl Entry
{
    /// Forget the bytes and keep the storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn clear(&mut self)
    {
        self.bytes.clear();
    }

    /// Write a kind byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn kind(
        &mut self,
        kind: Kind,
    )
    {
        self.bytes.push(kind.0);
    }

    /// Write a word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn word(
        &mut self,
        word: Word,
    )
    {
        self.bytes.extend_from_slice(&word.0.to_le_bytes());
    }

    /// Write a byte count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn count(
        &mut self,
        count: ByteCount,
    )
    {
        // A count of bytes in memory fits 64 bits on every target.
        let wide = u64::try_from(count.0).unwrap_or(u64::MAX);
        self.bytes.extend_from_slice(&wide.to_le_bytes());
    }

    /// Write a child.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn child(
        &mut self,
        id: NodeId,
    )
    {
        self.word(Word(u32::from(id)));
    }

    /// Write an evidence reference.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn evidence(
        &mut self,
        evidence: Evidence,
    )
    {
        self.word(Word(u32::from(evidence)));
    }

    /// Write an evidence slot.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn slot(
        &mut self,
        slot: EvidenceSlot,
    )
    {
        match slot {
            EvidenceSlot::Absent => self.kind(FIRST),
            EvidenceSlot::Given(evidence) => {
                self.kind(SECOND);
                self.evidence(evidence);
            },
        }
    }

    /// Write a dyadic: its exponent, then its mantissa as the shortest two's
    /// complement after its length.
    ///
    /// # Specification
    /// - ensures: appends the exponent as four bytes, then the mantissa's
    ///   length as eight bytes, then the mantissa's shortest two's complement,
    ///   least significant byte first; zero has no mantissa bytes.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every generated constant reads back, inline and
    ///   carried, at both signs and beside each byte boundary; L3 — a padded
    ///   mantissa is refused as not canonical.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
    fn dyadic(
        &mut self,
        value: &Dyadic,
    )
    {
        self.bytes
            .extend_from_slice(&i32::from(value.exponent()).to_le_bytes());
        match value.mantissa_view() {
            MantissaView::Small(mantissa) => {
                let bytes = mantissa.to_le_bytes();
                // Drop each top byte that only repeats the sign of the byte
                // below it; zero keeps no byte at all.
                let mut used = if mantissa == 0 { 0 } else { bytes.len() };
                while let (Some(top), Some(below)) = (used.checked_sub(1), used.checked_sub(2)) {
                    let (Some(&high), Some(&next)) = (bytes.get(top), bytes.get(below))
                    else {
                        break;
                    };
                    let repeats = (high == 0x00 && (next & 0x80) == 0)
                        || (high == 0xFF && (next & 0x80) != 0);
                    if !repeats {
                        break;
                    }
                    used = top;
                }
                self.count(ByteCount(used));
                self.bytes
                    .extend_from_slice(bytes.get(.. used).unwrap_or_default());
            },
            MantissaView::Large(mantissa) => {
                let bytes = mantissa.to_signed_bytes_le();
                self.count(ByteCount(bytes.len()));
                self.bytes.extend_from_slice(&bytes);
            },
        }
    }

    /// Write a bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn bound(
        &mut self,
        bound: &Bound,
    )
    {
        match bound.endpoint {
            Endpoint::NegInf => self.kind(FIRST),
            Endpoint::Finite(ref value) => {
                self.kind(SECOND);
                self.dyadic(value);
            },
            Endpoint::PosInf => self.kind(THIRD),
        }
        self.kind(match bound.closure {
            Closure::Closed => FIRST,
            Closure::Open => SECOND,
        });
    }

    /// Write an interval.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn interval(
        &mut self,
        interval: &NumericInterval,
    )
    {
        self.kind(match interval.orientation() {
            Orientation::Proper => FIRST,
            Orientation::Dual => SECOND,
        });
        self.bound(interval.lower());
        self.bound(interval.upper());
    }

    /// Write a quantifier's fields.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn quantifier(
        &mut self,
        quantifier: Quantifier,
    )
    {
        self.child(quantifier.domain.node());
        self.child(quantifier.body.node());
        self.evidence(quantifier.evidence);
        self.slot(quantifier.dual);
    }

    /// Write one node: its kind, then its fields in declaration order.
    ///
    /// # Specification
    /// - ensures: appends the node's kind byte, then each field in declaration
    ///   order in the layout of the module table.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every node kind of generated plans reads back equal;
    ///   L3 — the cut of the square root of two has a fixed byte count.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::the_square_root_of_two_is_a_small_cut`
    pub(crate) fn node(
        &mut self,
        node: &Node,
    )
    {
        let pair = |entry: &mut Self, kind: Kind, left: NodeId, right: NodeId| {
            entry.kind(kind);
            entry.child(left);
            entry.child(right);
        };
        match *node {
            Node::Real(ref real) => match *real {
                Real::Bound(index) => {
                    self.kind(Kind::BOUND);
                    self.word(Word(u32::from(index)));
                },
                Real::Constant(ref value) => {
                    self.kind(Kind::CONSTANT);
                    self.dyadic(value);
                },
                Real::Add(left, right) => pair(self, Kind::SUM, left.node(), right.node()),
                Real::Sub(left, right) => pair(self, Kind::SUB, left.node(), right.node()),
                Real::Mul(left, right) => pair(self, Kind::MUL, left.node(), right.node()),
                Real::Div {
                    numerator,
                    denominator,
                    nonzero,
                } => {
                    pair(self, Kind::DIV, numerator.node(), denominator.node());
                    self.evidence(nonzero);
                },
                Real::Power(base, power) => {
                    self.kind(Kind::POWER);
                    self.child(base.node());
                    self.word(Word(u32::from(power)));
                },
                Real::Cut(ref cut) => {
                    self.kind(Kind::CUT);
                    self.interval(&cut.hull);
                    self.child(cut.lower.node());
                    self.child(cut.upper.node());
                    self.evidence(cut.laws);
                },
            },
            Node::Open(ref open) => match *open {
                Open::Top => self.kind(Kind::TOP),
                Open::Bottom => self.kind(Kind::BOTTOM),
                Open::Less(left, right) => pair(self, Kind::LESS, left.node(), right.node()),
                Open::Meet(left, right) => pair(self, Kind::MEET, left.node(), right.node()),
                Open::Join(left, right) => pair(self, Kind::JOIN, left.node(), right.node()),
                Open::Exists(quantifier) => {
                    self.kind(Kind::EXISTS);
                    self.quantifier(quantifier);
                },
                Open::Forall(quantifier) => {
                    self.kind(Kind::FORALL);
                    self.quantifier(quantifier);
                },
            },
            Node::Domain(ref domain) => match *domain {
                Domain::Interval {
                    ref hull,
                    overt,
                    compact,
                } => {
                    self.kind(Kind::INTERVAL);
                    self.interval(hull);
                    self.slot(overt);
                    self.slot(compact);
                },
                Domain::Product {
                    left,
                    right,
                    evidence,
                } => {
                    pair(self, Kind::PRODUCT, left.node(), right.node());
                    self.evidence(evidence);
                },
                Domain::Subdomain {
                    parent,
                    classifier,
                    evidence,
                } => {
                    pair(self, Kind::SUBDOMAIN, parent.node(), classifier.node());
                    self.evidence(evidence);
                },
            },
        }
    }
}

/// A reader over the bytes not yet read.
#[repr(transparent)]
struct Reader<'bytes>
{
    /// The bytes after the last field read.
    rest: &'bytes [u8],
}

/// Bytes that the reader took.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Taken<'bytes>(&'bytes [u8]);

impl<'bytes> Reader<'bytes>
{
    /// Take the next `count` bytes.
    ///
    /// # Specification
    /// - ensures: returns the next `count` bytes and moves past them.
    /// - fails: returns [`DecodeError::Truncated`], the reader unchanged, when
    ///   fewer bytes remain.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DecodeError::Truncated`]: fewer than `count` bytes remain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every prefix of a valid encoding is refused as
    ///   truncated or as a later refusal, never read past its end.
    /// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
    #[spec(
        captures: before = self.rest.len(),
        ensures: |ref result| match *result {
            Ok(taken) => taken.0.len() == count.0 && self.rest.len() == before.saturating_sub(count.0),
            Err(_) => self.rest.len() == before,
        }
    )]
    fn take(
        &mut self,
        count: ByteCount,
    ) -> Result<Taken<'bytes>, DecodeError>
    {
        let (taken, rest) = self
            .rest
            .split_at_checked(count.0)
            .ok_or(DecodeError::Truncated)?;
        self.rest = rest;
        return Ok(Taken(taken));
    }

    /// Read a kind byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn kind(&mut self) -> Result<Kind, DecodeError>
    {
        let (&kind, rest) = self.rest.split_first().ok_or(DecodeError::Truncated)?;
        self.rest = rest;
        return Ok(Kind(kind));
    }

    /// Read a word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn word(&mut self) -> Result<Word, DecodeError>
    {
        let (&word, rest) = self
            .rest
            .split_first_chunk::<4>()
            .ok_or(DecodeError::Truncated)?;
        self.rest = rest;
        return Ok(Word(u32::from_le_bytes(word)));
    }

    /// Read a byte count, which must not exceed the bytes that remain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn count(&mut self) -> Result<ByteCount, DecodeError>
    {
        let (&count, rest) = self
            .rest
            .split_first_chunk::<8>()
            .ok_or(DecodeError::Truncated)?;
        self.rest = rest;
        let count =
            usize::try_from(u64::from_le_bytes(count)).map_err(|_wide| DecodeError::Truncated)?;
        return Ok(ByteCount(count));
    }

    /// Read a dyadic.
    ///
    /// # Specification
    /// - ensures: reads the exponent and the mantissa that the writer's layout
    ///   gives, and returns their canonical dyadic.
    /// - fails: returns [`DecodeError::Truncated`] when the bytes end inside
    ///   the dyadic, and [`DecodeError::Dyadic`] when its canonical exponent
    ///   leaves its range.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Errors
    /// - [`DecodeError::Truncated`]: the bytes end inside the dyadic.
    /// - [`DecodeError::Dyadic`]: the canonical exponent leaves its range.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every generated constant reads back; L3 — a mantissa
    ///   longer than the bytes left is truncated.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
    fn dyadic(&mut self) -> Result<Dyadic, DecodeError>
    {
        let (&exponent, rest) = self
            .rest
            .split_first_chunk::<4>()
            .ok_or(DecodeError::Truncated)?;
        self.rest = rest;
        let exponent = Exponent::from(i32::from_le_bytes(exponent));
        let length = self.count()?;
        let Taken(bytes) = self.take(length)?;
        let value = if let Some(&top) = bytes.last()
            && bytes.len() <= 8
        {
            // Sign-extend the shortest two's complement to eight bytes.
            let mut wide = if top & 0x80 == 0 {
                [0x00; 8]
            }
            else {
                [0xFF; 8]
            };
            for (slot, &byte) in wide.iter_mut().zip(bytes) {
                *slot = byte;
            }
            Dyadic::from_inline(InlineMantissa::from(i64::from_le_bytes(wide)), exponent)
        }
        else if bytes.is_empty() {
            Dyadic::from_inline(InlineMantissa::from(0), exponent)
        }
        else {
            Dyadic::new(BigInt::from_signed_bytes_le(bytes), exponent)
        };
        return value.map_err(DecodeError::Dyadic);
    }

    /// Read a bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn bound(&mut self) -> Result<Bound, DecodeError>
    {
        let endpoint = match self.kind()? {
            FIRST => Endpoint::NegInf,
            SECOND => Endpoint::Finite(self.dyadic()?),
            THIRD => Endpoint::PosInf,
            Kind(_) => return Err(DecodeError::UnknownKind),
        };
        let closure = match self.kind()? {
            FIRST => Closure::Closed,
            SECOND => Closure::Open,
            Kind(_) => return Err(DecodeError::UnknownKind),
        };
        return Ok(Bound::new(endpoint, closure));
    }

    /// Read an interval, refusing a malformed one by name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn interval(&mut self) -> Result<NumericInterval, DecodeError>
    {
        let orientation = match self.kind()? {
            FIRST => Orientation::Proper,
            SECOND => Orientation::Dual,
            Kind(_) => return Err(DecodeError::UnknownKind),
        };
        let lower = self.bound()?;
        let upper = self.bound()?;
        return NumericInterval::new(lower, upper, orientation).map_err(DecodeError::Interval);
    }

    /// Read an evidence reference.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn evidence(&mut self) -> Result<Evidence, DecodeError>
    {
        return self.word().map(|word| Evidence::from(word.0));
    }

    /// Read an evidence slot.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn slot(&mut self) -> Result<EvidenceSlot, DecodeError>
    {
        return match self.kind()? {
            FIRST => Ok(EvidenceSlot::Absent),
            SECOND => self.evidence().map(EvidenceSlot::Given),
            Kind(_) => Err(DecodeError::UnknownKind),
        };
    }

    /// Read a child of `sort`, which must name a node before this one.
    ///
    /// # Specification
    /// - ensures: returns the position read.
    /// - fails: returns [`DecodeError::ForwardReference`] when the builder
    ///   holds no node there yet, and [`DecodeError::WrongSort`] when the node
    ///   there has another sort.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DecodeError::Truncated`]: the bytes end inside the word.
    /// - [`DecodeError::ForwardReference`]: no earlier node stands there.
    /// - [`DecodeError::WrongSort`]: the earlier node has another sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child that names its own node and one that names a
    ///   node of each wrong sort.
    /// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |id| builder.sort_of(*id) == Ok(sort)))]
    fn child(
        &mut self,
        builder: &PlanBuilder,
        sort: Sort,
    ) -> Result<NodeId, DecodeError>
    {
        let id = NodeId::from(self.word()?.0);
        let found = builder
            .sort_of(id)
            .map_err(|_unknown| DecodeError::ForwardReference)?;
        if found != sort {
            return Err(DecodeError::WrongSort);
        }
        return Ok(id);
    }

    /// Read a quantifier's fields.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn quantifier(
        &mut self,
        builder: &PlanBuilder,
    ) -> Result<Quantifier, DecodeError>
    {
        let domain = DomainId::at(self.child(builder, Sort::Domain)?);
        let body = OpenId::at(self.child(builder, Sort::Open)?);
        let evidence = self.evidence()?;
        let dual = self.slot()?;
        return Ok(Quantifier {
            domain,
            body,
            evidence,
            dual,
        });
    }

    /// Read one node, its children naming the builder's nodes.
    ///
    /// # Specification
    /// - ensures: returns the node whose kind and fields the bytes hold, in the
    ///   writer's layout.
    /// - fails: refuses an unknown kind, a truncated field, a child that names
    ///   no earlier node or one of another sort, a malformed constant and a
    ///   malformed interval, each by name.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Errors
    /// Each [`DecodeError`] of the fields it reads, and
    /// [`DecodeError::UnknownKind`] for a kind byte that names no node.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every node kind of generated plans reads back equal;
    ///   L3 — each refusal on its smallest trigger.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
    fn node(
        &mut self,
        builder: &PlanBuilder,
    ) -> Result<Node, DecodeError>
    {
        let kind = self.kind()?;
        let node = match kind {
            Kind::BOUND => Node::Real(Real::Bound(DeBruijn::from(self.word()?.0))),
            Kind::CONSTANT => Node::Real(Real::Constant(self.dyadic()?)),
            Kind::SUM | Kind::SUB | Kind::MUL | Kind::LESS => {
                let left = RealId::at(self.child(builder, Sort::Real)?);
                let right = RealId::at(self.child(builder, Sort::Real)?);
                match kind {
                    Kind::SUM => Node::Real(Real::Add(left, right)),
                    Kind::SUB => Node::Real(Real::Sub(left, right)),
                    Kind::MUL => Node::Real(Real::Mul(left, right)),
                    Kind(_) => Node::Open(Open::Less(left, right)),
                }
            },
            Kind::DIV => {
                let numerator = RealId::at(self.child(builder, Sort::Real)?);
                let denominator = RealId::at(self.child(builder, Sort::Real)?);
                let nonzero = self.evidence()?;
                Node::Real(Real::Div {
                    numerator,
                    denominator,
                    nonzero,
                })
            },
            Kind::POWER => {
                let base = RealId::at(self.child(builder, Sort::Real)?);
                let power = Power::from(self.word()?.0);
                Node::Real(Real::Power(base, power))
            },
            Kind::CUT => {
                let hull = self.interval()?;
                let lower = OpenId::at(self.child(builder, Sort::Open)?);
                let upper = OpenId::at(self.child(builder, Sort::Open)?);
                let laws = self.evidence()?;
                Node::Real(Real::Cut(Cut {
                    hull,
                    lower,
                    upper,
                    laws,
                }))
            },
            Kind::TOP => Node::Open(Open::Top),
            Kind::BOTTOM => Node::Open(Open::Bottom),
            Kind::MEET | Kind::JOIN => {
                let left = OpenId::at(self.child(builder, Sort::Open)?);
                let right = OpenId::at(self.child(builder, Sort::Open)?);
                if kind == Kind::MEET {
                    Node::Open(Open::Meet(left, right))
                }
                else {
                    Node::Open(Open::Join(left, right))
                }
            },
            Kind::EXISTS => Node::Open(Open::Exists(self.quantifier(builder)?)),
            Kind::FORALL => Node::Open(Open::Forall(self.quantifier(builder)?)),
            Kind::INTERVAL => {
                let hull = self.interval()?;
                let overt = self.slot()?;
                let compact = self.slot()?;
                Node::Domain(Domain::Interval {
                    hull,
                    overt,
                    compact,
                })
            },
            Kind::PRODUCT => {
                let left = DomainId::at(self.child(builder, Sort::Domain)?);
                let right = DomainId::at(self.child(builder, Sort::Domain)?);
                let evidence = self.evidence()?;
                Node::Domain(Domain::Product {
                    left,
                    right,
                    evidence,
                })
            },
            Kind::SUBDOMAIN => {
                let parent = DomainId::at(self.child(builder, Sort::Domain)?);
                let classifier = OpenId::at(self.child(builder, Sort::Open)?);
                let evidence = self.evidence()?;
                Node::Domain(Domain::Subdomain {
                    parent,
                    classifier,
                    evidence,
                })
            },
            Kind(_) => return Err(DecodeError::UnknownKind),
        };
        return Ok(node);
    }
}

impl Plan
{
    /// The plan's canonical bytes.
    ///
    /// The plan is in canonical form, so the bytes are its nodes in order,
    /// each once. The work is linear in the number of distinct nodes and in
    /// the bytes of their constants.
    ///
    /// # Specification
    /// - ensures: the magic, the version, the node count, then each node's kind
    ///   and fields in the plan's order; [`Plan::decode`] reads the bytes back
    ///   to an equal plan.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated plans of every node kind round trip, and
    ///   two builds of one structure give one byte string; L3 — the cut of the
    ///   square root of two has a fixed byte count, and a chain of squares
    ///   writes one node per square.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::canonical_form_ignores_order_sharing_and_dead_nodes`
    /// - witness: `tests::plan::the_square_root_of_two_is_a_small_cut`
    /// - witness: `tests::plan::shared_subterms_serialize_once`
    #[must_use]
    #[inline]
    pub fn encode(&self) -> PlanBytes
    {
        // A pair node takes nine bytes and an inline constant at most
        // twenty-one. Sixteen bytes a node hold most plans in one allocation.
        let mut entry = Entry {
            bytes: Vec::with_capacity(
                usize::from(self.node_count())
                    .saturating_mul(16)
                    .saturating_add(14),
            ),
        };
        entry.bytes.extend_from_slice(&MAGIC);
        entry.bytes.extend_from_slice(&VERSION.to_le_bytes());
        entry.count(ByteCount(usize::from(self.node_count())));
        for (_, node) in self.nodes() {
            entry.node(node);
        }
        return PlanBytes(entry.bytes);
    }

    /// The plan that canonical bytes hold.
    ///
    /// The reader takes each node after the nodes that it names, and it
    /// refuses each malformed input by name. It then writes the plan it read
    /// and compares the bytes, so it accepts only the canonical bytes of a
    /// plan. The work is linear in the bytes and, for the comparison, in the
    /// distinct nodes times the depth of the search tree that finds equal
    /// nodes. The reader allocates no more than the bytes hold.
    ///
    /// # Specification
    /// - ensures: returns the plan whose canonical bytes `bytes` are.
    /// - fails: refuses bytes that do not open with the magic
    ///   ([`DecodeError::Magic`]) or the version ([`DecodeError::Version`]),
    ///   hold no node ([`DecodeError::Empty`]), end inside a field
    ///   ([`DecodeError::Truncated`]), carry a kind that its place does not
    ///   admit ([`DecodeError::UnknownKind`]), name a node not yet read
    ///   ([`DecodeError::ForwardReference`]) or of another sort
    ///   ([`DecodeError::WrongSort`]), hold a malformed constant or interval,
    ///   end with a domain ([`DecodeError::DomainRoot`]) or with bytes past the
    ///   last node ([`DecodeError::TrailingBytes`]), or differ from the
    ///   canonical bytes of what they hold ([`DecodeError::NotCanonical`]).
    /// - panics: none.
    /// - executable: none — the clause restates the reading.
    ///
    /// # Errors
    /// Each [`DecodeError`] above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated plans round trip, and arbitrary bytes and
    ///   one-byte edits of valid bytes either refuse or read a plan whose bytes
    ///   they are; L3 — each refusal on its smallest trigger.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
    /// - witness: `tests::plan::decoding_accepts_only_canonical_bytes`
    #[inline]
    pub fn decode(bytes: EncodedPlan<'_>) -> Result<Self, DecodeError>
    {
        return read(bytes, NodeCount::from(usize::MAX)).map_err(Fault::error);
    }
}

/// A decoding failure and where it stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Fault
{
    /// The node that the reader read when it failed, or the input as a
    /// whole.
    site: Site,
    /// The failure.
    error: DecodeError,
}

impl Fault
{
    /// Where the failure stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn site(self) -> Site
    {
        return self.site;
    }

    /// The failure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn error(self) -> DecodeError
    {
        return self.error;
    }
}

/// The plan that canonical bytes hold, read only when they count at most
/// `limit` nodes.
///
/// # Specification
/// - ensures: as [`Plan::decode`].
/// - fails: as [`Plan::decode`], and refuses a node count above `limit` as
///   [`DecodeError::TooManyNodes`] before it reads a node. A failure inside a
///   node stands at that node's position, and every other failure at the input.
/// - panics: none.
/// - executable: none — the clause restates the reading.
///
/// # Errors
/// As [`Plan::decode`], each at its site.
///
/// # Adequacy
/// - hypothesis: L2 — as [`Plan::decode`]; L3 — a count one past the limit, and
///   a fault in the last node, each at its site.
/// - witness: `tests::plan::decoding_refuses_malformed_bytes_by_name`
/// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
pub(crate) fn read(
    bytes: EncodedPlan<'_>,
    limit: NodeCount,
) -> Result<Plan, Fault>
{
    let input = |error: DecodeError| Fault {
        site: Site::Input,
        error,
    };
    let mut reader = Reader { rest: bytes.0 };
    let Taken(magic) = reader.take(ByteCount(MAGIC.len())).map_err(input)?;
    if magic != MAGIC.as_slice() {
        return Err(input(DecodeError::Magic));
    }
    let Taken(version) = reader.take(ByteCount(2)).map_err(input)?;
    if version != VERSION.to_le_bytes().as_slice() {
        return Err(input(DecodeError::Version));
    }
    let count = reader.count().map_err(input)?;
    if count.0 == 0 {
        return Err(input(DecodeError::Empty));
    }
    if count.0 > usize::from(limit) {
        return Err(input(DecodeError::TooManyNodes));
    }
    // Each node takes a byte or more, so the bytes left bound the storage
    // that the count may ask for.
    let mut builder = PlanBuilder::with_capacity(NodeCount::from(count.0.min(reader.rest.len())));
    for _ in 0 .. count.0 {
        let position = NodeId::try_from(usize::from(builder.node_count()))
            .map_err(|error| input(DecodeError::from(error)))?;
        let at = |error: DecodeError| Fault {
            site: Site::Node(position),
            error,
        };
        let node = reader.node(&builder).map_err(at)?;
        let _position = builder
            .push(node)
            .map_err(|error| at(DecodeError::from(error)))?;
    }
    if !reader.rest.is_empty() {
        return Err(input(DecodeError::TrailingBytes));
    }
    let last = NodeId::try_from(usize::from(builder.node_count()).saturating_sub(1))
        .map_err(|error| input(DecodeError::from(error)))?;
    let root = match builder.sort_of(last) {
        Ok(Sort::Real) => Root::Real(RealId::at(last)),
        Ok(Sort::Open) => Root::Open(OpenId::at(last)),
        Ok(Sort::Domain) => return Err(input(DecodeError::DomainRoot)),
        Err(error) => return Err(input(DecodeError::from(error))),
    };
    let plan = builder
        .finish(root)
        .map_err(|error| input(DecodeError::from(error)))?;
    if plan.encode().0 != bytes.0 {
        return Err(input(DecodeError::NotCanonical));
    }
    return Ok(plan);
}

/// The canonical bytes of a certificate.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CertificateBytes(Vec<u8>);

impl AsRef<[u8]> for CertificateBytes
{
    /// Borrow the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return &self.0;
    }
}

impl From<CertificateBytes> for Vec<u8>
{
    /// Take the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: CertificateBytes) -> Self
    {
        return bytes.0;
    }
}

/// Bytes that claim to be an encoded certificate, not yet read.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EncodedCertificate<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for EncodedCertificate<'bytes>
{
    /// Read a byte slice as an encoded certificate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        return Self(bytes);
    }
}

impl<'bytes> From<&'bytes CertificateBytes> for EncodedCertificate<'bytes>
{
    /// Read a certificate's own bytes as an encoded certificate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes CertificateBytes) -> Self
    {
        return Self(&bytes.0);
    }
}

impl Entry
{
    /// Write a premise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn premise(
        &mut self,
        id: StepId,
    )
    {
        self.word(Word(u32::from(id)));
    }

    /// Write a step of `kind` over the node `node` with two premises.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn binary(
        &mut self,
        kind: Kind,
        node: NodeId,
        (left, right): (StepId, StepId),
    )
    {
        self.kind(kind);
        self.child(node);
        self.premise(left);
        self.premise(right);
    }

    /// Write one certificate step: its kind, then its fields.
    ///
    /// # Specification
    /// - ensures: writes the step's kind byte and its fields in declaration
    ///   order, each by the layout of the module.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every step kind of the generated and the hand-made
    ///   certificates reads back equal.
    /// - witness: `tests::certificate::certificates_round_trip_through_their_canonical_bytes`
    fn step(
        &mut self,
        step: &Step,
    )
    {
        match *step {
            Step::Witnesses {
                cut,
                ref lower,
                ref upper,
            } => {
                self.kind(step_kind::WITNESSES);
                self.child(cut);
                self.dyadic(lower);
                self.dyadic(upper);
            },
            Step::Split {
                premise,
                ref point,
                side,
            } => {
                self.kind(step_kind::SPLIT);
                self.premise(premise);
                self.dyadic(point);
                self.kind(match side {
                    Side::Lower => FIRST,
                    Side::Upper => SECOND,
                });
            },
            Step::Constant { real } => {
                self.kind(step_kind::CONSTANT);
                self.child(real);
            },
            Step::Below { less, left, right } => {
                self.binary(step_kind::BELOW, less, (left, right));
            },
            Step::NotBelow { less, left, right } => {
                self.binary(step_kind::NOT_BELOW, less, (left, right));
            },
            Step::Variable {
                real,
                ref lower,
                ref upper,
            } => {
                self.kind(step_kind::VARIABLE);
                self.child(real);
                self.dyadic(lower);
                self.dyadic(upper);
            },
            Step::Sum { real, left, right } => self.binary(step_kind::SUM, real, (left, right)),
            Step::Difference { real, left, right } => {
                self.binary(step_kind::DIFFERENCE, real, (left, right));
            },
            Step::Product { real, left, right } => {
                self.binary(step_kind::PRODUCT, real, (left, right));
            },
            Step::Witness {
                exists: node,
                premise,
            }
            | Step::Counterexample {
                forall: node,
                premise,
            } => {
                self.kind(if matches!(*step, Step::Witness { .. }) {
                    step_kind::WITNESS
                }
                else {
                    step_kind::COUNTEREXAMPLE
                });
                self.child(node);
                self.premise(premise);
            },
            Step::Cover {
                forall: node,
                ref premises,
            }
            | Step::Refutation {
                exists: node,
                ref premises,
            } => {
                self.kind(if matches!(*step, Step::Cover { .. }) {
                    step_kind::COVER
                }
                else {
                    step_kind::REFUTATION
                });
                self.child(node);
                self.count(ByteCount(premises.len()));
                for &premise in premises {
                    self.premise(premise);
                }
            },
        }
    }
}

impl Reader<'_>
{
    /// Read one certificate step.
    ///
    /// # Specification
    /// - ensures: reads the kind byte and the fields that the layout gives for
    ///   it.
    /// - fails: returns [`DecodeError::Truncated`] when the bytes end inside
    ///   the step, [`DecodeError::UnknownKind`] for a kind or a side that the
    ///   layout does not name, and [`DecodeError::Dyadic`] for a malformed
    ///   point.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    ///
    /// # Errors
    /// Each [`DecodeError`] above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every step kind reads back; L3 — an unknown kind, an
    ///   unknown side and a truncated step.
    /// - witness: `tests::certificate::certificates_round_trip_through_their_canonical_bytes`
    /// - witness: `tests::certificate::malformed_certificate_bytes_are_refused_by_name`
    fn step(&mut self) -> Result<Step, DecodeError>
    {
        let node = |reader: &mut Self| reader.word().map(|word| NodeId::from(word.0));
        let premise = |reader: &mut Self| reader.word().map(|word| StepId::from(word.0));
        let premises = |reader: &mut Self| -> Result<Vec<StepId>, DecodeError> {
            let count = reader.count()?.0;
            // Each premise takes four bytes, so the bytes left bound the
            // storage that the count may ask for.
            let mut premises = Vec::with_capacity(count.min(reader.rest.len()));
            for _ in 0 .. count {
                premises.push(premise(reader)?);
            }
            return Ok(premises);
        };
        let operands = |reader: &mut Self| -> Result<(NodeId, StepId, StepId), DecodeError> {
            return Ok((node(reader)?, premise(reader)?, premise(reader)?));
        };
        return match self.kind()? {
            step_kind::WITNESSES => Ok(Step::Witnesses {
                cut: node(self)?,
                lower: self.dyadic()?,
                upper: self.dyadic()?,
            }),
            step_kind::SPLIT => {
                let premise = premise(self)?;
                let point = self.dyadic()?;
                let side = match self.kind()? {
                    FIRST => Side::Lower,
                    SECOND => Side::Upper,
                    _ => return Err(DecodeError::UnknownKind),
                };
                Ok(Step::Split {
                    premise,
                    point,
                    side,
                })
            },
            step_kind::CONSTANT => Ok(Step::Constant { real: node(self)? }),
            step_kind::BELOW => Ok(Step::Below {
                less: node(self)?,
                left: premise(self)?,
                right: premise(self)?,
            }),
            step_kind::NOT_BELOW => Ok(Step::NotBelow {
                less: node(self)?,
                left: premise(self)?,
                right: premise(self)?,
            }),
            step_kind::VARIABLE => Ok(Step::Variable {
                real: node(self)?,
                lower: self.dyadic()?,
                upper: self.dyadic()?,
            }),
            step_kind::SUM => {
                let (real, left, right) = operands(self)?;
                Ok(Step::Sum { real, left, right })
            },
            step_kind::DIFFERENCE => {
                let (real, left, right) = operands(self)?;
                Ok(Step::Difference { real, left, right })
            },
            step_kind::PRODUCT => {
                let (real, left, right) = operands(self)?;
                Ok(Step::Product { real, left, right })
            },
            step_kind::WITNESS => Ok(Step::Witness {
                exists: node(self)?,
                premise: premise(self)?,
            }),
            step_kind::COUNTEREXAMPLE => Ok(Step::Counterexample {
                forall: node(self)?,
                premise: premise(self)?,
            }),
            step_kind::COVER => Ok(Step::Cover {
                forall: node(self)?,
                premises: premises(self)?,
            }),
            step_kind::REFUTATION => Ok(Step::Refutation {
                exists: node(self)?,
                premises: premises(self)?,
            }),
            _ => Err(DecodeError::UnknownKind),
        };
    }
}

impl Certificate
{
    /// The certificate's canonical bytes.
    ///
    /// The bytes open with the magic `GXRC`, the format as a `u16` and the step
    /// count as a `u64`. Each step is its kind, then its fields: a node or a
    /// premise as a `u32`, a dyadic as the plan layout writes it, a side as
    /// `0x00` for the lower cut or `0x01` for the upper cut, and a list of
    /// premises as its count as a `u64`, then each premise.
    ///
    /// | Step | Byte | Fields |
    /// | ---- | ---- | ------ |
    /// | witnesses | `0x30` | the cut, the lower point, the upper point |
    /// | split | `0x31` | the premise, the point, the side |
    /// | constant | `0x32` | the constant node |
    /// | below | `0x33` | the comparison, the first premise, the second premise |
    /// | not below | `0x34` | the comparison, the first premise, the second premise |
    /// | variable | `0x35` | the variable, the lower end, the upper end |
    /// | sum | `0x36` | the sum, the first premise, the second premise |
    /// | difference | `0x37` | the difference, the first premise, the second premise |
    /// | product | `0x38` | the product, the first premise, the second premise |
    /// | witness | `0x39` | the existential, the premise |
    /// | cover | `0x3a` | the universal, the list of premises |
    /// | counterexample | `0x3b` | the universal, the premise |
    /// | refutation | `0x3c` | the existential, the list of premises |
    ///
    /// # Specification
    /// - ensures: the magic, the format, the step count, then each step's kind
    ///   and fields in order; [`Certificate::decode`] reads them back to an
    ///   equal certificate.
    /// - panics: none.
    /// - executable: none — the clause restates the layout.
    /// - intension: one allocation, sized for the steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the refinements of generated radicands and every
    ///   hand-made certificate round trip.
    /// - witness: `tests::certificate::certificates_round_trip_through_their_canonical_bytes`
    /// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
    #[must_use]
    #[inline]
    pub fn encode(&self) -> CertificateBytes
    {
        // A split step takes about thirty bytes at the widths of stage A.
        let mut entry = Entry {
            bytes: Vec::with_capacity(self.steps().len().saturating_mul(32).saturating_add(14)),
        };
        entry.bytes.extend_from_slice(&CERTIFICATE_MAGIC);
        entry
            .bytes
            .extend_from_slice(&u16::from(self.format()).to_le_bytes());
        entry.count(ByteCount(self.steps().len()));
        for step in self.steps() {
            entry.step(step);
        }
        return CertificateBytes(entry.bytes);
    }

    /// The certificate that canonical bytes hold.
    ///
    /// The reader checks the layout alone. The replay of
    /// [`crate::certificate::check`] judges what the steps claim.
    ///
    /// # Specification
    /// - ensures: returns the certificate whose canonical bytes `bytes` are.
    /// - fails: refuses bytes that do not open with the magic
    ///   ([`DecodeError::Magic`]) or the current format
    ///   ([`DecodeError::Version`]), hold no step ([`DecodeError::Empty`]), end
    ///   inside a field ([`DecodeError::Truncated`]), carry a kind that its
    ///   place does not admit ([`DecodeError::UnknownKind`]), hold a malformed
    ///   point ([`DecodeError::Dyadic`]), carry bytes past the last step
    ///   ([`DecodeError::TrailingBytes`]), or differ from the canonical bytes
    ///   of what they hold ([`DecodeError::NotCanonical`]).
    /// - panics: none.
    /// - executable: none — the clause restates the reading.
    /// - intension: linear in the bytes. The reader allocates no more than the
    ///   bytes hold.
    ///
    /// # Errors
    /// Each [`DecodeError`] above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — refinements round trip, and one-byte edits of their
    ///   bytes either refuse or read a certificate whose bytes they are; L3 —
    ///   each refusal on its smallest trigger.
    /// - witness: `tests::certificate::certificates_round_trip_through_their_canonical_bytes`
    /// - witness: `tests::certificate::malformed_certificate_bytes_are_refused_by_name`
    #[inline]
    pub fn decode(bytes: EncodedCertificate<'_>) -> Result<Self, DecodeError>
    {
        let mut reader = Reader { rest: bytes.0 };
        let Taken(magic) = reader.take(ByteCount(CERTIFICATE_MAGIC.len()))?;
        if magic != CERTIFICATE_MAGIC.as_slice() {
            return Err(DecodeError::Magic);
        }
        let Taken(format) = reader.take(ByteCount(2))?;
        if format != u16::from(FormatVersion::CURRENT).to_le_bytes().as_slice() {
            return Err(DecodeError::Version);
        }
        let count = reader.count()?;
        if count.0 == 0 {
            return Err(DecodeError::Empty);
        }
        // Each step takes a byte or more, so the bytes left bound the storage
        // that the count may ask for.
        let mut steps = Vec::with_capacity(count.0.min(reader.rest.len()));
        for _ in 0 .. count.0 {
            steps.push(reader.step()?);
        }
        if !reader.rest.is_empty() {
            return Err(DecodeError::TrailingBytes);
        }
        let certificate = Self::new(FormatVersion::CURRENT, steps);
        if certificate.encode().0 != bytes.0 {
            return Err(DecodeError::NotCanonical);
        }
        return Ok(certificate);
    }
}

/// The four bytes that open an encoded checkpoint.
const CHECKPOINT_MAGIC: [u8; 4] = *b"GXRK";

/// The kind byte of an obligation's demand in a checkpoint.
mod demand_kind
{
    use super::Kind;

    /// The open node holds.
    pub(super) const HOLDS: Kind = Kind(0x40);
    /// The open node fails.
    pub(super) const FAILS: Kind = Kind(0x41);
    /// An enclosure of a real node to a power of two.
    pub(super) const ENCLOSES: Kind = Kind(0x42);
}

/// The canonical bytes of a checkpoint.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CheckpointBytes(Vec<u8>);

impl AsRef<[u8]> for CheckpointBytes
{
    /// Borrow the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return &self.0;
    }
}

impl From<CheckpointBytes> for Vec<u8>
{
    /// Take the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: CheckpointBytes) -> Self
    {
        return bytes.0;
    }
}

/// Bytes offered as a checkpoint, read by
/// [`crate::dovetail::Dovetail::resume`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EncodedCheckpoint<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for EncodedCheckpoint<'bytes>
{
    /// Read a byte slice as an encoded checkpoint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        return Self(bytes);
    }
}

impl<'bytes> From<&'bytes CheckpointBytes> for EncodedCheckpoint<'bytes>
{
    /// Read a checkpoint's own bytes as an encoded checkpoint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes CheckpointBytes) -> Self
    {
        return Self(&bytes.0);
    }
}

impl AsRef<[u8]> for EncodedCheckpoint<'_>
{
    /// Borrow the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return self.0;
    }
}

/// One live obligation as a checkpoint holds it: its node, its demand, the
/// steps spent on it, and the steps of its certificate so far.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Held
{
    /// The node of the obligation.
    node: NodeId,
    /// The demand of the obligation.
    demand: Demand,
    /// The steps done on the obligation.
    spent: Steps,
    /// The steps of its certificate so far.
    steps: Vec<Step>,
}

impl Held
{
    /// The node, the demand, the spent steps and the steps of the
    /// certificate, taken out of the record.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn into_parts(self) -> (NodeId, Demand, Steps, Vec<Step>)
    {
        return (self.node, self.demand, self.spent, self.steps);
    }
}

/// The fields of a checkpoint as its bytes state them, not yet judged
/// against a plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Fields
{
    /// The most steps of one turn, or `None` for a quantum of no steps.
    quantum: Option<Quantum>,
    /// The bounds of each certificate.
    quotas: CheckerQuotas,
    /// The position of the next turn among the live obligations.
    cursor: Position,
    /// The live obligations, in the order of their turns.
    held: Vec<Held>,
}

impl Fields
{
    /// The quantum, the quotas, the cursor and the live obligations, taken
    /// out of the record.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn into_parts(self) -> (Option<Quantum>, CheckerQuotas, Position, Vec<Held>)
    {
        return (self.quantum, self.quotas, self.cursor, self.held);
    }
}

/// A `u64` field of a checkpoint.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Wide(u64);

impl Entry
{
    /// Write a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn wide(
        &mut self,
        value: Wide,
    )
    {
        self.bytes.extend_from_slice(&value.0.to_le_bytes());
    }

    /// Write a demand: its kind, then the width of an enclosure as an `i32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn demand(
        &mut self,
        demand: Demand,
    )
    {
        match demand {
            Demand::Holds => self.kind(demand_kind::HOLDS),
            Demand::Fails => self.kind(demand_kind::FAILS),
            Demand::Encloses { width } => {
                self.kind(demand_kind::ENCLOSES);
                self.bytes
                    .extend_from_slice(&i32::from(width).to_le_bytes());
            },
        }
    }
}

impl Reader<'_>
{
    /// Read a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn wide(&mut self) -> Result<Wide, DecodeError>
    {
        let (&wide, rest) = self
            .rest
            .split_first_chunk::<8>()
            .ok_or(DecodeError::Truncated)?;
        self.rest = rest;
        return Ok(Wide(u64::from_le_bytes(wide)));
    }

    /// Read a demand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn demand(&mut self) -> Result<Demand, DecodeError>
    {
        return match self.kind()? {
            demand_kind::HOLDS => Ok(Demand::Holds),
            demand_kind::FAILS => Ok(Demand::Fails),
            demand_kind::ENCLOSES => {
                let (&width, rest) = self
                    .rest
                    .split_first_chunk::<4>()
                    .ok_or(DecodeError::Truncated)?;
                self.rest = rest;
                Ok(Demand::Encloses {
                    width: Exponent::from(i32::from_le_bytes(width)),
                })
            },
            _ => Err(DecodeError::UnknownKind),
        };
    }
}

/// The canonical bytes of a checkpoint with these fields.
///
/// The bytes open with the magic `GXRK` and the version as a `u16`. The
/// quantum follows as a `u32`, then the step quota, the width quota, the
/// cursor and the count of live obligations, each a `u64`. Each obligation
/// is its node as a `u32`, its demand, the steps spent on it as a `u64`, and
/// the count and the steps of its certificate as [`Certificate::encode`]
/// writes them.
///
/// | Demand | Byte | Fields |
/// | ------ | ---- | ------ |
/// | holds | `0x40` | none |
/// | fails | `0x41` | none |
/// | encloses | `0x42` | the width as an `i32` |
///
/// # Specification
/// - ensures: the magic, the version, then the fields in order;
///   [`read_checkpoint`] reads them back to equal fields.
/// - panics: none.
/// - executable: none — the clause restates the layout.
/// - intension: one allocation, sized for the steps.
///
/// # Adequacy
/// - hypothesis: L2 — every checkpoint of generated runs round trips.
/// - witness: `tests::checkpoint::a_resumed_run_certifies_as_an_unbroken_one`
pub(crate) fn write_checkpoint<'steps, Held>(
    (quantum, quotas, cursor): (Quantum, &CheckerQuotas, Position),
    held: Held,
) -> CheckpointBytes
where
    Held: Iterator<Item = (NodeId, Demand, Steps, &'steps [Step])> + Clone,
{
    let (count, steps) =
        held.clone()
            .fold((0_usize, 0_usize), |(count, steps), (_, _, _, held)| {
                (count.saturating_add(1), steps.saturating_add(held.len()))
            });
    // A split step takes about thirty bytes at the widths of stage A.
    let mut entry = Entry {
        bytes: Vec::with_capacity(
            steps
                .saturating_mul(32)
                .saturating_add(count.saturating_mul(24))
                .saturating_add(46),
        ),
    };
    entry.bytes.extend_from_slice(&CHECKPOINT_MAGIC);
    entry.bytes.extend_from_slice(&VERSION.to_le_bytes());
    entry.word(Word(NonZeroU32::from(quantum).get()));
    entry.count(ByteCount(usize::from(quotas.steps)));
    entry.wide(Wide(u64::from(quotas.width)));
    entry.count(ByteCount(usize::from(cursor)));
    entry.count(ByteCount(count));
    for (node, demand, spent, steps) in held {
        entry.word(Word(u32::from(node)));
        entry.demand(demand);
        entry.wide(Wide(u64::from(spent)));
        entry.count(ByteCount(steps.len()));
        for step in steps {
            entry.step(step);
        }
    }
    return CheckpointBytes(entry.bytes);
}

/// The fields that the bytes of a checkpoint state.
///
/// The reader checks the layout alone. [`crate::dovetail::Dovetail::resume`]
/// judges the fields against a plan, replays each certificate's steps, and
/// refuses bytes that differ from the canonical bytes of what they hold.
///
/// # Specification
/// - ensures: returns the fields that [`write_checkpoint`] writes as `bytes`.
/// - fails: refuses bytes that do not open with the magic
///   ([`DecodeError::Magic`]) or the current version
///   ([`DecodeError::Version`]), end inside a field
///   ([`DecodeError::Truncated`]), carry a kind that its place does not admit
///   ([`DecodeError::UnknownKind`]), hold a malformed point
///   ([`DecodeError::Dyadic`]), or carry bytes past the last obligation
///   ([`DecodeError::TrailingBytes`]).
/// - panics: none.
/// - executable: none — the clause restates the reading.
/// - intension: linear in the bytes. The reader allocates no more than the
///   bytes hold.
///
/// # Errors
/// Each [`DecodeError`] above.
///
/// # Adequacy
/// - hypothesis: L3 — each refusal on its smallest trigger.
/// - witness: `tests::checkpoint::a_corrupt_checkpoint_is_refused_by_name`
pub(crate) fn read_checkpoint(bytes: EncodedCheckpoint<'_>) -> Result<Fields, DecodeError>
{
    let mut reader = Reader { rest: bytes.0 };
    let Taken(magic) = reader.take(ByteCount(CHECKPOINT_MAGIC.len()))?;
    if magic != CHECKPOINT_MAGIC.as_slice() {
        return Err(DecodeError::Magic);
    }
    let Taken(version) = reader.take(ByteCount(2))?;
    if version != VERSION.to_le_bytes().as_slice() {
        return Err(DecodeError::Version);
    }
    let quantum = NonZeroU32::new(reader.word()?.0).map(Quantum::from);
    let quotas = CheckerQuotas {
        steps: StepCount::from(reader.count()?.0),
        width: BitWidth::from(reader.wide()?.0),
    };
    let cursor = Position::from(reader.count()?.0);
    let count = reader.count()?.0;
    // Each obligation takes a byte or more, so the bytes left bound the
    // storage that the count may ask for.
    let mut held = Vec::with_capacity(count.min(reader.rest.len()));
    for _ in 0 .. count {
        let node = NodeId::from(reader.word()?.0);
        let demand = reader.demand()?;
        let spent = Steps::from(reader.wide()?.0);
        let length = reader.count()?.0;
        let mut steps = Vec::with_capacity(length.min(reader.rest.len()));
        for _ in 0 .. length {
            steps.push(reader.step()?);
        }
        held.push(Held {
            node,
            demand,
            spent,
            steps,
        });
    }
    if !reader.rest.is_empty() {
        return Err(DecodeError::TrailingBytes);
    }
    return Ok(Fields {
        quantum,
        quotas,
        cursor,
        held,
    });
}
