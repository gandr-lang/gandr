//! The canonical serialization of a plan.
//!
//! A plan crosses a process boundary as bytes, and a later stage keys a
//! cache and a certificate by them. So the bytes of a plan are canonical: two
//! plans of equal structure give equal bytes, and the bytes read back to an
//! equal plan. The writer reads a [`Plan`] in its canonical form and writes
//! each node once, in the plan's order. A child is the position of a node
//! before it. The reader refuses each malformed input by name, and it refuses
//! bytes that decode but differ from the canonical bytes of what they hold.
//! The root is the last node, and its sort says whether the plan encloses a
//! real or decides an open proposition.
//!
//! # Boundaries
//!
//! The layout follows the tree's convention for canonical bytes: a one-byte
//! kind before each record, every integer little-endian at a fixed width, a
//! byte payload after its length as a `u64`, and no unknown kind admitted.
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

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use num_bigint::BigInt;

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
use crate::plan::Sort;

/// The four bytes that open an encoded plan.
const MAGIC: [u8; 4] = *b"GXRP";

/// The layout version that this build writes and reads.
const VERSION: u16 = 1;

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
    /// The bytes do not open with the plan magic.
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
    /// The bytes hold no node.
    Empty,
    /// The last node, the root, is a domain.
    DomainRoot,
    /// Bytes follow the last node.
    TrailingBytes,
    /// The count of nodes exceeds what a position counts.
    TooManyNodes,
    /// A constant's exponent leaves its range.
    Dyadic(DyadicError),
    /// An interval is malformed.
    Interval(IntervalError),
    /// The bytes decode, but they differ from the canonical bytes of the plan
    /// that they hold.
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
            Self::Magic => f.write_str("the bytes do not open with the plan magic"),
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
            Self::Empty => f.write_str("the bytes hold no node"),
            Self::DomainRoot => f.write_str("the root is a domain"),
            Self::TrailingBytes => f.write_str("bytes follow the last node"),
            Self::TooManyNodes => f.write_str("the count of nodes exceeds what a position counts"),
            Self::Dyadic(error) => write!(f, "a constant is malformed: {error}"),
            Self::Interval(error) => write!(f, "an interval is malformed: {error}"),
            Self::NotCanonical => {
                f.write_str("the bytes are not the canonical bytes of their plan")
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
        let mut reader = Reader { rest: bytes.0 };
        let Taken(magic) = reader.take(ByteCount(MAGIC.len()))?;
        if magic != MAGIC.as_slice() {
            return Err(DecodeError::Magic);
        }
        let Taken(version) = reader.take(ByteCount(2))?;
        if version != VERSION.to_le_bytes().as_slice() {
            return Err(DecodeError::Version);
        }
        let count = reader.count()?;
        if count.0 == 0 {
            return Err(DecodeError::Empty);
        }
        // Each node takes a byte or more, so the bytes left bound the
        // storage that the count may ask for.
        let mut builder =
            PlanBuilder::with_capacity(NodeCount::from(count.0.min(reader.rest.len())));
        for _ in 0 .. count.0 {
            let node = reader.node(&builder)?;
            let _position = builder.push(node)?;
        }
        if !reader.rest.is_empty() {
            return Err(DecodeError::TrailingBytes);
        }
        let last = NodeId::try_from(usize::from(builder.node_count()).saturating_sub(1))?;
        let root = match builder.sort_of(last)? {
            Sort::Real => Root::Real(RealId::at(last)),
            Sort::Open => Root::Open(OpenId::at(last)),
            Sort::Domain => return Err(DecodeError::DomainRoot),
        };
        let plan = builder.finish(root)?;
        if plan.encode().0 != bytes.0 {
            return Err(DecodeError::NotCanonical);
        }
        return Ok(plan);
    }
}
