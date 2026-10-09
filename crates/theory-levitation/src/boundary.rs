//! The crate's own boundary wrappers: every name, count, index, verdict and
//! rendered text a signature of this crate crosses, so no signature passes a
//! bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits,
//! so a primitive is unpacked only where a comparison, an index, a count or
//! an encoding needs it. The vocabulary is this crate's alone: a consumer
//! keeps its own names, budgets and verdicts, and nothing here is another
//! crate's wrapper re-exported.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// Defines a transparent copyable newtype over one numeric primitive, with
/// `From` conversions both ways and `Display` passthrough.
macro_rules! count_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the wrapped number.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                self.0.fmt(f)
            }
        }
    };
}

/// Defines a transparent copyable newtype over one `bool` verdict, with `From`
/// conversions both ways.
macro_rules! verdict_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name(bool);

        impl From<bool> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: bool) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for bool
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

/// Defines a transparent owned-text newtype over a `String`, with `From`
/// conversions both ways, `AsRef<str>` and `Display` passthrough.
macro_rules! text_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
        $vis struct $name(String);

        impl From<String> for $name
        {
            /// Wraps the text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: String) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for String
        {
            /// Unwraps the text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl AsRef<str> for $name
        {
            /// The wrapped text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &str
            {
                &self.0
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the wrapped text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                self.0.fmt(f)
            }
        }
    };
}

/// A borrowed source-level name: a constructor, operation, sort, parameter,
/// port or pattern-variable spelling, read without taking ownership.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NameRef<'source>(&'source str);

impl<'source> From<&'source str> for NameRef<'source>
{
    /// Borrows the spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'source str) -> Self
    {
        Self(value)
    }
}

impl<'source> From<&'source String> for NameRef<'source>
{
    /// Borrows the owned spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'source String) -> Self
    {
        Self(value.as_str())
    }
}

impl<'source> From<NameRef<'source>> for &'source str
{
    /// The borrowed spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NameRef<'source>) -> Self
    {
        value.0
    }
}

impl AsRef<str> for NameRef<'_>
{
    /// The borrowed spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for NameRef<'_>
{
    /// Writes the spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

count_wrapper! {
    /// A zero-based constructor index into a description's constructor table.
    pub struct ConstructorTag(usize);
}

count_wrapper! {
    /// The monotone serial a minted description identity carries, assigned in
    /// declaration order within one elaboration.
    pub struct NominalSerial(u64);
}

count_wrapper! {
    /// A byte offset into the source text, for description provenance spans.
    pub struct SurfaceByteOffset(usize);
}

count_wrapper! {
    /// The number of monomials in a bridge arity's product layer.
    pub struct MonomialCount(usize);
}

count_wrapper! {
    /// A child index within a first-order term position, counted from the
    /// left.
    pub struct TermPositionIndex(usize);
}

count_wrapper! {
    /// The number of arguments a rewrite-sorted port's instantiation involves.
    pub struct PortArgumentCount(usize);
}

count_wrapper! {
    /// The most boundary nodes one circuit derivation may unfold.
    pub struct CircuitNodeBudget(usize);
}

impl CircuitNodeBudget
{
    /// The standing ceiling a circuit derivation runs under.
    ///
    /// A wire consumed twice is unfolded twice, so reconvergence is a shared
    /// subterm on the term-shaped store and a body of `n` doubling frames
    /// derives a term of `2ⁿ` nodes. The ceiling turns a source-supplied
    /// body's blow-up into a defined decline rather than a hang. It is a
    /// ceiling, not a measurement: far above any wiring a reader writes (the
    /// two-redex congruence body derives five nodes) and far below where the
    /// unfolding stops being interactive.
    pub const DEFAULT: Self = Self(4_096);
}

verdict_wrapper! {
    /// Whether an attribute slot holds no markers.
    pub struct AttributeEmptiness;
}

verdict_wrapper! {
    /// Whether an attribute slot holds a named marker.
    pub struct AttributePresence;
}

verdict_wrapper! {
    /// Whether a description code lies in the first-order fragment.
    pub struct FirstOrderStatus;
}

verdict_wrapper! {
    /// Whether a description or a code mentions a recursive occurrence.
    pub struct RecursiveStatus;
}

verdict_wrapper! {
    /// Whether a rule-face pattern variable occurs exactly once on the
    /// left-hand side.
    pub struct RuleVariableLinearity;
}

verdict_wrapper! {
    /// The verdict of description-guided structural equality of two values.
    pub struct GenericEquality;
}

verdict_wrapper! {
    /// Whether a typed rule face's context types every pattern variable the
    /// face declares.
    pub struct ContextTotality;
}

text_wrapper! {
    /// The inspection rendering of a whole description.
    pub struct SerializedDescText;
}

text_wrapper! {
    /// A human-readable well-formedness diagnostic.
    pub struct DiagnosticMessage;
}

/// The canonical byte encoding of a value of a described datatype.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct SerializedValueBytes(Vec<u8>);

impl From<Vec<u8>> for SerializedValueBytes
{
    /// Wraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Vec<u8>) -> Self
    {
        Self(value)
    }
}

impl From<SerializedValueBytes> for Vec<u8>
{
    /// Unwraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: SerializedValueBytes) -> Self
    {
        value.0
    }
}

impl AsRef<[u8]> for SerializedValueBytes
{
    /// The encoded bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// The opaque bytes a leaf field's value carries, read by the leaf's own
/// value decoder and compared bytewise by the generic programs.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LeafBytes(Box<[u8]>);

impl From<Box<[u8]>> for LeafBytes
{
    /// Wraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Box<[u8]>) -> Self
    {
        Self(value)
    }
}

impl From<Vec<u8>> for LeafBytes
{
    /// Wraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Vec<u8>) -> Self
    {
        Self(value.into_boxed_slice())
    }
}

impl From<&[u8]> for LeafBytes
{
    /// Copies the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &[u8]) -> Self
    {
        Self(Box::from(value))
    }
}

impl From<LeafBytes> for Box<[u8]>
{
    /// Unwraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: LeafBytes) -> Self
    {
        value.0
    }
}

impl AsRef<[u8]> for LeafBytes
{
    /// The leaf's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}
