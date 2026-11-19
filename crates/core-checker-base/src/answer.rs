//! What a judgement answers: the [`Direction`] it runs in, the type it
//! [`Synthesised`] and the evidence it [`Checked`] with, and the reason the
//! memo gives a goal no answer.
//!
//! The modules below the judgement read these types, and the judgement makes
//! them. Thus a module below the judgement names this module, and not the
//! judgement.

use crate::conversion::ConversionCount;

quenchant_shape::reason_enum! {
    /// Why the memo gives a goal no answer.
    pub mod unanswered {
        /// The reason it gives none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The memo neither answers nor records where the run stands.
            Closed,
            /// The goal is not a value judgement or a value type's formation,
            /// or it reads a linear binder or one the context does not hold.
            Unkeyed,
            /// The memo holds no answer for the goal's key; the goal is now
            /// under way, and its answer is recorded when it finishes.
            Missed,
        }
    }
}

/// The direction a judgement runs in.
///
/// # Judgement
/// - direction: synthesis hands the term's type out; checking takes the
///   expected type in. A dispatch on it names both, so a rule added in one mode
///   is a compile error in every dispatch that forgot the other.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Direction<Expected>
{
    /// The term's type is read off the term.
    Synthesise,
    /// The term is checked against the type held.
    Check(Expected),
}

/// A type a judgement synthesised, beside the evidence of how it got there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Synthesised<Type>
{
    /// The type.
    produced: Type,
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl<Type: Copy> Synthesised<Type>
{
    /// The synthesis of `produced`, after a run that made `conversions`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        produced: Type,
        conversions: ConversionCount,
    ) -> Self
    {
        Self {
            produced,
            conversions,
        }
    }

    /// The type synthesised.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn produced(&self) -> Type
    {
        self.produced
    }

    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}

/// The evidence a check succeeded with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Checked
{
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl Checked
{
    /// The evidence of a check whose run made `conversions`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(conversions: ConversionCount) -> Self
    {
        Self { conversions }
    }

    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}
