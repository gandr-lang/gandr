//! The judgement as the formers and formation ask it: forming a type and
//! checking a value.
//!
//! The judgement reads the formers and formation, and they ask the judgement
//! in turn. A type forms in the judgement's machine, and a former checks an
//! interface's laws there. A context holds a [`Judge`], and these two asks go
//! through it. So no module below the judgement names the judgement, and the
//! judgement builds over them.
//!
//! The module also holds what a judgement answers: the [`Direction`] it runs
//! in, the type it [`Synthesised`] and the evidence it [`Checked`] with. The
//! modules below the judgement read them, and the judgement makes them.
//!
//! # One indirect call at each ask
//!
//! An ask is one call through the context's trait object. The judgement it
//! starts runs its machine for many steps, so the call is a small part of the
//! ask. The alternative was a context generic over its judge. Every function
//! that names a context then names the judge, and the whole checker compiles
//! where the judge is known. Reversal: a measure of the checking path where
//! the indirect call costs more than 1 %.

use core::fmt;

use gandr_core_term::ValueId;

use crate::context::CheckingContext;
use crate::conversion::ConversionCount;
use crate::failure::Failure;
use crate::formation::FormedValueType;
use crate::refusal::TypeNode;

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

/// The judgement's two entries that the formers and formation ask through a
/// context.
///
/// # Specification
/// - provides: forming a type and checking a value, for the modules the
///   judgement builds over.
/// - panics: none of its own.
/// - executable: none — the trait states obligations its implementation
///   carries.
pub trait Judge: fmt::Debug + Sync
{
    /// Form `node` in the context's binders, and keep the failure of a
    /// refused run.
    ///
    /// # Specification
    /// - requires: `node` resolves in the context's arena, under the context's
    ///   binders.
    /// - ensures: the judgement's formation of `node`; the context's binders
    ///   stand where they stood before.
    /// - panics: none.
    /// - executable: none — the formation is the implementation's run.
    ///
    /// # Errors
    /// The failure of the refused run, with the rules pending when it refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the implementation's witnesses form each type former
    ///   and refuse a malformed one by name.
    /// - declaration-only: the obligation is the implementation's run; the
    ///   trait has no body to witness.
    fn form(
        &self,
        context: &mut CheckingContext<'_>,
        node: TypeNode,
    ) -> Result<(), Failure>;

    /// Check `value` against `expected`, and keep the failure of a refused
    /// run.
    ///
    /// # Specification
    /// - requires: `value` resolves in the context's arena, closed over the
    ///   context's binders; `expected` formed there.
    /// - ensures: the judgement's check of `value` at `expected`, with the
    ///   conversions the run made; the context's binders stand where they stood
    ///   before.
    /// - panics: none.
    /// - executable: none — the check is the implementation's run.
    ///
    /// # Errors
    /// The failure of the refused run, with the rules pending when it refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the implementation's witnesses check each value
    ///   former in both modes and refuse each mismatch by name.
    /// - declaration-only: the obligation is the implementation's run; the
    ///   trait has no body to witness.
    fn check_value(
        &self,
        context: &mut CheckingContext<'_>,
        value: ValueId,
        expected: FormedValueType,
    ) -> Result<Checked, Failure>;
}
