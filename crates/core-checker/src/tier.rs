//! The driver's tier: where a closed endpoint pair is decided before the
//! machine.
//!
//! The checker names no evaluator. A run hands its context a [`ClosedTier`]
//! the driver supplies, as it hands a staging check a [`crate::fork::Fork`],
//! and the driver owns the emitter, its code and its fuel. The `here` rule
//! offers the tier each endpoint pair whose two sides mention no variable. A
//! pair the tier meets carries the one decision `Evaluate`, which the kernel
//! converts by its own evaluation; every other pair goes to the machine, as
//! every pair does in a context with no tier.

use alloc::boxed::Box;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;

use crate::code::CodeDefinitions;

/// Runs two closed values to their normal forms and compares them.
///
/// # Specification
/// - provides: the `here` rule's first try at a closed endpoint pair.
/// - panics: none of its own.
/// - executable: none — the trait states obligations its implementations carry.
pub trait ClosedTier
{
    /// Whether `pair`'s two values reach one normal form, every definition
    /// `definitions` holds unfolding.
    ///
    /// # Specification
    /// - requires: both values mention no variable, and they and every body
    ///   `definitions` holds live in `core`.
    /// - ensures: [`Meeting::Met`] only when both values run to normal forms
    ///   that are one term; [`Meeting::Unmet`] otherwise, a run that spends the
    ///   tier's fuel, sticks or does not read back among them.
    /// - panics: none.
    /// - executable: none — the normal forms are the implementation's runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each implementation's witness meets a pair that
    ///   computes one value and leaves apart one that computes two.
    /// - declaration-only: the obligation is each implementation's run; the
    ///   trait has no body to witness.
    fn meet(
        &mut self,
        core: &CoreArena,
        definitions: &CodeDefinitions,
        pair: (ValueId, ValueId),
    ) -> Meeting;
}

/// What a tier answers for a closed pair.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Meeting
{
    /// Both values ran to one normal form.
    Met,
    /// The tier shows nothing: the machine decides the pair.
    Unmet,
}

/// Makes the tier a context decides closed pairs on: one per context, so a
/// tier's focused program never outlives the arena its definitions live in.
pub type MakeTier = fn() -> Box<dyn ClosedTier>;
