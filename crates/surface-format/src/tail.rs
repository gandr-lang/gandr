//! The tails whose `return` the sugared form leaves unwritten, as the source's
//! lowering lists them.
//!
//! A `return` where a path through a body ends, over a value, is the exit
//! the lowering infers for that value written bare, so the sugared form writes
//! the value alone. Whether a `return` stands so is the lowering's to say: a
//! tail is a body's last computation or what stands in tail position of one —
//! a match's arm, a block's last statement — and a `return` in a statement
//! whose rest it distributes is an early exit, which stays. The operand's
//! polarity decides the exit a bare tail takes, so a `return` of a computation
//! stays too, and so does every `return` an `explicit_exits` attribute asks
//! for. The lowering lists exactly the elidable ones
//! (`gandr_surface_lowering::ElidableExit`); this module carries their spans
//! into the formatted source.

use alloc::vec::Vec;

use gandr_surface_lowering::LoweredModule;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;

use crate::composite::Reach;
use crate::composite::within;

/// The spans of the `return` forms the sugared form writes as their value.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tails
{
    /// The `return` forms' spans, in the source's own offsets.
    elidable: Vec<ByteSpan>,
    /// Which `return` forms are elidable.
    reach: Reach,
}

/// How the sugared form writes a `return` form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Exit
{
    /// The lowering would infer it: written as its value.
    Inferred,
    /// Written as it is.
    Kept,
}

impl Tails
{
    /// Every `return` elidable: for the writing that asks which forms a
    /// rewrite would enter.
    ///
    /// # Specification
    /// trivial.
    pub const fn any() -> Self
    {
        Self {
            elidable: Vec::new(),
            reach: Reach::Any,
        }
    }

    /// The elidable exits `module` lists, of which the formatted source starts
    /// at `base` in the unit's text.
    ///
    /// # Specification
    /// trivial.
    pub fn of(
        module: &LoweredModule<'_>,
        base: ByteOffset,
    ) -> Self
    {
        Self {
            elidable: module
                .elidable_exits()
                .iter()
                .filter_map(|exit| within(exit.span, base))
                .collect(),
            reach: Reach::Derived,
        }
    }

    /// How the sugared form writes the `return` form spanning exactly `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn exit(
        &self,
        span: ByteSpan,
    ) -> Exit
    {
        match (self.reach, self.elidable.binary_search(&span)) {
            (Reach::Any, _) | (Reach::Derived, Ok(_)) => Exit::Inferred,
            (Reach::Derived, Err(_)) => Exit::Kept,
        }
    }
}
