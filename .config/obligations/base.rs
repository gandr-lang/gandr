//! The recorded case of the re-verification lane (#2636): `base.rs` is the
//! crate before its change and `edited.rs` after it, the two differing in
//! `limit`'s body alone. `bump`'s prose clause names `limit`, so the change
//! obliges that clause to be re-read (`check:obligations`).

/// A level a bump raises.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Level(u8);

/// The level a bump stops at.
///
/// # Specification
/// - ensures: the third level.
#[must_use]
pub const fn limit() -> Level
{
    Level(3)
}

/// One level up, never past the bound.
///
/// # Specification
/// - ensures: the result is at most [`limit`].
#[must_use]
pub fn bump(level: Level) -> Level
{
    Level(level.0.saturating_add(1)).min(limit())
}
