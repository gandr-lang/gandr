//! The tactics a splice runs at the hole it writes.
//!
//! A splice `~t` stands where a term is read and names a compile-stage
//! program, the tactic `t`, run at the goal the position holds: the binders
//! in scope with their types, and the type the term is checked against. The
//! checker runs the tactic, judges the term it returns against the goal again
//! and fills the hole with it, so the kernel replays the filled declaration
//! and no tactic is trusted.
//!
//! Two tactics stand: `assumption`, the innermost binder whose type is the
//! goal's, and `intro(t)`, a function whose body is `t`'s answer at the goal
//! of its codomain, the binder in scope. A [`Tactic`] is the count of
//! introductions before the assumption, which is every program the two
//! compose to; the hole a splice writes carries it in its name
//! ([`crate::hole::HoleId::spliced`]).

use anodized::spec;

/// A tactic: `intros` introductions, the innermost last, then an
/// assumption.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Tactic
{
    /// The introductions before the assumption.
    intros: u8,
}

impl Tactic
{
    /// `assumption` alone.
    pub const ASSUMPTION: Self = Self { intros: 0 };
    /// The introductions a tactic may make before its assumption, exclusive.
    pub const INTROS: u8 = 32;

    /// `intro(self)`: one introduction before `self`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a tactic of one more introduction than `self`; `None` once
    ///   that count reaches [`Self::INTROS`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `assumption` under one introduction and under the
    ///   last one admitted separate the tactics from the refusal past it.
    /// - witness: `tactic::tests::intro_counts_up_to_the_limit`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        Some(tactic) => tactic.intros == self.intros.saturating_add(1) && tactic.intros < Self::INTROS,
        None => self.intros.saturating_add(1) >= Self::INTROS,
    })]
    pub const fn intro(self) -> Option<Self>
    {
        let intros = self.intros.saturating_add(1);
        if intros >= Self::INTROS {
            return None;
        }
        Some(Self { intros })
    }

    /// The tactic `intro` runs at its body's goal, or `None` for
    /// `assumption`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tactic of one introduction fewer when `self` makes one;
    ///   `None` when it makes none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `intro(assumption)` answers `assumption`, and
    ///   `assumption` answers none.
    /// - witness: `tactic::tests::intro_counts_up_to_the_limit`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        Some(body) => body.intros.saturating_add(1) == self.intros,
        None => self.intros == 0,
    })]
    pub const fn body(self) -> Option<Self>
    {
        match self.intros.checked_sub(1) {
            Some(intros) => Some(Self { intros }),
            None => None,
        }
    }
}

/// A count of introductions at or past [`Tactic::INTROS`], which no tactic
/// makes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TooManyIntros;

impl From<Tactic> for u8
{
    /// The introductions `tactic` makes before its assumption.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tactic: Tactic) -> Self
    {
        tactic.intros
    }
}

impl TryFrom<u8> for Tactic
{
    type Error = TooManyIntros;

    /// The tactic of `intros` introductions before its assumption.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tactic `u8::from` reads `intros` back from below
    ///   [`Tactic::INTROS`]; [`TooManyIntros`] from it on.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last count admitted and the first refused
    ///   separate the tactics from the refusal.
    /// - witness: `tactic::tests::intro_counts_up_to_the_limit`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(intros >= Self::INTROS, |tactic| tactic.intros == intros))]
    fn try_from(intros: u8) -> Result<Self, Self::Error>
    {
        if intros >= Self::INTROS {
            return Err(TooManyIntros);
        }
        Ok(Self { intros })
    }
}

impl core::fmt::Display for Tactic
{
    /// The tactic as its splice writes it: `intro(` per introduction, then
    /// `assumption`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        for _intro in 0 .. self.intros {
            f.write_str("intro(")?;
        }
        f.write_str("assumption")?;
        for _intro in 0 .. self.intros {
            f.write_str(")")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
