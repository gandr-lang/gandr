//! The definitions a run unfolds: what each constant stands for, by its
//! admission position. A transparent constant's focused, closed value is
//! evaluated where the constant is met; an opaque one — owed or refused — is
//! carried as itself, and observing it stops the run at the constant.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;

use crate::il::ProducerId;

/// What a constant stands for when a run meets it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Definition
{
    /// A definition with a body: its focused value, closed.
    Transparent(ProducerId),
    /// A declaration with no body to run, owed or refused, which a run
    /// carries as itself.
    Opaque,
}

/// The definitions a run unfolds, by admission position.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Definitions
{
    /// Each constant's definition, at its admission position.
    entries: Vec<Definition>,
}

impl Definitions
{
    /// No definitions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Admit the next definition.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the definition is admitted at the next position, which is
    ///   returned.
    /// - provides: the one way a constant gets a definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the admitted definition is read back at the position
    ///   returned, and the next admission takes the position after it.
    /// - witness: `definitions::tests::each_admission_takes_the_next_position`
    #[inline]
    #[spec(
        captures: [entry = self.entries.len()],
        ensures: |ret| usize::from(ret) == entry && entry.checked_add(1) == Some(self.entries.len())
            && self.entries.get(entry) == Some(&definition),
    )]
    pub fn push(
        &mut self,
        definition: Definition,
    ) -> ConstantIndex
    {
        let position = ConstantIndex::from(self.entries.len());
        self.entries.push(definition);
        position
    }

    /// The definition admitted at a position, or `None`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        constant: ConstantIndex,
    ) -> Option<Definition>
    {
        self.entries.get(usize::from(constant)).copied()
    }

    /// How many definitions are admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> crate::NodeCount
    {
        crate::NodeCount::from(self.entries.len())
    }
}

#[cfg(test)]
mod tests;
