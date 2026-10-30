//! Unbiased composition as the core holds it: the stratum a composite is made
//! at and the shape its cells fill.
//!
//! [`Value::Compose`] is `compose[n, k](Γ, d)`. Its [`Composite`] is the
//! [`Stratum`] `n` and `k` write and the [`Pasting`] Γ names. The cells of `d`
//! are the node's children in vertex order, and so is the composite the
//! lowering realises from them: the left-nested fold `(c₁ then c₂) then …`,
//! whose every motive fixes the first cell's start. `gandr-core-checker`'s
//! `compose` module certifies the stratum, reads Γ as a shape of it and checks
//! that the cells fill it; evaluation and the kernel read the realisation.
//!
//! # Decisions
//!
//! - **The realisation is a child.** A composite of paths is a transport per
//!   cell, and each motive names the carrier and the start, which only a typed
//!   reading knows. The lowering reads them as it reads them for `then`, so the
//!   node carries a term evaluation runs and the bridge erases to, and nothing
//!   downstream rebuilds it. The alternative, a realisation the checker records
//!   by node, leaves evaluation with a node it cannot run. Reversal: a core
//!   composition former of its own in both checkers and the kernel.
//! - **Γ is named, not read off the cells.** At dimension one the chain is the
//!   cells' count, but a shape above it is not, so the former takes the shape
//!   the wreath's levels extend. Reversal: none at dimension one.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: unbiased
//!   composition is a term former at a certified stratum, and the node holds
//!   the cells' left-nested fold as its realisation.
//!
//! [`Value::Compose`]: crate::Value::Compose

use anodized::spec;

use crate::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::ua::Stratum;

#[cfg(test)]
mod tests;

/// How many cells a pasting shape holds: its vertex count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellCount(usize);

impl From<usize> for CellCount
{
    /// The count of `cells`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cells: usize) -> Self
    {
        Self(cells)
    }
}

impl From<CellCount> for usize
{
    /// The number of cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: CellCount) -> Self
    {
        count.0
    }
}

/// Γ in `compose[n, k](Γ, d)`: a shape of the site's chain sub-site.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Pasting
{
    /// `chain(m)`: the chain of `m` composable 1-cells.
    Chain
    {
        /// Its cell count, `m`.
        cells: CellCount,
    },
}

/// The stratum a composite is made at and the shape it composes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Composite
{
    /// The degree and the catalogue bound written in the head.
    pub stratum: Stratum,
    /// The shape its cells fill.
    pub pasting: Pasting,
}

/// The composite of `cells` at `composite`, its realisation the left-nested
/// `then` fold over `carrier` from `start`.
///
/// # Specification
/// - requires: `carrier` and `start` are read in the context the composite
///   stands in, `start` being the first cell's left endpoint.
/// - ensures: a [`Value::Compose`] holding `cells` in order, its realisation
///   [`crate::identity::then`] of the composite so far and the next cell for
///   each cell past the first, the first cell returned for one cell, and the
///   reflexivity at `start` returned for none.
/// - provides: the one realisation the lowering and the tests build.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — three cells realise as the transport of the first two's
///   composite along the third; one cell realises as itself returned.
/// - witness: `compose::tests::three_cells_realise_as_the_left_nested_fold`
#[spec(ensures: |ret| matches!(arena.value(ret), Some(&Value::Compose { composite: held, cells: ref held_cells, realised })
    if held == composite && **held_cells == *cells
        && match cells.len() {
            0 | 1 => matches!(arena.computation(realised), Some(&Computation::Return(_))),
            _ => matches!(arena.computation(realised), Some(&Computation::PathTransport { path, .. }) if cells.last() == Some(&path)),
        }))]
#[inline]
#[must_use]
pub fn compose(
    arena: &mut CoreArena,
    composite: Composite,
    (carrier, start): (ValueTypeId, ValueId),
    cells: &[ValueId],
) -> ValueId
{
    let mut written = cells.iter().copied();
    let realised = if let Some(first) = written.next() {
        let mut realised = arena.computation_return(first);
        let mut sofar = first;
        for cell in written {
            realised = crate::identity::then(arena, carrier, start, sofar, cell);
            sofar = arena.value_returned(realised);
        }
        realised
    }
    else {
        let reflexive = arena.value_here(start);
        arena.computation_return(reflexive)
    };
    arena.value_compose(composite, cells.into(), realised)
}
