//! What a condition run reports: holds over its cases, or fails at the
//! first case in enumeration order, which is the smallest by total size.

use alloc::vec::Vec;
use core::fmt;

use quenchant_shape::shape::Maybe;

use crate::map::SiteMap;
use crate::shape::Shape;

wrapper! {
    /// How many cases a condition examined.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CaseCount(usize);
}

quenchant_shape::reason_enum! {
    /// Why an outcome carries no counter-example.
    pub mod outcome_witness {
        /// The reason no witness is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The condition holds over every case.
            Held,
        }
    }
}

/// Whether a condition held.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Verdict
{
    /// It held over every case at the bound.
    Holds,
    /// Some case broke it.
    Fails,
}

impl fmt::Display for Verdict
{
    /// Writes `holds` or `fails`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Holds => "holds",
            | Self::Fails => "fails",
        })
    }
}

/// A condition's result over a finite site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome<Witness>
{
    /// Every case passed.
    Holds
    {
        /// How many cases were examined.
        cases: CaseCount,
    },
    /// A case failed; the search stopped there.
    Fails
    {
        /// How many cases were examined, the failing one included.
        cases: CaseCount,
        /// The failing case, the smallest in enumeration order.
        witness: Witness,
    },
}

impl<Witness> Outcome<Witness>
{
    /// Whether the condition held.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> Verdict
    {
        match *self {
            | Self::Holds { .. } => Verdict::Holds,
            | Self::Fails { .. } => Verdict::Fails,
        }
    }

    /// How many cases were examined.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cases(&self) -> CaseCount
    {
        match *self {
            | Self::Holds { cases } | Self::Fails { cases, .. } => cases,
        }
    }

    /// The counter-example, when the condition failed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn witness(&self) -> Maybe<&Witness, outcome_witness::Absent>
    {
        match *self {
            | Self::Holds { .. } => Maybe::Absent(outcome_witness::Absent::Held),
            | Self::Fails { ref witness, .. } => Maybe::Present(witness),
        }
    }
}

impl<Witness> fmt::Display for Outcome<Witness>
where
    Witness: fmt::Display,
{
    /// Writes the verdict, the case count and any counter-example.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Holds { cases } => write!(f, "holds over {} cases", cases.0),
            | Self::Fails { cases, ref witness } => {
                write!(f, "fails at case {}: {witness}", cases.0)
            },
        }
    }
}

/// A running count of examined cases.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Tally(usize);

impl Tally
{
    /// Counts one more case.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn count(&mut self)
    {
        self.0 = self.0.saturating_add(1);
    }

    /// The outcome when every case passed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn holds<Witness>(self) -> Outcome<Witness>
    {
        Outcome::Holds {
            cases: CaseCount(self.0),
        }
    }

    /// The outcome at a failing case.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fails<Witness>(
        self,
        witness: Witness,
    ) -> Outcome<Witness>
    {
        Outcome::Fails {
            cases: CaseCount(self.0),
            witness,
        }
    }
}

/// One map with its source and target, as a counter-example names it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MapCase
{
    /// The map's source.
    source: Shape,
    /// The map's target.
    target: Shape,
    /// The map.
    map: SiteMap,
}

impl MapCase
{
    /// The case of `map` from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: Shape,
        target: Shape,
        map: SiteMap,
    ) -> Self
    {
        Self {
            source,
            target,
            map,
        }
    }

    /// The source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> &Shape
    {
        &self.source
    }

    /// The target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> &Shape
    {
        &self.target
    }

    /// The map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn map(&self) -> &SiteMap
    {
        &self.map
    }
}

impl fmt::Display for MapCase
{
    /// Writes `source → target by map`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} → {} by {}", self.source, self.target, self.map)
    }
}

/// Several maps a counter-example names together: a composable pair, a
/// span, a cycle or a chain.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Chain
{
    /// The maps, in the order the condition names them.
    links: Vec<MapCase>,
}

impl Chain
{
    /// The chain of `links`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(links: Vec<MapCase>) -> Self
    {
        Self { links }
    }

    /// The maps, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn links(&self) -> &[MapCase]
    {
        &self.links
    }
}

impl fmt::Display for Chain
{
    /// Writes the maps separated by ` ; `.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for (index, link) in self.links.iter().enumerate() {
            let separator = if index == 0 { "" } else { " ; " };
            write!(f, "{separator}{link}")?;
        }
        Ok(())
    }
}
