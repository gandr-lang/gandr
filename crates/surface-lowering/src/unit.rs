//! Units: the sources one lowering reads, laid end to end in the order their
//! imports admit them.
//!
//! # A unit is one module's text per source, end to end
//!
//! A source that imports a sibling is lowered together with it: the sibling's
//! text first, the importer's after it, one tree, one arena. The [`Unit`]
//! records where each source starts in that text and what each of its imports
//! resolved to; the lowering keeps every top-level name in the scope of the
//! source that declares it ([`Container::TopLevel`]) and answers a name a
//! source does not declare from the sources it imports. A source that imports
//! nothing and is imported by nothing is a unit of one, [`Unit::single`],
//! which lowers exactly as a source always has.
//!
//! A unit may hold two sources neither of which imports the other. The walk
//! (`gandr-surface-dispatcher`) lays out a whole import-connected component
//! as one unit, so a source imported by several is lowered once; an editor
//! session lays out one source's import closure. Either way a source sees
//! only the names it declares and the names of the sources it imports.
//!
//! The spans of a unit's tree are the unit's: a source's bytes stand at its
//! start. The faces that render a source subtract its start
//! (`gandr-surface-dispatcher`'s `Step::Source` carries it), so a reader sees
//! each source as it wrote it.
//!
//! One table stays unit-wide, which for the walk is component-wide. The
//! outermost [`Recognition`](crate::namespace::Recognition) scope — the
//! builtins and the module paths — is one per lowering, so a module a sibling
//! declares is recognised by path in its importer, and two sources of one
//! component declaring a module of one name collide there, whether or not
//! either imports the other. It reverses when a unit is a package's
//! component: each source's module paths go under its own scope.
//!
//! # A form's key in its unit names its source
//!
//! A form's [`NodeKey`] is its content digest and a rank, so two
//! byte-identical forms in two sources of one unit share it. The lowering
//! files what it keeps per form — attributes, documentation, a declaration's
//! halves — under a [`UnitKey`]: the source holding the form, then its
//! `NodeKey`. Two members of one component that write one form byte for byte
//! each keep their own expectations and documentation (#596). A face that
//! answers inside one source's own tree, where every form is that source's,
//! reads the `UnitKey`s of that source by [`UnitKey::form`].
//!
//! - Choice: the source beside the key, at the lowering, the one place a unit's
//!   layout is known; the tree keys stay content keys, so a source parsed alone
//!   and the same source laid in a unit name a form alike.
//! - Alternatives: the source mixed into the tree's form digest, which makes a
//!   form's key depend on where its source is laid and so moves every key of a
//!   source an editor re-lays; an occurrence count among identical forms in the
//!   tree, which names a form by what other sources hold.
//! - Reversal: a consumer that needs one form identity across units — reuse of
//!   a source's work when the unit around it changes — files by the `NodeKey`
//!   and projects each unit's keys onto it, as an editor's face does.
//!
//! [`Container::TopLevel`]: crate::Container::TopLevel

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::NodeKey;

/// A source's position in its unit, which is the order the unit admits its
/// sources in: every source after each source it imports.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceIndex(usize);

impl From<usize> for SourceIndex
{
    /// The source at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<SourceIndex> for usize
{
    /// The position `index` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: SourceIndex) -> Self
    {
        index.0
    }
}

impl fmt::Display for SourceIndex
{
    /// Writes the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A form's key in the unit that lays its source out: the source holding the
/// form, then the form's own [`NodeKey`].
///
/// # Specification
/// - requires: nothing; the type is a carrier and admits any pair.
/// - ensures: two keys are equal exactly when their sources and form keys are;
///   the order compares the source first.
/// - provides: the key the lowering files a form's attributes, documentation
///   and declaration halves under, apart for two byte-identical forms of two
///   sources.
/// - fails: never.
/// - panics: none.
/// - executable: none — a carrier with no invariant beyond its fields.
///
/// # Adequacy
/// - hypothesis: L3 — two byte-identical attributed forms in two sources of one
///   unit are filed apart and each settles under its own expectation.
/// - witness: `attribute::tests::two_declarations_keep_separate_entry_lists`
/// - witness: `tests::namespace::one_form_in_two_sources_files_its_attributes_apart_596`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UnitKey
{
    /// The source holding the form.
    source: SourceIndex,
    /// The form's key in its tree.
    form: NodeKey,
}

impl UnitKey
{
    /// The key of the form `form` keys in the source at `source`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: SourceIndex,
        form: NodeKey,
    ) -> Self
    {
        Self { source, form }
    }

    /// The source holding the form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> SourceIndex
    {
        self.source
    }

    /// The form's key in its tree, as the source read alone keys it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> NodeKey
    {
        self.form
    }
}

/// A path import's position among its source's path imports, in the order
/// the source writes them; an import whose address has a scheme takes none.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathImportOrdinal(usize);

impl From<usize> for PathImportOrdinal
{
    /// The path import at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl PathImportOrdinal
{
    /// The path import after this one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next position, saturating at the widest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the second path import of a source answers its second
    ///   target.
    /// - witness: `unit::tests::an_unlaid_import_is_unresolved`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(1_usize))]
    pub const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1_usize))
    }
}

/// What one import of a source names, as the caller that read the unit's
/// sources resolved it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ImportTarget
{
    /// The unit's source at this position, admitted before the importer.
    Source(SourceIndex),
    /// No source the import's root holds and the run could lower: the path
    /// names nothing, names something outside the importer's root, or names
    /// a source refused as a whole.
    Unresolved,
    /// A source whose imports lead back to the importer.
    Cycle,
    /// A module path whose head names nothing among the package's sources and
    /// no dependency its lock records: an alias the package's `dependencies`
    /// may declare and its `gandr.lock` does not yet hold (#533 p3). The import
    /// binds nothing, and a name read through it is refused at that name.
    Unlocked,
}

/// One source of a unit: where its text starts, and what its imports
/// resolved to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnitSource
{
    /// The offset in the unit's text where the source's own text starts.
    start: ByteOffset,
    /// What each import whose address is a path resolved to, in the order
    /// the source writes them; an import whose address has a scheme takes no
    /// entry.
    imports: Vec<ImportTarget>,
}

impl UnitSource
{
    /// The source starting at `start`, its path imports resolved to
    /// `imports` in the order it writes them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        start: ByteOffset,
        imports: Vec<ImportTarget>,
    ) -> Self
    {
        Self { start, imports }
    }

    /// Where the source's own text starts in the unit's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> ByteOffset
    {
        self.start
    }

    /// What its path imports resolved to, in the order it writes them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn imports(&self) -> &[ImportTarget]
    {
        &self.imports
    }
}

/// The sources a lowering reads, in the order it admits them.
///
/// # Specification
/// - requires: the sources start in ascending order, the first at zero, and
///   every [`ImportTarget::Source`] names a source before its importer.
/// - ensures: [`Unit::source_at`] answers the source whose text holds an
///   offset; [`Unit::prelude`] answers the first source exactly when the unit
///   was laid by [`Unit::preluded`].
/// - provides: the layout the lowering scopes top-level names by.
/// - executable: none — a data type; [`Unit::new`] states its check.
///
/// # Adequacy
/// - hypothesis: L3 — a unit of two sources resolves an offset in each to its
///   source and its boundary to the second.
/// - witness: `unit::tests::an_offset_belongs_to_the_source_that_holds_it`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unit
{
    /// The sources, in admission order; never empty.
    sources: Vec<UnitSource>,
    /// The source holding [`crate::prelude::TEXT`], which every other source
    /// imports unqualified without writing it: the first, when the unit lays
    /// one.
    prelude: Option<SourceIndex>,
}

impl Default for Unit
{
    /// [`Unit::single`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::single()
    }
}

/// Why a unit could not be laid out.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnitFault
{
    /// No source was given.
    Empty,
    /// A source does not start after the one before it, or the first does
    /// not start at zero, or, after the prelude, at
    /// [`crate::prelude::base`].
    Unordered(SourceIndex),
    /// An import names a source at or after its importer.
    Forward(SourceIndex),
}

impl Unit
{
    /// The unit of one source, starting at zero, whose path imports resolve
    /// to nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn single() -> Self
    {
        Self {
            sources: Vec::from([UnitSource::new(ByteOffset::from(0_usize), Vec::new())]),
            prelude: None,
        }
    }

    /// The unit of `sources`, in admission order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the unit holds exactly `sources`.
    /// - provides: the layout a caller that read several sources hands the
    ///   lowering.
    /// - fails: [`UnitFault::Empty`] for no source, [`UnitFault::Unordered`]
    ///   for a source not starting after the one before it or a first source
    ///   not at zero, and [`UnitFault::Forward`] for an import naming its
    ///   importer or a later source.
    /// - panics: none.
    ///
    /// # Errors
    /// [`UnitFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ordered unit, an empty one, a second source at the
    ///   first's offset and a backward import each answer exactly.
    /// - witness: `unit::tests::a_unit_is_ordered_and_imports_only_backward`
    #[spec(captures: offered = sources.len(), ensures: |ret| ret.as_ref().map_or(true, |unit| unit.sources.len() == offered))]
    #[inline]
    pub fn new(sources: Vec<UnitSource>) -> Result<Self, UnitFault>
    {
        let Some(first) = sources.first()
        else {
            return Err(UnitFault::Empty);
        };
        if usize::from(first.start) != 0_usize {
            return Err(UnitFault::Unordered(SourceIndex(0_usize)));
        }
        let mut previous = first.start;
        for (position, source) in sources.iter().enumerate() {
            if position > 0_usize && source.start <= previous {
                return Err(UnitFault::Unordered(SourceIndex(position)));
            }
            previous = source.start;
            let forward = source.imports.iter().any(|target| match *target {
                ImportTarget::Source(SourceIndex(imported)) => imported >= position,
                ImportTarget::Unresolved | ImportTarget::Cycle | ImportTarget::Unlocked => false,
            });
            if forward {
                return Err(UnitFault::Forward(SourceIndex(position)));
            }
        }

        Ok(Self {
            sources,
            prelude: None,
        })
    }

    /// The unit of the prelude, then `sources` in admission order: the
    /// prelude's text first, at zero, each of `sources` after it.
    ///
    /// # Specification
    /// - requires: `sources` are laid after [`crate::prelude::TEXT`] and its
    ///   separating newline, and each [`ImportTarget::Source`] among their
    ///   imports counts the prelude as the unit's first source.
    /// - ensures: the unit holds the prelude, starting at zero and importing
    ///   nothing, then exactly `sources`; [`Unit::prelude`] answers the first
    ///   source.
    /// - provides: the layout every program is lowered in, the prelude the
    ///   implicit first import of each of its sources.
    /// - fails: [`UnitFault::Empty`] for no source; [`UnitFault::Unordered`]
    ///   for a first source not starting at [`crate::prelude::base`] and as
    ///   [`Unit::new`] otherwise; [`UnitFault::Forward`] as [`Unit::new`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`UnitFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sources laid after the prelude keep their offsets
    ///   and the first's import of the second's predecessor, and a source laid
    ///   over the prelude's bytes is refused.
    /// - witness: `unit::tests::a_preluded_unit_lays_the_prelude_first`
    #[spec(captures: offered = sources.len(), ensures: |ret| ret.as_ref().map_or(true, |unit| unit.sources.len() == offered.saturating_add(1_usize) && unit.prelude == Some(SourceIndex(0_usize))))]
    #[inline]
    pub fn preluded(sources: Vec<UnitSource>) -> Result<Self, UnitFault>
    {
        let Some(first) = sources.first()
        else {
            return Err(UnitFault::Empty);
        };
        if first.start != crate::prelude::base() {
            return Err(UnitFault::Unordered(SourceIndex(1_usize)));
        }
        let mut laid = Vec::with_capacity(sources.len().saturating_add(1_usize));
        laid.push(UnitSource::new(ByteOffset::from(0_usize), Vec::new()));
        laid.extend(sources);
        let mut unit = Self::new(laid)?;
        unit.prelude = Some(SourceIndex(0_usize));

        Ok(unit)
    }

    /// The source holding the prelude, when the unit lays one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn prelude(&self) -> Option<SourceIndex>
    {
        self.prelude
    }

    /// The unit of every source but the last, the prelude kept: the closure a
    /// document laid last is judged after.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sources before the last, in order, and the prelude when
    ///   the unit lays one and it stands among them.
    /// - provides: the unit an editor lowers a document's closure in once.
    /// - fails: [`UnitFault::Empty`] for a unit of one source.
    /// - panics: none.
    ///
    /// # Errors
    /// [`UnitFault::Empty`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a preluded unit of a document alone leaves the
    ///   prelude, still marked, and a unit of one source leaves nothing.
    /// - witness: `unit::tests::a_preluded_unit_lays_the_prelude_first`
    #[spec(ensures: |ret| ret.as_ref().map_or(self.sources.len() <= 1_usize, |closure| closure.sources.len() == self.sources.len().saturating_sub(1_usize)))]
    #[inline]
    pub fn before_last(&self) -> Result<Self, UnitFault>
    {
        let kept = self.sources.len().saturating_sub(1_usize);
        let sources = self.sources.get(.. kept).unwrap_or_default();
        if sources.is_empty() {
            return Err(UnitFault::Empty);
        }
        Ok(Self {
            sources: sources.to_vec(),
            prelude: self.prelude.filter(|prelude| prelude.0 < kept),
        })
    }

    /// The sources, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sources(&self) -> &[UnitSource]
    {
        &self.sources
    }

    /// The source whose text holds `offset`: the last source starting at or
    /// before it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the greatest position whose source starts at or before
    ///   `offset`; the first source for an offset before every start.
    /// - provides: the source a top-level form, a declaration or a site belongs
    ///   to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — offsets inside each of two sources and at the second
    ///   one's start resolve exactly.
    /// - witness: `unit::tests::an_offset_belongs_to_the_source_that_holds_it`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| self.sources.get(ret.0).is_some_and(|held| held.start <= offset || ret.0 == 0_usize)
        && self.sources.get(ret.0.saturating_add(1_usize)).is_none_or(|next| next.start > offset))]
    pub fn source_at(
        &self,
        offset: ByteOffset,
    ) -> SourceIndex
    {
        let after = self
            .sources
            .partition_point(|source| source.start <= offset);

        SourceIndex(after.saturating_sub(1_usize))
    }

    /// What the `ordinal`-th path import of `source` resolved to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry the caller laid out; [`ImportTarget::Unresolved`]
    ///   for an import the caller did not resolve, which is every path import
    ///   of a [`Unit::single`].
    /// - provides: the target the lowering binds an import to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a laid-out import answers its target and an import
    ///   past the layout answers unresolved.
    /// - witness: `unit::tests::an_unlaid_import_is_unresolved`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.sources.get(source.0)
        .and_then(|held| held.imports.get(ordinal.0).copied())
        .unwrap_or(ImportTarget::Unresolved))]
    pub fn target(
        &self,
        source: SourceIndex,
        ordinal: PathImportOrdinal,
    ) -> ImportTarget
    {
        self.sources
            .get(source.0)
            .and_then(|held| held.imports.get(ordinal.0).copied())
            .unwrap_or(ImportTarget::Unresolved)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_surface_syntax::ByteOffset;

    use super::ImportTarget;
    use super::PathImportOrdinal;
    use super::SourceIndex;
    use super::Unit;
    use super::UnitFault;
    use super::UnitSource;

    /// Two sources, the second starting at ten and importing the first.
    ///
    /// # Specification
    /// trivial.
    fn two() -> Unit
    {
        Unit::new(Vec::from([
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(
                ByteOffset::from(10_usize),
                Vec::from([ImportTarget::Source(SourceIndex::from(0_usize))]),
            ),
        ]))
        .unwrap()
    }

    #[test]
    fn an_offset_belongs_to_the_source_that_holds_it()
    {
        let unit = two();
        for (offset, source) in [(0_usize, 0_usize), (9, 0), (10, 1), (40, 1)] {
            assert_eq!(
                unit.source_at(ByteOffset::from(offset)),
                SourceIndex::from(source),
                "offset {offset}"
            );
        }
    }

    #[test]
    fn a_unit_is_ordered_and_imports_only_backward()
    {
        assert_eq!(two().sources().len(), 2_usize);
        assert_eq!(Unit::new(Vec::new()), Err(UnitFault::Empty));
        assert_eq!(
            Unit::new(Vec::from([
                UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
                UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            ])),
            Err(UnitFault::Unordered(SourceIndex::from(1_usize)))
        );
        assert_eq!(
            Unit::new(Vec::from([UnitSource::new(
                ByteOffset::from(0_usize),
                Vec::from([ImportTarget::Source(SourceIndex::from(0_usize))]),
            )])),
            Err(UnitFault::Forward(SourceIndex::from(0_usize)))
        );
    }

    #[test]
    fn an_unlaid_import_is_unresolved()
    {
        let unit = two();
        let first = PathImportOrdinal::from(0_usize);
        assert_eq!(
            unit.target(SourceIndex::from(1_usize), first),
            ImportTarget::Source(SourceIndex::from(0_usize))
        );
        assert_eq!(
            unit.target(SourceIndex::from(1_usize), first.next()),
            ImportTarget::Unresolved
        );
        assert_eq!(
            Unit::single().target(SourceIndex::from(0_usize), first),
            ImportTarget::Unresolved
        );
    }

    #[test]
    fn a_preluded_unit_lays_the_prelude_first()
    {
        let text = "0123456789second";
        let (laid, unit) =
            crate::prelude::lay(gandr_surface_syntax::SourceText::from(text), &two()).unwrap();
        let base = usize::from(crate::prelude::base());
        assert_eq!(
            laid.get(.. base),
            Some(alloc::format!("{}\n", crate::prelude::TEXT).as_str())
        );
        assert_eq!(laid.get(base ..), Some(text));
        assert_eq!(unit.prelude(), Some(SourceIndex::from(0_usize)));
        assert_eq!(unit.sources().len(), 3_usize);
        for (offset, source) in [(0_usize, 0_usize), (base - 1, 0), (base, 1), (base + 10, 2)] {
            assert_eq!(
                unit.source_at(ByteOffset::from(offset)),
                SourceIndex::from(source),
                "offset {offset}"
            );
        }
        assert_eq!(
            unit.target(SourceIndex::from(2_usize), PathImportOrdinal::from(0_usize)),
            ImportTarget::Source(SourceIndex::from(1_usize)),
            "the import of the first source moves with it"
        );
        assert_eq!(two().prelude(), None, "a unit laid alone has no prelude");
        assert_eq!(
            Unit::preluded(Vec::from([UnitSource::new(
                ByteOffset::from(1_usize),
                Vec::new()
            )])),
            Err(UnitFault::Unordered(SourceIndex::from(1_usize))),
            "a source over the prelude's bytes"
        );
        assert_eq!(Unit::preluded(Vec::new()), Err(UnitFault::Empty));
        let closure = unit.before_last().unwrap();
        assert_eq!(
            (closure.sources().len(), closure.prelude()),
            (2_usize, Some(SourceIndex::from(0_usize))),
            "the closure before the importer keeps the prelude"
        );
        assert_eq!(Unit::single().before_last(), Err(UnitFault::Empty));
    }
}
