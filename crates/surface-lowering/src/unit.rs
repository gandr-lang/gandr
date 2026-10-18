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
///   offset.
/// - provides: the layout the lowering scopes top-level names by.
/// - executable: none — a data type; [`Unit::new`] states its check.
///
/// # Adequacy
/// - hypothesis: L3 — a unit of two sources resolves an offset in each to its
///   source and its boundary to the second.
/// - witness: `unit::tests::an_offset_belongs_to_the_source_that_holds_it`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unit
{
    /// The sources, in admission order; never empty.
    sources: Vec<UnitSource>,
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
    /// not start at zero.
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
                ImportTarget::Unresolved | ImportTarget::Cycle => false,
            });
            if forward {
                return Err(UnitFault::Forward(SourceIndex(position)));
            }
        }

        Ok(Self { sources })
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
}
