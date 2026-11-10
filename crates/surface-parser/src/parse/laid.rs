//! The laid join: a join that takes a run's forms up whole from the parse
//! before it, as slices of that parse's tree ([`TreeSlice`]), where the run and
//! the run before it are the ones that parse molded.
//!
//! The region of a run is its bytes, from its first token to the next run's
//! first token. Its slice is the root children whose start lies in the region,
//! each with the block of its descendants. The split cuts before each
//! declaration head, so a `///` run that documents the first form of a run lies
//! at the end of the run before it, and the form holds it: the slice counts its
//! spans from the start of the run before it ([`LaidUnit`]).
//!
//! A unit is clean when its fold never touched its stand-in and its slope ends
//! settled ([`ParkedUnit::cleanness`]). The join takes a run up as a block when
//! the caller gives a laid region for it, which the caller gives only while the
//! run before it is the one the region was laid after, and when the run, the
//! run before it and the run after it are clean. The other runs join, in run
//! order, onto one melder each stretch of them: the stretch resumes the
//! checkpoint of the block before it, its context, and it closes before a
//! block only when its slope settles. The stretch's commit is checked three
//! ways, and the join falls back to the whole join when one fails:
//!
//! |Check|Failure means|
//! |---|---|
//! |no fold or collapse of the stretch touched the context's cells|a fold reached the context's forms|
//! |the stretch's root children in the context's region are the context slice's, by label and span|a comment of the context went elsewhere|
//! |each comment the next block's first form holds from the stretch's text stands at the stretch's root, and no root child starts past the stretch's text|the regions do not partition the root|
//!
//! The tree is then assembled from the slices ([`SyntaxTree::assembled`]), with
//! one copy of each node, and committed as the whole join commits. A slice is
//! laid for the next parse only where no later fold or collapse touched the
//! run's cells and the run's own seam held, so a slice holds exactly the
//! molding of its own unit and the comments the run before it gives.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteLength;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ChildCount;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_surface_syntax::TreeSlice;

use super::FormJoin;
use super::FormSplit;
use super::ParseResult;
use super::ordered;
use super::place;
use crate::FormUnit;
use crate::MeldError;
use crate::MeldState;
use crate::Molder;
use crate::ParkedUnit;
use crate::TokenRun;
use crate::UnitBase;
use crate::UnitSeam;
use crate::meld::SlopeHeight;
use crate::meld::UnitCleanness;
use crate::meld::UnitEnding;
use crate::oblig::ObligationInstance;

/// What a parse laid out for one run: the slice of the run's region and the
/// obligations whose spans start in the region, each counted from the start of
/// the run before it.
///
/// # Specification
/// - requires: constructed by [`FormSplit::join_laid`].
/// - ensures: the slice holds the root children whose start lies in the region,
///   with the blocks of their descendants; the obligations are the parse's
///   before its repairs were placed.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the laid join
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source, joined again from the regions its
///   own parse laid, and edited at its middle boundary, parses whole; a region
///   that kept a form another unit's fold reached, or lost its obligations,
///   changes a tree.
/// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
/// - witness: `parse::tests::hostile_edits_join_laid_as_whole`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LaidUnit
{
    /// The region's root children with their blocks.
    slice: TreeSlice,
    /// The obligations whose spans start in the region.
    obligations: Vec<ObligationInstance>,
}

/// One run's unit as a laid join takes it: the unit parked under the run's
/// identity, the unit itself when this revision molded it, and the region the
/// last parse laid out for the run.
///
/// # Specification
/// - requires: the parked unit has the run's identity and was molded over the
///   join's grammar; the unit, when given, is the one parked; the laid region,
///   when given, was laid for a run of this identity after a run of the
///   identity the run before this one has.
/// - ensures: holds what the join reads of one run.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the laid join
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`LaidUnit`].
/// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
pub struct JoinPiece<'pbg, 'held>
{
    /// The unit parked under the run's identity.
    parked: &'held ParkedUnit,
    /// The unit, when this revision molded it.
    unit: Option<FormUnit<'pbg>>,
    /// The region the last parse laid out for the run.
    laid: Option<&'held LaidUnit>,
}

impl<'pbg, 'held> JoinPiece<'pbg, 'held>
{
    /// The piece of one run: `parked`, the unit `unit` when this revision
    /// molded it, and the region `laid`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        parked: &'held ParkedUnit,
        unit: Option<FormUnit<'pbg>>,
        laid: Option<&'held LaidUnit>,
    ) -> Self
    {
        Self { parked, unit, laid }
    }
}

/// A laid join's parse, what it laid out for each run, and how many runs it
/// took up whole.
///
/// # Specification
/// - requires: constructed by [`FormSplit::join_laid`].
/// - ensures: one laid entry per run, in run order: a region for the next
///   parse, or nothing where the run keeps the region it had or has none.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the laid join
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`LaidUnit`].
/// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
#[derive(Debug)]
pub struct LaidJoin<'source>
{
    /// The joined parse and its seams.
    join: FormJoin<'source>,
    /// Per run, the region laid for the next parse.
    laid: Vec<Option<LaidUnit>>,
    /// How many runs the join took up as blocks.
    kept: RunCount,
}

impl<'source> LaidJoin<'source>
{
    /// The joined parse and its seams.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn join(&self) -> &FormJoin<'source>
    {
        &self.join
    }

    /// How many runs the join took up as blocks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kept(&self) -> RunCount
    {
        self.kept
    }

    /// Consume the join: the parse and its seams, and per run the region laid
    /// for the next parse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (FormJoin<'source>, Vec<Option<LaidUnit>>)
    {
        (self.join, self.laid)
    }
}

/// A number of runs of one split.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a count; a laid join gives at most its split's runs.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the laid join
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`LaidUnit`].
/// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RunCount(usize);

impl From<RunCount> for usize
{
    /// Read the run count back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: RunCount) -> Self
    {
        count.0
    }
}

/// How one unit met the state it joined.
#[derive(Clone, Copy, Debug)]
struct Met
{
    /// How the unit's seam stood.
    seam: UnitSeam,
    /// The slope's height after the unit joined: its cells lie below.
    ceiling: SlopeHeight,
    /// The lowest slope position the join touched.
    touched: SlopeHeight,
}

/// The position of a run among its split's runs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RunAt(usize);

impl RunAt
{
    /// The run after this one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }

    /// The run before this one, or nothing for the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn before(self) -> Option<Self>
    {
        self.0.checked_sub(1).map(Self)
    }
}

/// How the join takes a run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Taking
{
    /// Up whole, as the region the last parse laid for it.
    Block,
    /// Onto a melder, in a stretch.
    Stretched,
}

/// Whether the join lays a run's region for the next parse.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Laying
{
    /// The run kept its own molding to the commit.
    Lay,
    /// The run's seam broke, or a later fold reached its cells.
    Skip,
}

/// Where each run's region starts in the source, and then the source's end.
#[repr(transparent)]
struct Regions
{
    /// One start per run, the first zero, then the source's length.
    starts: Vec<ByteOffset>,
}

impl Regions
{
    /// Where `run`'s region starts: the source's end for the run past the
    /// last, and zero past that.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn start(
        &self,
        run: RunAt,
    ) -> ByteOffset
    {
        self.starts
            .get(run.0)
            .copied()
            .unwrap_or_else(|| ByteOffset::from(0_usize))
    }

    /// The anchor `run`'s slice counts from: the start of the run before it,
    /// and zero for the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn anchor(
        &self,
        run: RunAt,
    ) -> ByteOffset
    {
        run.before()
            .map_or_else(|| ByteOffset::from(0_usize), |before| self.start(before))
    }
}

/// A stretch of runs that the join molds onto one melder.
#[derive(Clone, Copy, Debug)]
struct Stretch
{
    /// The run before the stretch, whose checkpoint the stretch resumes.
    context: Option<RunAt>,
    /// The stretch's first run.
    first: RunAt,
    /// The run after the stretch's last.
    end: RunAt,
    /// Where the stretch's text starts in the source.
    origin: ByteOffset,
}

/// A stretch's commit, checked: what it cut for each member, and which of
/// those to lay for the next parse.
type Cut = (Vec<Option<LaidUnit>>, Vec<Laying>);

impl<'source> FormSplit<'source>
{
    /// Join `pieces`, one per run in run order, taking up as a block each run
    /// whose laid region still holds, and commit the source's parse.
    ///
    /// # Specification
    /// - requires: `pieces` are this split's, one per run, in run order, over
    ///   `molder`'s grammar.
    /// - ensures: the parse equals [`parse`](fn@crate::parse) of the source;
    ///   the seams are how each unit met the state before it, and a run taken
    ///   up as a block meets it joined; one laid entry per run.
    /// - provides: the parse of an edited revision at the cost of the forms the
    ///   edit reached and one copy of every node.
    /// - fails: [`MeldError`] when the commit's arena cannot be built.
    /// - panics: none.
    /// - intension: a run taken up as a block is neither resumed nor replayed;
    ///   a stretch resumes one checkpoint, its context's.
    ///
    /// # Errors
    /// The commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source, joined again from the regions
    ///   its own parse laid, and edited at its middle boundary, parses whole,
    ///   and hostile sources edited at one fragment do; a join that took up an
    ///   unclean unit, skipped a check or laid a region another fold reached
    ///   changes a tree or an obligation.
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    /// - witness: `parse::tests::hostile_edits_join_laid_as_whole`
    #[inline]
    #[spec(captures: before = pieces.len(),
        ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|joined| joined.join.seams.len() == before
            && joined.laid.len() == before && joined.kept.0 <= before))]
    pub fn join_laid<'pbg>(
        &self,
        molder: &mut Molder<'pbg>,
        mut pieces: Vec<JoinPiece<'pbg, '_>>,
    ) -> Result<LaidJoin<'source>, MeldError>
    {
        let regions = self.regions();
        let clean: Vec<UnitCleanness> = pieces
            .iter()
            .map(|piece| piece.parked.cleanness())
            .collect();
        let is_clean = |at: usize| {
            clean
                .get(at)
                .is_none_or(|&held| held == UnitCleanness::Clean)
        };
        let mut taking: Vec<Taking> = pieces
            .iter()
            .enumerate()
            .map(|(at, piece)| {
                let before = at.checked_sub(1).is_none_or(is_clean);
                if piece.laid.is_some() && is_clean(at) && before && is_clean(at.saturating_add(1))
                {
                    Taking::Block
                }
                else {
                    Taking::Stretched
                }
            })
            .collect();
        if pieces.len() == self.runs.len()
            && taking.contains(&Taking::Block)
            && let Some(joined) = self.join_blocks(molder, &mut pieces, &mut taking, &regions)?
        {
            return Ok(joined);
        }
        self.join_whole(molder, pieces, &regions)
    }

    /// Where each run's region starts in the source, and then the source's
    /// end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one start per run, the first zero, then the source's length.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormSplit::join_laid`].
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    #[spec(ensures: |ret| ret.starts.len() == self.runs.len().saturating_add(1))]
    fn regions(&self) -> Regions
    {
        let tokens = self.labeling.tokens();
        let end = <&str>::from(self.source).len();
        let mut starts = Vec::with_capacity(self.runs.len().saturating_add(1));
        starts.extend(self.runs.iter().map(|run| {
            if usize::from(run.start()) == 0 {
                ByteOffset::from(0_usize)
            }
            else {
                ByteOffset::from(
                    tokens
                        .get(usize::from(run.start()))
                        .map_or(end, |token| usize::try_from(token.start).unwrap_or(end)),
                )
            }
        }));
        starts.push(ByteOffset::from(end));
        Regions { starts }
    }

    /// Join `unit`, `piece`'s unit or its parked unit taken up for `run`, to
    /// `state`, and say how it met the state.
    ///
    /// # Specification
    /// - requires: as [`Molder::join_unit`].
    /// - ensures: the seam, the slope's height after the join, and the lowest
    ///   slope position the join touched.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the join.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormSplit::join_laid`].
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    fn join_one<'pbg>(
        &self,
        molder: &mut Molder<'pbg>,
        state: &mut MeldState<'pbg>,
        piece: &mut JoinPiece<'pbg, '_>,
        run: TokenRun,
    ) -> Met
    {
        let pbg = molder.pbg();
        let unit = piece
            .unit
            .take()
            .unwrap_or_else(|| FormUnit::resume(pbg, run, piece.parked));
        let _before = state.take_low_water();
        let seam = molder.join_unit(state, unit, self.labeling.tokens(), self.source);
        let touched = state.take_low_water();
        Met {
            seam,
            ceiling: state.slope_height(),
            touched,
        }
    }

    /// Join every piece onto one melder and commit, as
    /// [`join`](Self::join) does, and lay each run whose molding no later
    /// fold reached.
    ///
    /// # Specification
    /// - requires: as [`FormSplit::join_laid`].
    /// - ensures: the whole join's parse and seams; a laid region for each run
    ///   whose seam held and whose cells no later join or the collapse touched,
    ///   nothing for the others; no run taken up as a block.
    /// - fails: the commit's [`MeldError`].
    /// - panics: none.
    /// - executable: none — the clause restates the join.
    ///
    /// # Errors
    /// The commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormSplit::join_laid`].
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    fn join_whole<'pbg>(
        &self,
        molder: &mut Molder<'pbg>,
        pieces: Vec<JoinPiece<'pbg, '_>>,
        regions: &Regions,
    ) -> Result<LaidJoin<'source>, MeldError>
    {
        let pbg = molder.pbg();
        let mut whole = MeldState::new(pbg);
        // The joined state reserves the room of the whole stream once.
        whole.reserve_for(self.labeling.tokens());
        let mut met = Vec::with_capacity(pieces.len());
        for (mut piece, &run) in pieces.into_iter().zip(&self.runs) {
            met.push(self.join_one(molder, &mut whole, &mut piece, run));
        }
        let (tree, mut obligations, collapse) = whole.commit_reached(self.source)?;
        let wanted = kept_molding(&met, collapse);
        let stretch = Stretch {
            context: None,
            first: RunAt(0),
            end: RunAt(met.len()),
            origin: ByteOffset::from(0_usize),
        };
        let laid = self.cut(&tree, &obligations, stretch, &[], &wanted, regions);
        ordered(&mut obligations);
        let result = place::placed(pbg, ParseResult { tree, obligations });
        Ok(LaidJoin {
            join: FormJoin {
                result,
                seams: met.iter().map(|unit| unit.seam).collect(),
            },
            laid,
            kept: RunCount(0),
        })
    }

    /// Join the runs that are not blocks in stretches, check each stretch's
    /// commit, and assemble the tree from the blocks' and the stretches'
    /// slices; nothing when a check fails.
    ///
    /// # Specification
    /// - requires: as [`FormSplit::join_laid`]; `taking` marks the runs to take
    ///   up whole, each with a laid region.
    /// - ensures: on a parse, the one the whole join commits; a block a stretch
    ///   before it did not settle is joined into the stretch, and `taking`
    ///   marks it stretched; nothing when a check fails.
    /// - fails: a stretch commit's [`MeldError`].
    /// - panics: none.
    /// - executable: none — the clause restates the stretches.
    ///
    /// # Errors
    /// A stretch commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormSplit::join_laid`].
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    fn join_blocks<'pbg>(
        &self,
        molder: &mut Molder<'pbg>,
        pieces: &mut [JoinPiece<'pbg, '_>],
        taking: &mut [Taking],
        regions: &Regions,
    ) -> Result<Option<LaidJoin<'source>>, MeldError>
    {
        let pbg = molder.pbg();
        let count = pieces.len();
        let mut fresh: Vec<Option<LaidUnit>> = core::iter::repeat_n(None, count).collect();
        let mut lay = alloc::vec![Laying::Skip; count];
        let mut seams = alloc::vec![UnitSeam::Joined; count];
        let mut met = Vec::new();
        let mut at = 0_usize;
        while at < count {
            if taking.get(at) == Some(&Taking::Block) {
                at = at.saturating_add(1);
                continue;
            }
            let context = RunAt(at).before();
            let origin =
                context.map_or_else(|| ByteOffset::from(0_usize), |run| regions.start(run));
            let mut state = context.and_then(|run| pieces.get(run.0)).map_or_else(
                || MeldState::new(pbg),
                |piece| MeldState::resume(pbg, piece.parked.checkpoint()),
            );
            let floor = state.slope_height();
            let first = at;
            met.clear();
            while let (Some(piece), Some(&run)) = (pieces.get_mut(at), self.runs.get(at)) {
                met.push(self.join_one(molder, &mut state, piece, run));
                at = at.saturating_add(1);
                match taking.get_mut(at) {
                    Some(&mut Taking::Block) if state.ending() == UnitEnding::Settled => break,
                    Some(take) => *take = Taking::Stretched,
                    None => break,
                }
            }
            let end = regions.start(RunAt(at));
            let text = <&str>::from(self.source)
                .get(usize::from(origin) .. usize::from(end))
                .unwrap_or_default();
            let (tree, obligations, collapse) = state.commit_reached(SourceText::from(text))?;
            let reached = met
                .iter()
                .map(|met| met.touched)
                .fold(collapse, SlopeHeight::min);
            if reached < floor {
                return Ok(None);
            }
            let stretch = Stretch {
                context,
                first: RunAt(first),
                end: RunAt(at),
                origin,
            };
            let Some((cut, wanted)) = self.checked_stretch(
                (&tree, &obligations, &met, collapse),
                pieces,
                stretch,
                regions,
            )
            else {
                return Ok(None);
            };
            for ((run, laid), wanted) in (first .. at).zip(cut).zip(wanted) {
                if let Some(slot) = fresh.get_mut(run) {
                    *slot = laid;
                }
                if let Some(flag) = lay.get_mut(run) {
                    *flag = wanted;
                }
            }
            for (run, unit) in (first ..).zip(&met) {
                if let Some(seam) = seams.get_mut(run) {
                    *seam = unit.seam;
                }
            }
        }
        let mut obligations = Vec::new();
        let mut laid_out = Vec::with_capacity(count);
        for (run, (piece, own)) in pieces.iter().zip(&fresh).enumerate() {
            let held = if taking.get(run) == Some(&Taking::Block) {
                piece.laid
            }
            else {
                own.as_ref()
            };
            let Some(held) = held
            else {
                return Ok(None);
            };
            let anchor = regions.anchor(RunAt(run));
            let by = ByteLength::from(usize::from(anchor));
            obligations.extend(
                held.obligations
                    .iter()
                    .map(|owed| ObligationInstance::new(owed.class, owed.span.shifted(by))),
            );
            laid_out.push((&held.slice, anchor));
        }
        let Ok(tree) = SyntaxTree::assembled(self.source, pbg.fingerprint(), &laid_out)
        else {
            return Ok(None);
        };
        ordered(&mut obligations);
        let result = place::placed(pbg, ParseResult { tree, obligations });
        let kept = RunCount(taking.iter().filter(|&&take| take == Taking::Block).count());
        let laid = fresh
            .into_iter()
            .zip(lay)
            .map(|(laid, wanted)| laid.filter(|_| wanted == Laying::Lay))
            .collect();
        Ok(Some(LaidJoin {
            join: FormJoin { result, seams },
            laid,
            kept,
        }))
    }

    /// Check a stretch's commit against its context and the block after it,
    /// and cut each member's region out of it.
    ///
    /// # Specification
    /// - requires: `tree` and `obligations` are the commit of `stretch`,
    ///   resumed from the checkpoint of its context, over the text from its
    ///   origin; `met` is how each member met the stretch, and `collapse` how
    ///   far the commit's collapse reached.
    /// - ensures: nothing when the stretch's root children in the context's
    ///   region are not the context slice's by label and span, when a comment
    ///   the next block's first form holds from the stretch's text is not at
    ///   the stretch's root, or when a root child starts past the stretch's
    ///   text; otherwise each member's laid region, the next block's comments
    ///   passed over, and whether to lay it for the next parse.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the checks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormSplit::join_laid`].
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    fn checked_stretch(
        &self,
        (tree, obligations, met, collapse): (
            &SyntaxTree<'_>,
            &[ObligationInstance],
            &[Met],
            SlopeHeight,
        ),
        pieces: &[JoinPiece<'_, '_>],
        stretch: Stretch,
        regions: &Regions,
    ) -> Option<Cut>
    {
        let tops = tree.top_level();
        let origin = usize::from(stretch.origin);
        let start_of = |run: RunAt| usize::from(regions.start(run));
        let anchor_of = |run: RunAt| usize::from(regions.anchor(run));
        if let Some(run) = stretch.context {
            let piece = pieces.get(run.0)?;
            let laid = piece.laid?;
            let lead = start_of(run).checked_sub(anchor_of(run))?;
            let ends = start_of(run.next()).checked_sub(origin)?;
            let within = tops.partition_point(|child| usize::from(child.span().start()) < ends);
            let mut own = tops.get(.. within).unwrap_or_default();
            if piece.parked.base() == UnitBase::FormBoundary {
                let (stand_in, rest) = own.split_first()?;
                if stand_in.label() != NodeLabel::Wald || usize::from(stand_in.span().end()) != 0 {
                    return None;
                }
                own = rest;
            }
            let held = laid.slice.children();
            let same = own.len() == held.len()
                && own.iter().zip(held).all(|(child, kept)| {
                    child.label() == kept.label()
                        && usize::from(child.span().start()).checked_add(lead)
                            == Some(usize::from(kept.span().start()))
                        && usize::from(child.span().end()).checked_add(lead)
                            == Some(usize::from(kept.span().end()))
                });
            if !same {
                return None;
            }
        }
        let last = stretch.end;
        let mut passed = Vec::new();
        if let Some(next) = pieces.get(last.0) {
            let laid = next.laid?;
            let end = start_of(last).checked_sub(origin)?;
            if tops
                .last()
                .is_some_and(|child| usize::from(child.span().start()) >= end)
            {
                return None;
            }
            let anchor = anchor_of(last);
            let lead = start_of(last).checked_sub(anchor)?;
            let shift = anchor.checked_sub(origin)?;
            for comment in laid.slice.leading(ByteOffset::from(lead)) {
                let start = usize::from(comment.span().start()).checked_add(shift)?;
                let finish = usize::from(comment.span().end()).checked_add(shift)?;
                let at = tops.partition_point(|child| usize::from(child.span().start()) < start);
                let found = tops.get(at)?;
                if found.label() != comment.label()
                    || usize::from(found.span().start()) != start
                    || usize::from(found.span().end()) != finish
                {
                    return None;
                }
                passed.push(ChildCount::from(at));
            }
        }
        let wanted = kept_molding(met, collapse);
        let cut = self.cut(
            tree,
            obligations,
            stretch,
            &passed,
            &alloc::vec![Laying::Lay; wanted.len()],
            regions,
        );
        Some((cut, wanted))
    }

    /// Cut each run of `stretch` out of `tree`, whose text starts at the
    /// stretch's origin in the source, where `wanted` asks for it: the slice of
    /// its region and its region's obligations, counted from the start of the
    /// run before it. The last member's slice passes over the root children at
    /// `passed`.
    ///
    /// # Specification
    /// - requires: `tree` and `obligations` are a commit of the text of the
    ///   runs of `stretch` from its origin; `wanted` has one entry per member;
    ///   `passed` is ascending.
    /// - ensures: one entry per member: its laid region where wanted and the
    ///   slice can be cut, nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the cut.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FormSplit::join_laid`].
    /// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
    fn cut(
        &self,
        tree: &SyntaxTree<'_>,
        obligations: &[ObligationInstance],
        stretch: Stretch,
        passed: &[ChildCount],
        wanted: &[Laying],
        regions: &Regions,
    ) -> Vec<Option<LaidUnit>>
    {
        let tops = tree.top_level();
        let runs = self.runs.len();
        let origin = usize::from(stretch.origin);
        let local = |at: ByteOffset| usize::from(at).saturating_sub(origin);
        (stretch.first.0 .. stretch.end.0)
            .zip(wanted)
            .map(|(run, &wanted)| {
                if wanted == Laying::Skip {
                    return None;
                }
                let run = RunAt(run);
                let from = local(regions.start(run));
                let to = (run.next().0 < runs).then(|| local(regions.start(run.next())));
                let within = |at: usize| at >= from && to.is_none_or(|to| at < to);
                let first = tops.partition_point(|child| usize::from(child.span().start()) < from);
                let end = to.map_or(tops.len(), |to| {
                    tops.partition_point(|child| usize::from(child.span().start()) < to)
                });
                let anchor = local(regions.anchor(run));
                let without = if run.next() == stretch.end {
                    passed
                }
                else {
                    &[]
                };
                let slice = tree
                    .slice(
                        ChildCount::from(first) .. ChildCount::from(end),
                        without,
                        ByteOffset::from(anchor),
                    )
                    .ok()?;
                let owed = obligations
                    .iter()
                    .filter(|owed| within(usize::from(owed.span.start())))
                    .map(|owed| {
                        let start = usize::from(owed.span.start()).saturating_sub(anchor);
                        let end = usize::from(owed.span.end()).saturating_sub(anchor);
                        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
                            .map(|span| ObligationInstance::new(owed.class, span))
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .ok()?;
                Some(LaidUnit {
                    slice,
                    obligations: owed,
                })
            })
            .collect()
    }
}

/// Per unit, whether it kept its own molding to the commit: its seam held, and
/// no later join and not the collapse touched a cell below its ceiling.
///
/// # Specification
/// - requires: `met` is how each unit met one state, in order, and `collapse`
///   how far that state's commit reached.
/// - ensures: one entry per unit.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`FormSplit::join_laid`].
/// - witness: `parse::tests::a_laid_join_parses_as_the_whole_source`
#[spec(ensures: |ret| ret.len() == met.len())]
fn kept_molding(
    met: &[Met],
    collapse: SlopeHeight,
) -> Vec<Laying>
{
    let mut later = collapse;
    let mut kept: Vec<Laying> = met
        .iter()
        .rev()
        .map(|met| {
            let own = if met.seam == UnitSeam::Joined && later >= met.ceiling {
                Laying::Lay
            }
            else {
                Laying::Skip
            };
            later = later.min(met.touched);
            own
        })
        .collect();
    kept.reverse();
    kept
}
