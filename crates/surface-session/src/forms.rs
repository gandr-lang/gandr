//! The form store: every form of the latest parsed revision, molded and
//! parked under its identity, so the next revision molds only the forms whose
//! identity the store does not hold, and that revision's labeling, so the next
//! revision relabels only around its edit.
//!
//! A revision is relabeled from the latest one's labeling
//! ([`Labeling::relabel`]) and split at its predicted top-level form
//! boundaries ([`FormSplit`]). Each run's identity ([`FormSplit::identity`])
//! spells what its molding reads: its tokens, the lookahead past it, and
//! whether it starts the source. A run whose identity the store holds keeps its
//! parked unit; the others are molded through the session's fork, largest
//! first. The commit takes up whole each run whose region the store laid out
//! after the unit the run before it holds now, where that unit, the run's own
//! and the next run's are clean ([`FormSplit::join_laid`]). The other runs
//! join, in run order, onto the checkpoint of the run before them; the join's
//! seam checks re-mold any run whose boundary was not real, so the parse
//! equals the whole parse of the revision whatever the store held. The store
//! then holds exactly the revision's units, the regions laid for them, and its
//! labeling.
//!
//! # The form store parses only the forms an edit touched
//!
//! **Choice.** The session keeps every top-level form of the latest parsed
//! revision, molded and parked by the parser (`FormUnit::park`), under the
//! form's identity (`FormSplit::identity`), and the revision's text and
//! labeling. A revision is relabeled from the latest one's labeling
//! (`Labeling::relabel`), which scans only around the edit, and split at its
//! predicted form boundaries; a form whose identity the store holds, molded
//! under the session's grammar, is taken up from its parked unit
//! (`FormUnit::resume`), and the rest are molded on the pool the driver hands
//! the session (`Session::with_pool`, the calling thread alone by default),
//! largest first. The commit takes up whole each form whose region the store
//! laid out after the same form before it, one copy of its nodes with its
//! digest, and joins only the other units (`FormSplit::join_laid`). The store
//! then holds exactly the revision's units and their regions, so its memory is
//! one revision's forms whatever the history. `Submission::forms` counts the
//! revision's forms, the ones molded and the ones taken up whole.
//!
//! **Identity.** A form's identity is the exact spelling of everything its
//! molding reads: whether it starts the source or follows a form boundary, its
//! tokens' classes and relative ends, and the bytes from its first token
//! through the eighth significant token past its end, the furthest the molder's
//! lookahead reads. Two forms with one identity mold to one unit, so a taken-up
//! unit is the unit molding would build. An edit therefore molds the forms it
//! changed and the forms whose lookahead reaches into it — on the generated
//! two-thousand-form module, one to eight. An edit that moves a boundary — a
//! merge that drops a terminator, a split that adds one, an insertion or a
//! deletion — changes the identities across it, and the join's seam checks
//! re-mold any run whose predicted boundary was not real, so the parse equals
//! the whole parse of the revision whatever the store held. A session whose
//! grammar's fingerprint differs from the one a unit was molded under molds
//! every form, which is the whole revision.
//!
//! **The equality.** The witnesses submit every edit class — a change, an
//! insertion, a deletion, a move, a merge, a split, a top-level return the
//! lowering refuses whole — over generated modules of both roots, whose forms
//! include data declarations and cases over their constructors, at one thread
//! and at three, and compare each submission with the walk's composition of the
//! same text and with a fresh session's: the composition, the standing, the
//! parse's repairs, the kernel checkpoint and the resume's typings. Edit
//! scripts over every corpus source are compared the same way. Under enforced
//! specifications, whose checks multiply a submission's cost about fortyfold,
//! the scripts run over a thirty-two-form module, every sixth corpus source and
//! fewer property cases.
//!
//! **Alternatives.** A form is identified by its content across revisions, and
//! a content digest is the usual key. A digest of the window costs a hash per
//! form on every submission, measured on the edit path, and can collide; the
//! exact spelling costs a copy of bytes the revision already holds and cannot.
//! A store that kept units from every revision would serve an undo without
//! molding, at memory growing with the history; keeping one revision bounds it.
//! Re-parsing only the edited byte range would need the molder to restart
//! mid-form, which its push machine does not offer; a form is the smallest unit
//! it resumes from a checkpoint.
//!
//! **Reversal.** Identities persisted across processes, beside the session's
//! checkpoints, need a fixed-width key: a digest of the spelling then becomes
//! the stored key. A measured undo-heavy face would keep a bounded history of
//! revisions.
//!
//! **What it does not cover.** On the generated two-thousand-form module, a
//! one-form edit does not label or re-mold the revision: the store relabels it
//! around the edit (`Labeling::relabel`), and the store looks each form up once
//! and prunes itself in place. The commit takes an unchanged form up whole: it
//! joins the edited forms and the form after them onto the checkpoint of the
//! form before (`FormSplit::join_laid`), and assembles the tree from the
//! regions with one copy of each node and one digest per form
//! (`SyntaxTree::assembled`). A digest per form costs less than a digest per
//! node in the parked units. What remains is linear in the module, and each
//! stage names what removes it. The lowering reads the whole tree, and its
//! classification cannot be kept per form: it writes about twelve index spaces
//! keyed by the tree's positions — plans, readings, operand, statement and
//! parameter stretches, binder scopes, case forms, answers, descents, hole
//! identities, which are positions themselves — so a kept form needs every
//! index remapped. One arena segment per form, over the same per-form layout,
//! carries a form's identity through
//! tree, arena and origins, hole and case origins included, and removes the
//! lowering's whole-module pass with the commit's. The incremental checker's
//! resume and the edit snapshot re-encode every item from the arena, and an
//! item carried with its segment needs neither. The whole-module judgement
//! retires when a report is assembled from adopted checkpoints. The readmission
//! and the kernel export run after the report and are linear in the module. The
//! measurement — `cargo run --release -p gandr-surface-session --example
//! edit_loop` — prints each edit class's judged, admitted and whole submission
//! walls at both roots and both widths, and the heap the form store and the
//! session keep against the lowered revision.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::cmp::Reverse;

use anodized::spec;
use gandr_core_fork::Fork;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::FormIdentity;
use gandr_surface_parser::FormSplit;
use gandr_surface_parser::FormUnit;
use gandr_surface_parser::JoinPiece;
use gandr_surface_parser::Labeling;
use gandr_surface_parser::LaidUnit;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::Molder;
use gandr_surface_parser::ParkedUnit;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::RunCount;
use gandr_surface_parser::RunRegion;
use gandr_surface_parser::TokenCount;
use gandr_surface_parser::TokenRun;
use gandr_surface_syntax::ByteOffset;
#[cfg(feature = "instrument")]
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

use crate::stack::Spines;
use crate::stack::Stack;

/// A count of top-level forms.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormCount(usize);

impl From<usize> for FormCount
{
    /// The count `forms`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(forms: usize) -> Self
    {
        Self(forms)
    }
}

impl From<FormCount> for usize
{
    /// The number `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: FormCount) -> Self
    {
        count.0
    }
}

/// How a revision's parse was assembled: its forms and how they came in.
///
/// The census counts the forms molded rather than taken up from the form
/// store, the forms the commit took up whole as laid out before, and the
/// tokens the labeling scanned afresh.
///
/// # Specification
/// - requires: constructed by the form store's parse.
/// - ensures: `molded` and `kept` each never exceed `forms`.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the store's parse
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a first revision molds every form and keeps none whole,
///   an unchanged one molds none, and a one-form edit molds the edited form and
///   the forms whose lookahead reads it and keeps whole the forms beyond its
///   neighbours; a census counting the taken-up forms as molded, or a stretch's
///   forms as kept, changes those counts.
/// - witness: `tests::forms::a_one_form_edit_molds_only_the_forms_that_read_it`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FormCensus
{
    /// The revision's top-level forms.
    forms: FormCount,
    /// The forms molded rather than taken up.
    molded: FormCount,
    /// The forms the commit took up whole, as a parse before laid them out.
    kept: FormCount,
    /// The tokens labeled afresh: every token of a revision labeled whole, and
    /// the relabel's scan around the edit otherwise.
    relabeled: TokenCount,
}

impl FormCensus
{
    /// The revision's top-level forms, as its split predicted them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn forms(&self) -> FormCount
    {
        self.forms
    }

    /// The forms molded rather than taken up from the form store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn molded(&self) -> FormCount
    {
        self.molded
    }

    /// The forms the commit took up whole, as a parse before laid them out,
    /// rather than joining their units again.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kept(&self) -> FormCount
    {
        self.kept
    }

    /// The tokens labeled afresh rather than shifted from the latest
    /// revision's labeling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relabeled(&self) -> TokenCount
    {
        self.relabeled
    }
}

/// Every form of the latest parsed revision, parked under its identity, and
/// that revision's labeling.
///
/// # Specification
/// - requires: nothing.
/// - ensures: after a parse, holds one parked unit per distinct identity among
///   the parsed revision's runs, and nothing else, and the parsed revision's
///   text and labeling.
/// - panics: none.
/// - executable: none — this state carrier has no call boundary; its parse
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — generated edits of every class, at both roots and both
///   widths, submit to the batch composition of each revision; a store keeping
///   a stale unit, dropping one the next revision needs, or relabeling from a
///   stale labeling changes a report or the molded count.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
/// - witness: `tests::forms::a_one_form_edit_molds_only_the_forms_that_read_it`
#[derive(Clone, Debug, Default)]
pub struct FormStore
{
    /// The parked units, by identity, each with the parse that last took it
    /// up or parked it.
    units: BTreeMap<FormIdentity, Held>,
    /// The latest parsed revision's text and labeling.
    labeled: Labeled,
    /// The latest parse.
    generation: Generation,
    /// The serial the next parked unit takes.
    next: Serial,
    /// The spines of the latest parsed revision, by form.
    stack: Arc<Stack>,
    /// The runs the latest parse molded, in source order, which the counts
    /// layer reads.
    #[cfg(feature = "instrument")]
    molded: Vec<(RunPosition, TokenRun)>,
}

/// A parked unit, the parse that last took it up or parked it, its serial,
/// and the region a parse laid out for it.
#[derive(Clone, Debug)]
struct Held
{
    /// The unit.
    parked: ParkedUnit,
    /// The parse that last took it up or parked it.
    seen: Generation,
    /// The unit's serial: two held units of one serial are one unit.
    serial: Serial,
    /// The region the latest parse that laid one laid out for the unit.
    laid: Option<Laid>,
}

/// A region a parse laid out for a unit, the unit the run before it held, and
/// the spines the parse read off the region.
#[derive(Clone, Debug)]
struct Laid
{
    /// The unit the run before held, whose comments the region's first form
    /// holds.
    after: Predecessor,
    /// The region.
    unit: LaidUnit,
    /// The spines of the region's forms, counted from the region's start;
    /// none when they hold no spine.
    spines: Option<Arc<Spines>>,
}

/// What a run follows: the start of the source, or the unit of one serial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Predecessor
{
    /// The run starts the source.
    SourceStart,
    /// The run before holds the unit of this serial.
    Unit(Serial),
}

/// A parked unit's serial, given once by the store that parks it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Serial(u64);

/// One of the store's parses, counted from its first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Generation(u64);

/// What the store kept of the latest parsed revision for the next to
/// relabel.
#[derive(Clone, Debug, Default)]
enum Labeled
{
    /// The store has parsed nothing: the next revision is labeled whole.
    #[default]
    Nothing,
    /// The latest parsed revision.
    Revision
    {
        /// Its text.
        text: String,
        /// Its labeling.
        labeling: Labeling,
    },
}

impl FormStore
{
    /// Parse `revision` under `grammar`, relabeling it from the latest
    /// revision's labeling, taking up every form whose identity the store
    /// holds and molding the rest through `fork`.
    ///
    /// # Specification
    /// - requires: nothing; the store may hold units of any revision and any
    ///   grammar.
    /// - ensures: the parse equals [`parse`](gandr_surface_parser::parse) of
    ///   `revision` under `grammar`. A run is taken up when the store holds a
    ///   unit under its identity that was molded over `grammar`'s fingerprint,
    ///   and molded otherwise, once per distinct identity. A run is taken up
    ///   whole when the store holds a region laid for its unit after the unit
    ///   the run before it holds now. The census counts the runs, the molded
    ///   identities and the runs taken up whole. The store then holds one unit
    ///   per distinct identity of the revision's runs, each with the region the
    ///   latest parse laid for it and the spines read off that region, the
    ///   revision's labeling, whether the commit succeeded or not, and the
    ///   stack of the parse ([`Self::stack`]).
    /// - provides: the parse every submission lowers; a grammar the store's
    ///   units were not molded over molds every form, which is the whole
    ///   revision.
    /// - fails: [`MeldError`] when the commit's arena cannot be built.
    /// - panics: only by propagating a molding job's panic.
    /// - economy: the revision is labeled around its edit; each run's identity
    ///   is looked up once, each molded unit is parked once, and the store is
    ///   pruned in place. A unit is resumed only where the join molds its run
    ///   again; a run taken up whole costs one copy of its nodes and keeps its
    ///   spines; the spines of every other run are read off its region.
    ///
    /// # Errors
    /// The commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated edits of every class, at both roots and
    ///   both widths, submit to the batch composition of each revision with the
    ///   molded and kept counts the edits predict, and every revision commits
    ///   the whole parse's tree; a unit molded over another grammar is never
    ///   taken up.
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    /// - witness: `tests::forms::a_one_form_edit_molds_only_the_forms_that_read_it`
    /// - witness: `tests::forms::sweeps::every_corpus_edit_script_submits_as_the_walk_composes_it`
    /// - witness: `forms::tests::a_unit_of_another_grammar_is_molded_again`
    #[inline]
    #[spec(ensures: |ret| self.units.len() <= ret.as_ref().map_or(usize::MAX, |&(_, census)| usize::from(census.forms))
        && (ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(ref parsed, census)| parsed.tree().source() == revision
            && census.molded <= census.forms && census.kept <= census.forms)))]
    pub fn parse<'text, F>(
        &mut self,
        grammar: &Pbg,
        revision: SourceText<'text>,
        fork: &F,
    ) -> Result<(ParseResult<'text>, FormCensus), MeldError>
    where
        F: Fork,
    {
        let mut molder = Molder::new(grammar);
        let text = <&str>::from(revision);
        let (labeling, relabeled) = match core::mem::take(&mut self.labeled) {
            Labeled::Revision {
                text: before,
                labeling,
            } => labeling.relabel(
                SourceFragment::from(before.as_str()),
                SourceFragment::from(text),
            ),
            Labeled::Nothing => whole(revision),
        };
        let split = FormSplit::labeled(&molder, revision, labeling);
        let runs = split.runs();
        let forms = FormCount(runs.len());
        let identities: Vec<FormIdentity> = runs.iter().map(|&run| split.identity(run)).collect();
        self.generation = Generation(self.generation.0.saturating_add(1));
        let generation = self.generation;
        // The runs the store cannot serve, one per distinct identity, to mold.
        let mut missing: Vec<(RunPosition, TokenRun)> = Vec::new();
        let mut planned = BTreeSet::new();
        for (position, (&run, identity)) in runs.iter().zip(&identities).enumerate() {
            match self.units.get_mut(identity) {
                Some(held) if held.parked.fingerprint() == grammar.fingerprint() => {
                    held.seen = generation;
                },
                Some(_) | None => {
                    if planned.insert(identity) {
                        missing.push((RunPosition(position), run));
                    }
                },
            }
        }
        let molded = mold_runs(grammar, &split, &missing, fork);
        let mut fresh = BTreeMap::new();
        for (RunPosition(position), unit) in molded {
            if let Some(identity) = identities.get(position) {
                let serial = self.serial();
                let _stale = self.units.insert(identity.clone(), Held {
                    parked: unit.park(),
                    seen: generation,
                    serial,
                    laid: None,
                });
            }
            let _first = fresh.insert(position, unit);
        }
        self.units.retain(|_, held| held.seen == generation);
        let serials: Vec<Option<Serial>> = identities
            .iter()
            .map(|identity| self.units.get(identity).map(|held| held.serial))
            .collect();
        let follows = |position: usize| {
            position
                .checked_sub(1)
                .map_or(Some(Predecessor::SourceStart), |before| {
                    serials
                        .get(before)
                        .copied()
                        .flatten()
                        .map(Predecessor::Unit)
                })
        };
        // Every identity was parked above, so each run has its held unit; a
        // run without one is molded whole, which keeps the parse total.
        let pieces: Option<Vec<JoinPiece<'_, '_>>> = identities
            .iter()
            .enumerate()
            .map(|(position, identity)| {
                let held = self.units.get(identity)?;
                let laid = held
                    .laid
                    .as_ref()
                    .filter(|laid| Some(laid.after) == follows(position))
                    .map(|laid| &laid.unit);
                Some(JoinPiece::new(&held.parked, fresh.remove(&position), laid))
            })
            .collect();
        let laid = pieces.map(|pieces| {
            split.join_laid(&mut molder, pieces).map(|laid| {
                let kept = laid.kept();
                let (join, regions, starts) = laid.into_parts();
                (join, regions, starts, kept)
            })
        });
        let joined = laid.unwrap_or_else(|| {
            let units = runs
                .iter()
                .map(|&run| split.mold(&mut molder, run))
                .collect();
            split
                .join(&mut molder, units)
                .map(|join| (join, Vec::new(), Vec::new(), RunCount::default()))
        });
        self.labeled = Labeled::Revision {
            text: text.to_owned(),
            labeling: split.into_labeling(),
        };
        let (join, regions, starts, kept) = match joined {
            Ok(joined) => joined,
            Err(fault) => {
                self.stack = Arc::new(Stack::default());
                return Err(fault);
            },
        };
        let parsed = join.into_result();
        let tree = parsed.tree();
        let stack = if regions.is_empty() {
            Stack::of(grammar, tree)
        }
        else {
            let mut tops = tree
                .children(tree.root())
                .filter_map(|child| Some((tree.node(child)?.span().start(), child)))
                .peekable();
            let read = |own: &[NodeIndex], start: ByteOffset| {
                Spines::read(grammar, tree, own, start).map(Arc::new)
            };
            let mut spined = Vec::with_capacity(regions.len());
            let mut own: Vec<NodeIndex> = Vec::new();
            for (position, region) in regions.into_iter().enumerate() {
                let Some(&start) = starts.get(position)
                else {
                    continue;
                };
                let end = starts.get(position.saturating_add(1)).copied();
                own.clear();
                while let Some(child) = tops.next_if(|&(at, _)| end.is_none_or(|end| at < end)) {
                    own.push(child.1);
                }
                let held = identities
                    .get(position)
                    .and_then(|identity| self.units.get_mut(identity));
                let spines = match region {
                    RunRegion::Kept => held
                        .and_then(|held| held.laid.as_ref())
                        .and_then(|laid| laid.spines.as_ref())
                        .map(Arc::clone),
                    RunRegion::Laid(unit) => {
                        let spines = read(&own, start);
                        if let (Some(held), Some(after)) = (held, follows(position)) {
                            held.laid = Some(Laid {
                                after,
                                unit,
                                spines: spines.as_ref().map(Arc::clone),
                            });
                        }
                        spines
                    },
                    RunRegion::Unlaid => read(&own, start),
                };
                if let Some(spines) = spines {
                    spined.push((start, spines));
                }
            }
            Stack::from_forms(spined)
        };
        self.stack = Arc::new(stack);
        let census = FormCensus {
            forms,
            molded: FormCount(missing.len()),
            kept: FormCount(usize::from(kept)),
            relabeled,
        };
        #[cfg(feature = "instrument")]
        {
            self.molded = missing;
        }
        Ok((parsed, census))
    }

    /// The spines of the latest parsed revision, by form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stack [`Stack::of`] reads off the latest parse's tree,
    ///   spine for spine; empty before a parse and after a parse that did not
    ///   commit.
    /// - provides: the context stack of the revision a face's judgement parsed,
    ///   at no walk of the forms the parse took up whole.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over generated edits of every class and every corpus
    ///   edit script, the stack the store keeps is the stack read off the whole
    ///   parse of the same text.
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    /// - witness: `tests::forms::sweeps::every_corpus_edit_script_submits_as_the_walk_composes_it`
    #[inline]
    #[must_use]
    pub const fn stack(&self) -> &Arc<Stack>
    {
        &self.stack
    }

    /// The bytes of each form that the latest parse molded, in source order,
    /// in the coordinates of the text it parsed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one span for each run that the latest parse molded and that
    ///   holds a token, from the start of its first token to the end of its
    ///   last, ascending; none before a parse.
    /// - panics: none.
    /// - executable: none — the result is a lazy iterator over the store.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recheck at the counts layer reads one molded form
    ///   in each declaration of a first parse, and none in a second parse of
    ///   the same text.
    /// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
    #[cfg(feature = "instrument")]
    pub(crate) fn molded(&self) -> impl Iterator<Item = ByteSpan> + '_
    {
        let tokens = match self.labeled {
            Labeled::Revision { ref labeling, .. } => labeling.tokens(),
            Labeled::Nothing => &[],
        };
        let offset = |at: u32| ByteOffset::from(usize::try_from(at).unwrap_or(usize::MAX));
        self.molded.iter().filter_map(move |&(_, run)| {
            let run = tokens.get(usize::from(run.start()) .. usize::from(run.end()))?;
            ByteSpan::new(offset(run.first()?.start), offset(run.last()?.end)).ok()
        })
    }

    /// The serial the next parked unit takes, and the store's next one past
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn serial(&mut self) -> Serial
    {
        let given = self.next;
        self.next = Serial(given.0.saturating_add(1));
        given
    }

    /// Parse `revision` under `grammar`, taking up every form whose identity
    /// the store holds and molding the rest through `fork`, keeping
    /// nothing: the store is unchanged.
    ///
    /// # Specification
    /// - requires: nothing; the store may hold units of any revision and any
    ///   grammar.
    /// - ensures: the parse equals [`parse`](gandr_surface_parser::parse) of
    ///   `revision` under `grammar`. The revision is labeled whole; a run is
    ///   taken up when the store holds a unit under its identity molded over
    ///   `grammar`'s fingerprint, and molded otherwise, once per run; the
    ///   census counts the runs and the molded ones.
    /// - provides: the parse a trial lowers, so a candidate revision reuses
    ///   every form it shares with the latest one without disturbing the store
    ///   another trial or the next submission reads.
    /// - fails: [`MeldError`] when the commit's arena cannot be built.
    /// - panics: only by propagating a molding job's panic.
    /// - economy: each run's identity is looked up once and each taken-up
    ///   unit's checkpoint cloned once into the join; nothing is parked.
    ///
    /// # Errors
    /// The commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — candidate revisions of a submitted one parse to the
    ///   trees their whole parse gives, molding only the forms the store does
    ///   not hold, and leave the store as the next submission's census reads
    ///   it.
    /// - witness: `forms::tests::a_held_parse_keeps_the_store`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(ref parsed, census)|
        parsed.tree().source() == revision && census.molded <= census.forms))]
    pub fn parse_held<'text, F>(
        &self,
        grammar: &Pbg,
        revision: SourceText<'text>,
        fork: &F,
    ) -> Result<(ParseResult<'text>, FormCensus), MeldError>
    where
        F: Fork,
    {
        let mut molder = Molder::new(grammar);
        let (labeling, relabeled) = whole(revision);
        let split = FormSplit::labeled(&molder, revision, labeling);
        let runs = split.runs();
        let held: Vec<Option<&ParkedUnit>> = runs
            .iter()
            .map(|&run| {
                self.units
                    .get(&split.identity(run))
                    .map(|held| &held.parked)
                    .filter(|parked| parked.fingerprint() == grammar.fingerprint())
            })
            .collect();
        let missing: Vec<(RunPosition, TokenRun)> = runs
            .iter()
            .zip(&held)
            .enumerate()
            .filter(|&(_, (_, parked))| parked.is_none())
            .map(|(position, (&run, _))| (RunPosition(position), run))
            .collect();
        let mut molded: BTreeMap<usize, FormUnit<'_>> = mold_runs(grammar, &split, &missing, fork)
            .into_iter()
            .map(|(RunPosition(position), unit)| (position, unit))
            .collect();
        let census = FormCensus {
            forms: FormCount(runs.len()),
            molded: FormCount(molded.len()),
            kept: FormCount(0),
            relabeled,
        };
        let mut units = Vec::with_capacity(runs.len());
        for (position, (&run, parked)) in runs.iter().zip(&held).enumerate() {
            units.push(match (*parked, molded.remove(&position)) {
                (Some(parked), _) => FormUnit::resume(grammar, run, parked),
                (None, Some(unit)) => unit,
                // Every run the store does not hold was molded above; molding
                // here keeps the parse total should that ever not hold.
                (None, None) => split.mold(&mut molder, run),
            });
        }
        Ok((split.join(&mut molder, units)?.into_result(), census))
    }
}

/// `revision` labeled whole, and its every token counted as labeled afresh.
///
/// # Specification
/// trivial.
fn whole(revision: SourceText<'_>) -> (Labeling, TokenCount)
{
    let labeling = Labeling::new(SourceFragment::from(<&str>::from(revision)));
    let tokens = TokenCount(labeling.tokens().len());
    (labeling, tokens)
}

/// A run's position among its revision's runs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RunPosition(usize);

/// Mold `runs` of `split` through `fork`, offering the largest run by tokens
/// first, each fork worker molding with a molder of its own.
///
/// # Specification
/// - requires: each run is one of `split`'s.
/// - ensures: one unit per run, beside the position it came with, each as
///   [`FormSplit::mold`] molds it. Whatever the fork's width, every unit is the
///   one a lone molder builds.
/// - panics: only by propagating a molding job's panic.
///
/// # Adequacy
/// - hypothesis: L3 — the generated edits submit alike at one thread and at the
///   host's width, and serial and pooled forks of every width mold the same
///   units for a whole revision and for a part of it.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
/// - witness: `forms::tests::every_width_molds_the_same_units`
#[spec(ensures: |ret| ret.len() == runs.len())]
fn mold_runs<'pbg, F>(
    grammar: &'pbg Pbg,
    split: &FormSplit<'_>,
    runs: &[(RunPosition, TokenRun)],
    fork: &F,
) -> Vec<(RunPosition, FormUnit<'pbg>)>
where
    F: Fork,
{
    let mut slots: Vec<(RunPosition, TokenRun, Option<FormUnit<'pbg>>)> = runs
        .iter()
        .map(|&(position, run)| (position, run, None))
        .collect();
    slots.sort_by_key(|&(position, run, _)| {
        (
            Reverse(usize::from(run.end()).saturating_sub(usize::from(run.start()))),
            position,
        )
    });
    fork.each(
        &mut slots,
        || Molder::new(grammar),
        |molder, &mut (_, run, ref mut unit)| *unit = Some(split.mold(molder, run)),
    );
    slots
        .into_iter()
        .filter_map(|(position, _, unit)| unit.map(|unit| (position, unit)))
        .collect()
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;

    use gandr_core_fork::Serial;
    use gandr_surface_dispatcher::Pool;
    use gandr_surface_dispatcher::Threads;
    use gandr_surface_dispatcher::Width;
    use gandr_surface_grammar::built_in;
    use gandr_surface_parser::FormSplit;
    use gandr_surface_parser::FormUnit;
    use gandr_surface_parser::Molder;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;

    use super::FormStore;
    use super::RunPosition;
    use super::mold_runs;

    /// Twelve declarations, each its own form.
    const SOURCE: &str = include_str!("forms/fixtures/source.gandr");

    #[test]
    fn every_width_molds_the_same_units()
    {
        let grammar = built_in().expect("the grammar builds");
        let molder = Molder::new(&grammar);
        let split = FormSplit::new(&molder, SourceText::from(SOURCE));
        let runs: Vec<_> = split
            .runs()
            .iter()
            .copied()
            .enumerate()
            .map(|(position, run)| (RunPosition(position), run))
            .collect();
        assert_eq!(runs.len(), 12);
        let serial = mold_runs(&grammar, &split, &runs, &Serial);
        let parked = |mut units: Vec<(RunPosition, FormUnit<'_>)>| {
            units.sort_by_key(|&(position, _)| position);
            units
                .into_iter()
                .map(|(RunPosition(position), unit)| (position, unit.park()))
                .collect::<Vec<_>>()
        };
        let serial = parked(serial);
        assert_eq!(
            serial
                .iter()
                .map(|&(position, _)| position)
                .collect::<Vec<_>>(),
            (0 .. 12).collect::<Vec<_>>()
        );
        let some: Vec<_> = runs
            .iter()
            .copied()
            .filter(|&(RunPosition(position), _)| position % 3 == 1)
            .collect();
        let serial_some = serial
            .iter()
            .filter(|&&(position, _)| position % 3 == 1)
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(
            parked(mold_runs(&grammar, &split, &some, &Serial)),
            serial_some
        );
        for width in [2_usize, 5, 64] {
            let pool = Pool::new(Width::Threads(Threads::from(
                NonZeroUsize::new(width).expect("not zero"),
            )));
            assert_eq!(
                parked(mold_runs(&grammar, &split, &runs, &pool)),
                serial,
                "{width} threads"
            );
            assert_eq!(
                parked(mold_runs(&grammar, &split, &some, &pool)),
                serial_some,
                "{width} threads, a part of the runs"
            );
        }
    }

    #[test]
    fn a_unit_of_another_grammar_is_molded_again()
    {
        // Units parked over one grammar are never taken up under another with
        // a different fingerprint: every form is molded, and the parse is the
        // whole parse under the new grammar.
        let grammar = built_in().expect("the grammar builds");
        let source = SourceText::from(SOURCE);
        let mut store = FormStore::default();
        let (_, first) = store.parse(&grammar, source, &Serial).expect("commits");
        assert_eq!(usize::from(first.molded()), 12);
        let (_, again) = store.parse(&grammar, source, &Serial).expect("commits");
        assert_eq!(usize::from(again.molded()), 0);
        let mut rules = grammar.rules().to_vec();
        let _circuit = rules.pop();
        let other = gandr_surface_grammar::Pbg::build(grammar.dag().clone(), rules)
            .expect("the grammar less one circuit rule builds");
        assert_ne!(other.fingerprint(), grammar.fingerprint());
        let (parsed, census) = store.parse(&other, source, &Serial).expect("commits");
        assert_eq!(usize::from(census.molded()), 12);
        assert_eq!(parsed, parse(&other, source).expect("commits"));
    }

    #[test]
    fn a_held_parse_keeps_the_store()
    {
        // A held parse takes up what the store holds and molds the rest, to the
        // whole parse of its text, and parks nothing: the store still holds
        // exactly the latest parsed revision's units afterwards.
        let grammar = built_in().expect("the grammar builds");
        let edited = SOURCE.replace("def e = 5;", "def e = 50;");
        let edited = SourceText::from(edited.as_str());
        let empty = FormStore::default();
        let (parsed, census) = empty
            .parse_held(&grammar, edited, &Serial)
            .expect("commits");
        assert_eq!(parsed, parse(&grammar, edited).expect("commits"));
        assert_eq!(
            usize::from(census.molded()),
            12,
            "an empty store molds every form"
        );
        let mut store = FormStore::default();
        let _first = store
            .parse(&grammar, SourceText::from(SOURCE), &Serial)
            .expect("commits");
        for _ in 0_u8 .. 2_u8 {
            let (parsed, held) = store
                .parse_held(&grammar, edited, &Serial)
                .expect("commits");
            assert_eq!(parsed, parse(&grammar, edited).expect("commits"));
            assert!(
                usize::from(held.molded()) > 0 && usize::from(held.molded()) < 12,
                "the edited form and the forms reading it are molded, the rest taken up"
            );
            assert_eq!(usize::from(held.forms()), 12);
        }
        let (_, again) = store
            .parse(&grammar, SourceText::from(SOURCE), &Serial)
            .expect("commits");
        assert_eq!(
            usize::from(again.molded()),
            0,
            "the store still holds every form of the revision it parsed"
        );
        let (_, submitted) = store.parse(&grammar, edited, &Serial).expect("commits");
        assert!(
            usize::from(submitted.molded()) > 0,
            "nothing the held parses molded was parked for the next parse"
        );
    }
}
