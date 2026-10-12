//! The form store: every form of the latest parsed revision, molded and
//! parked under its identity, so the next revision molds only the forms whose
//! identity the store does not hold, and that revision's labeling, so the next
//! revision relabels only around its edit.
//!
//! A revision is relabeled from the latest one's labeling
//! ([`Labeling::relabel`]) and split at its predicted top-level form
//! boundaries ([`FormSplit`]). Each run's identity ([`FormSplit::identity`])
//! spells what its molding reads: its tokens, the lookahead past it, and
//! whether it starts the source. A run whose identity the store holds is taken
//! up from the parked unit ([`FormUnit::resume`]); the others are molded,
//! across as many threads as the session's width answers, largest first. The
//! units are joined in run order and committed; the join's seam checks
//! re-mold any run whose boundary was not real, so the parse equals the whole
//! parse of the revision whatever the store held. The store then holds
//! exactly the revision's units and its labeling.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::sync::mpsc;

use anodized::spec;
use gandr_surface_dispatcher::Threads;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::FormIdentity;
use gandr_surface_parser::FormSplit;
use gandr_surface_parser::FormUnit;
use gandr_surface_parser::Labeling;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::Molder;
use gandr_surface_parser::ParkedUnit;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::TokenRun;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

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

/// How a revision's parse was assembled: its forms, and how many of them
/// were molded rather than taken up from the form store.
///
/// # Specification
/// - requires: constructed by the form store's parse.
/// - ensures: `molded` never exceeds `forms`.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the store's parse
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a first revision molds every form, an unchanged one none,
///   and a one-form edit the edited form and the forms whose lookahead reads
///   it; a census counting the taken-up forms as molded changes those counts.
/// - witness: `tests::forms::a_one_form_edit_molds_only_the_forms_that_read_it`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FormCensus
{
    /// The revision's top-level forms.
    forms: FormCount,
    /// The forms molded rather than taken up.
    molded: FormCount,
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
}

/// A parked unit and the parse that last took it up or parked it.
#[derive(Clone, Debug)]
struct Held
{
    /// The unit.
    parked: ParkedUnit,
    /// The parse that last took it up or parked it.
    seen: Generation,
}

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
    /// holds and molding the rest on `threads` threads.
    ///
    /// # Specification
    /// - requires: nothing; the store may hold units of any revision and any
    ///   grammar.
    /// - ensures: the parse equals [`parse`](gandr_surface_parser::parse) of
    ///   `revision` under `grammar`. A run is taken up when the store holds a
    ///   unit under its identity that was molded over `grammar`'s fingerprint,
    ///   and molded otherwise, once per distinct identity; the census counts
    ///   the runs and the molded identities. The store then holds one unit per
    ///   distinct identity of the revision's runs, and the revision's labeling,
    ///   whether the commit succeeded or not.
    /// - provides: the parse every submission lowers; a grammar the store's
    ///   units were not molded over molds every form, which is the whole
    ///   revision.
    /// - fails: [`MeldError`] when the commit's arena cannot be built.
    /// - panics: only by propagating a molding thread's panic.
    /// - economy: the revision is labeled around its edit; each run's identity
    ///   is looked up once, each taken-up unit's checkpoint is cloned once into
    ///   the join, each molded unit is parked once, and the store is pruned in
    ///   place.
    ///
    /// # Errors
    /// The commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated edits of every class, at both roots and
    ///   both widths, submit to the batch composition of each revision with the
    ///   molded counts the edits predict; a unit molded over another grammar is
    ///   never taken up.
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    /// - witness: `tests::forms::a_one_form_edit_molds_only_the_forms_that_read_it`
    /// - witness: `forms::tests::a_unit_of_another_grammar_is_molded_again`
    #[spec(ensures: |ret| self.units.len() <= ret.as_ref().map_or(usize::MAX, |&(_, census)| usize::from(census.forms))
        && (ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(ref parsed, census)| parsed.tree().source() == revision
            && census.molded <= census.forms)))]
    pub fn parse<'text>(
        &mut self,
        grammar: &Pbg,
        revision: SourceText<'text>,
        threads: Threads,
    ) -> Result<(ParseResult<'text>, FormCensus), MeldError>
    {
        let mut molder = Molder::new(grammar);
        let text = <&str>::from(revision);
        let labeling = match core::mem::take(&mut self.labeled) {
            | Labeled::Revision {
                text: before,
                labeling,
            } => labeling.relabel(
                SourceFragment::from(before.as_str()),
                SourceFragment::from(text),
            ),
            | Labeled::Nothing => Labeling::new(SourceFragment::from(text)),
        };
        let split = FormSplit::labeled(&molder, revision, labeling);
        let runs = split.runs();
        let identities: Vec<FormIdentity> = runs.iter().map(|&run| split.identity(run)).collect();
        self.generation = Generation(self.generation.0.saturating_add(1));
        let generation = self.generation;
        // The units the store serves, in run order; the runs it cannot serve,
        // in run order; and one of those per distinct identity, to mold.
        let mut taken = Vec::with_capacity(runs.len());
        let mut pending: Vec<RunPosition> = Vec::new();
        let mut missing: Vec<(RunPosition, TokenRun)> = Vec::new();
        let mut planned = BTreeSet::new();
        for (position, (&run, identity)) in runs.iter().zip(&identities).enumerate() {
            match self.units.get_mut(identity) {
                | Some(held) if held.parked.fingerprint() == grammar.fingerprint() => {
                    held.seen = generation;
                    taken.push(FormUnit::resume(grammar, run, &held.parked));
                },
                | Some(_) | None => {
                    pending.push(RunPosition(position));
                    if planned.insert(identity) {
                        missing.push((RunPosition(position), run));
                    }
                },
            }
        }
        let molded = mold_runs(grammar, &split, &missing, threads);
        let census = FormCensus {
            forms: FormCount(runs.len()),
            molded: FormCount(molded.len()),
        };
        let mut fresh = BTreeMap::new();
        for (RunPosition(position), unit) in molded {
            if let Some(identity) = identities.get(position) {
                let _stale = self.units.insert(identity.clone(), Held {
                    parked: unit.park(),
                    seen: generation,
                });
            }
            let _first = fresh.insert(position, unit);
        }
        let mut taken = taken.into_iter();
        let mut pending = pending.into_iter().peekable();
        let mut units = Vec::with_capacity(runs.len());
        for (position, (&run, identity)) in runs.iter().zip(&identities).enumerate() {
            let unit = if pending.next_if_eq(&RunPosition(position)).is_some() {
                match (fresh.remove(&position), self.units.get(identity)) {
                    | (Some(unit), _) => unit,
                    // A later run of an identity molded above takes up its
                    // unit.
                    | (None, Some(held)) => FormUnit::resume(grammar, run, &held.parked),
                    // Every identity was parked above; molding here keeps the
                    // parse total should that ever not hold.
                    | (None, None) => split.mold(&mut molder, run),
                }
            }
            else {
                match taken.next() {
                    | Some(unit) => unit,
                    | None => split.mold(&mut molder, run),
                }
            };
            units.push(unit);
        }
        self.units.retain(|_, held| held.seen == generation);
        let joined = split.join(&mut molder, units);
        self.labeled = Labeled::Revision {
            text: text.to_owned(),
            labeling: split.into_labeling(),
        };
        Ok((joined?.into_result(), census))
    }

    /// Parse `revision` under `grammar`, taking up every form whose identity
    /// the store holds and molding the rest on `threads` threads, keeping
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
    /// - panics: only by propagating a molding thread's panic.
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
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(ref parsed, census)|
        parsed.tree().source() == revision && census.molded <= census.forms))]
    pub fn parse_held<'text>(
        &self,
        grammar: &Pbg,
        revision: SourceText<'text>,
        threads: Threads,
    ) -> Result<(ParseResult<'text>, FormCensus), MeldError>
    {
        let mut molder = Molder::new(grammar);
        let split = FormSplit::labeled(
            &molder,
            revision,
            Labeling::new(SourceFragment::from(<&str>::from(revision))),
        );
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
        let mut molded: BTreeMap<usize, FormUnit<'_>> =
            mold_runs(grammar, &split, &missing, threads)
                .into_iter()
                .map(|(RunPosition(position), unit)| (position, unit))
                .collect();
        let census = FormCensus {
            forms: FormCount(runs.len()),
            molded: FormCount(molded.len()),
        };
        let mut units = Vec::with_capacity(runs.len());
        for (position, (&run, parked)) in runs.iter().zip(&held).enumerate() {
            units.push(match (*parked, molded.remove(&position)) {
                | (Some(parked), _) => FormUnit::resume(grammar, run, parked),
                | (None, Some(unit)) => unit,
                // Every run the store does not hold was molded above; molding
                // here keeps the parse total should that ever not hold.
                | (None, None) => split.mold(&mut molder, run),
            });
        }
        Ok((split.join(&mut molder, units)?.into_result(), census))
    }
}

/// A run's position among its revision's runs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RunPosition(usize);

/// Mold `runs` of `split` on as many threads as `threads` answers, never more
/// than the runs, the calling thread among them, each taking the largest run
/// by tokens no thread has taken.
///
/// # Specification
/// - requires: each run is one of `split`'s.
/// - ensures: one unit per run, beside the position it came with, each as
///   [`FormSplit::mold`] molds it; fewer than two runs, or one thread, mold on
///   the calling thread alone. A thread the host refuses to start leaves its
///   runs to the others.
/// - panics: only by propagating a molding thread's panic.
///
/// # Adequacy
/// - hypothesis: L3 — the generated edits submit alike at one thread and at the
///   host's width, and a whole revision molds every run.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
/// - witness: `forms::tests::every_width_molds_the_same_units`
#[spec(ensures: |ret| ret.len() == runs.len())]
fn mold_runs<'pbg>(
    grammar: &'pbg Pbg,
    split: &FormSplit<'_>,
    runs: &[(RunPosition, TokenRun)],
    threads: Threads,
) -> Vec<(RunPosition, FormUnit<'pbg>)>
{
    let threads = usize::from(NonZeroUsize::from(threads)).min(runs.len());
    if threads <= 1 {
        let mut molder = Molder::new(grammar);
        return runs
            .iter()
            .map(|&(position, run)| (position, split.mold(&mut molder, run)))
            .collect();
    }
    let mut order: Vec<&(RunPosition, TokenRun)> = runs.iter().collect();
    order.sort_by_key(|&&(position, run)| {
        (
            core::cmp::Reverse(usize::from(run.end()).saturating_sub(usize::from(run.start()))),
            position,
        )
    });
    let cursor = AtomicUsize::new(0);
    let take = || order.get(cursor.fetch_add(1, Ordering::Relaxed)).copied();
    let (sender, receiver) = mpsc::channel();
    std::thread::scope(|scope| {
        for _ in 1 .. threads {
            let sender = sender.clone();
            let take = &take;
            let _started = std::thread::Builder::new().spawn_scoped(scope, move || {
                let mut molder = Molder::new(grammar);
                while let Some(&(position, run)) = take() {
                    if sender
                        .send((position, split.mold(&mut molder, run)))
                        .is_err()
                    {
                        break;
                    }
                }
            });
        }
        drop(sender);
        let mut molder = Molder::new(grammar);
        let mut units = Vec::with_capacity(runs.len());
        while let Some(&(position, run)) = take() {
            units.push((position, split.mold(&mut molder, run)));
        }
        units.extend(receiver.iter());
        units
    })
}

#[cfg(test)]
mod tests
{
    use gandr_surface_dispatcher::Threads;
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
    const SOURCE: &str = "def a = 1;\ndef b = 2;\ndef c = a;\ndef d = b;\ndef e = 5;\ndef f = 6;\n\
                          def g = 7;\ndef h = 8;\ndef i = 9;\ndef j = 10;\ndef k = 11;\ndef l = 12;\n";

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
        let serial = mold_runs(&grammar, &split, &runs, Threads::ONE);
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
        for width in [2_usize, 5, 64] {
            let threads = Threads::from(core::num::NonZeroUsize::new(width).expect("not zero"));
            assert_eq!(
                parked(mold_runs(&grammar, &split, &runs, threads)),
                serial,
                "{width} threads"
            );
        }
        let some: Vec<_> = runs
            .iter()
            .copied()
            .filter(|&(RunPosition(position), _)| position % 3 == 1)
            .collect();
        assert_eq!(
            parked(mold_runs(&grammar, &split, &some, Threads::ONE)),
            serial
                .iter()
                .filter(|&&(position, _)| position % 3 == 1)
                .cloned()
                .collect::<Vec<_>>()
        );
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
        let (_, first) = store
            .parse(&grammar, source, Threads::ONE)
            .expect("commits");
        assert_eq!(usize::from(first.molded()), 12);
        let (_, again) = store
            .parse(&grammar, source, Threads::ONE)
            .expect("commits");
        assert_eq!(usize::from(again.molded()), 0);
        let mut rules = grammar.rules().to_vec();
        let _circuit = rules.pop();
        let other = gandr_surface_grammar::Pbg::build(grammar.dag().clone(), rules)
            .expect("the grammar less one circuit rule builds");
        assert_ne!(other.fingerprint(), grammar.fingerprint());
        let (parsed, census) = store.parse(&other, source, Threads::ONE).expect("commits");
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
            .parse_held(&grammar, edited, Threads::ONE)
            .expect("commits");
        assert_eq!(parsed, parse(&grammar, edited).expect("commits"));
        assert_eq!(
            usize::from(census.molded()),
            12,
            "an empty store molds every form"
        );
        let mut store = FormStore::default();
        let _first = store
            .parse(&grammar, SourceText::from(SOURCE), Threads::ONE)
            .expect("commits");
        for _ in 0_u8 .. 2_u8 {
            let (parsed, held) = store
                .parse_held(&grammar, edited, Threads::ONE)
                .expect("commits");
            assert_eq!(parsed, parse(&grammar, edited).expect("commits"));
            assert!(
                usize::from(held.molded()) > 0 && usize::from(held.molded()) < 12,
                "the edited form and the forms reading it are molded, the rest taken up"
            );
            assert_eq!(usize::from(held.forms()), 12);
        }
        let (_, again) = store
            .parse(&grammar, SourceText::from(SOURCE), Threads::ONE)
            .expect("commits");
        assert_eq!(
            usize::from(again.molded()),
            0,
            "the store still holds every form of the revision it parsed"
        );
        let (_, submitted) = store
            .parse(&grammar, edited, Threads::ONE)
            .expect("commits");
        assert!(
            usize::from(submitted.molded()) > 0,
            "nothing the held parses molded was parked for the next parse"
        );
    }
}
