//! **Sweeps**: the corpus sources a sweep test visits. A sweep drives the
//! whole corpus through one feature — typing and erasing every source,
//! formatting it, molding every token drop — and runs in two budgets: a
//! stated sample on every pull request and every merge-queue entry, with
//! specifications enforced, within the 30 s every test is held to; and whole
//! under the `nightly` nextest profile, where the costliest sweeps each visit
//! the night's slice of the corpus and the rest visit all of it. The
//! `sweeps` profile visits the whole corpus in every sweep at once.
//!
//! - [`coverage`] reads which budget a run is in from the nextest profile.
//! - [`corpus`] walks the corpus and names each source's class.
//! - [`changed`] lists the corpus sources a change touches.
//! - [`sample`] draws a sample's hashed, stratified slice.
//! - [`rotation`] names the night's slice of a rotating sweep.
//!
//! A sweep test asks [`Sweep::asked`] once, filters [`corpus::sources`] to
//! its candidates, and visits what [`Sweep::visit`] returns, or what
//! [`Sweep::visit_rotating`] returns when it rotates nightly:
//!
//! ```no_run
//! use gandr_workflow_sweep::Sample;
//! use gandr_workflow_sweep::SampleName;
//! use gandr_workflow_sweep::SampleSize;
//! use gandr_workflow_sweep::Sweep;
//! use gandr_workflow_sweep::corpus;
//!
//! const SAMPLE: Sample = Sample {
//!     name: SampleName("every_source_formats_once"),
//!     size: SampleSize(12),
//! };
//! let sweep = Sweep::asked()?;
//! for source in sweep.visit(SAMPLE, &corpus::sources()?) {
//!     let _text = std::fs::read_to_string(&source.path);
//! }
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! # Decisions
//!
//! **One test, two budgets.** A sweep never leaves the pull-request lanes:
//! each test exercises some of its inputs under enforcement on every
//! landing, and the whole corpus nightly. The alternative was moving sweeps
//! to a nightly lane alone, which lets a landing break a sweep unseen for a
//! day.
//!
//! **The profile is the knob.** nextest names the running profile to every
//! test in `NEXTEST_PROFILE`; the `sweeps` profile means the whole corpus, the
//! `nightly` profile the whole corpus over its rotation, and every other
//! profile, or a run outside nextest, the sample. A sweep is selected by the
//! `sweeps` module it sits in, so neither whole profile's filter names a test.
//! The alternative was a variable per lane, which a task forgets to
//! set and a local run never sets.
//!
//! **A hashed slice at a fixed size.** A sample ranks its candidates by the
//! BLAKE3 digest of the sweep's name and the source's corpus path and takes
//! the first `size`: the same slice on every machine and every run, salted
//! per sweep so two sweeps cover different sources, and moved by at most one
//! source when the corpus gains or loses one. Its cost is fixed until the
//! corpus changes, which a stride over a length-sorted list is too, but a
//! stride moves every choice when one source is added. The alternatives were
//! the stride and a random draw per run, which makes a failure a lottery.
//!
//! **Stratified by location.** A source's class is where it sits — the
//! strict root, or the family below the fixture root, the pending set among
//! them — because membership in the corpus is location. The slice keeps the
//! first-ranked source of every class, so no class goes unvisited.
//!
//! **The change is always in.** Every candidate the change adds or modifies
//! joins the slice, measured against the revision `GANDR_SWEEP_BASE` names or,
//! unset, where `HEAD` left `origin/main` — the merge-base selection the
//! obligations report applies to witnesses. A run that cannot list the change
//! fails rather than sample without it. A change touching more sources than a
//! sweep's bound affords fails that bound; the sweep's own cost is the thing
//! to cut.
//!
//! **A layout is no change.** A modified source the formatter lays out to the
//! text it lays the base's out to holds the base's tokens and comments in the
//! base's order — the invariant `gandr-surface-format` checks on every text
//! it returns — so every sweep reads it as before, and it leaves the change.
//! A corpus-wide layout then keeps every sample at its stated size; the
//! nightly profile, visiting every source over its rotation, is the backstop.
//! The alternative was every touched file in, which put the corpus's layout
//! pass past the 30 s bound in every sample at once (#492).
//!
//! **A rotating cover nightly.** The whole nightly run is held to fifteen
//! minutes summed over its jobs, twenty at the most. A sweep that cannot
//! visit the whole corpus inside its share of that visits one slice of it a
//! night and covers the whole over the [`Nights`] it states beside its
//! sample: its whole cost on the nightly runner over its share. The slice is
//! a hash of the sweep's name and the source's corpus path
//! ([`Rotation::holds`]). The typing cannot rotate by source: its costliest
//! source alone types for longer than its share, so it types every source
//! each night, opened whole up to the night's part and typed through it,
//! each source cut into as many parts as its nights so each costs about that
//! fraction ([`Rotation::part`]). Either way the night is the UTC day, every
//! input is visited within the sweep's nights, the run prints the night it
//! visited, and `GANDR_SWEEP_NIGHT` replays it. A sweep cheap enough visits
//! the whole corpus every night. The alternatives were one night count for
//! every rotating sweep, which leaves the costliest past the budget or spreads
//! the cheaper ones thinner than they need; a stride over the keystrokes,
//! which never visits the text between its steps; shards across jobs, which
//! each pay the build again inside one summed budget; a raised timeout, which
//! spends the budget; and retiring a sweep, which no pull-request lane covers
//! whole.
//!
//! **Reversal**: a runner that takes the whole sweeps between nightlies, or
//! nextest's own test partitioning by input, makes the sample and the
//! rotation unnecessary.
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-sweep/README.md).

// Module documentation that predates the shape lint: 1 heading outside the
// vocabulary, 1 decision record, 2 issue references and 2 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]

extern crate alloc;

pub mod changed;
pub mod corpus;
pub mod coverage;
pub mod error;
pub mod rotation;
pub mod sample;

use anodized::spec;

pub use crate::changed::Changed;
pub use crate::corpus::Class;
pub use crate::corpus::CorpusName;
pub use crate::corpus::Source;
pub use crate::coverage::Coverage;
pub use crate::error::SweepError;
pub use crate::rotation::Held;
pub use crate::rotation::Night;
pub use crate::rotation::Nights;
pub use crate::rotation::Offset;
pub use crate::rotation::Part;
pub use crate::rotation::Rotation;
pub use crate::rotation::Slice;
pub use crate::rotation::Text;
pub use crate::sample::Sample;
pub use crate::sample::SampleName;
pub use crate::sample::SampleSize;

/// What a run asks a sweep to visit: its coverage, and, when sampled, the
/// sources the change touches, and, when whole, the slice a rotating sweep
/// visits.
///
/// # Specification
/// - provides: [`Sweep::visit`] and [`Sweep::visit_rotating`], the selections
///   every sweep test applies.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sweep
{
    /// The budget the run is in.
    coverage: Coverage,
    /// The changed corpus sources; empty under [`Coverage::Full`], which
    /// visits every one.
    changed: Changed,
    /// The slice a rotating sweep visits under [`Coverage::Full`];
    /// [`Rotation::Whole`] under [`Coverage::Sampled`], whose sample draws
    /// from every source.
    rotation: Rotation,
}

impl Sweep
{
    /// The sweep the running profile asks for.
    ///
    /// # Specification
    /// - requires: when sampled, as [`Changed::asked`].
    /// - ensures: the coverage [`Coverage::asked`] reads; when sampled, the
    ///   change [`Changed::asked`] lists against the corpus directory and the
    ///   whole rotation; when full, no change and the rotation
    ///   [`Rotation::asked`] reads.
    /// - provides: what a sweep test reads once before choosing its inputs.
    /// - fails: [`SweepError::Walk`] when the corpus directory cannot be
    ///   resolved, [`SweepError::Git`] when the change cannot be listed, and
    ///   [`SweepError::Night`] when the night cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the environment's and Git's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parts are witnessed where they live; this joins
    ///   them, and every sweep test runs it in both budgets.
    /// - witness: `tests::a_full_sweep_visits_every_candidate`
    #[inline]
    pub fn asked() -> Result<Self, SweepError>
    {
        let coverage = Coverage::asked();
        let (changed, rotation) = match coverage {
            Coverage::Full => (Changed::default(), Rotation::asked()?),
            Coverage::Sampled => {
                let changed = Changed::asked(&corpus::directory()?)?;
                (changed, Rotation::Whole)
            },
        };
        Ok(Self {
            coverage,
            changed,
            rotation,
        })
    }

    /// A sweep of `coverage` over a change touching `changed`, rotating as
    /// `rotation` says when full.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        coverage: Coverage,
        changed: Changed,
        rotation: Rotation,
    ) -> Self
    {
        Self {
            coverage,
            changed,
            rotation,
        }
    }

    /// The budget the run is in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn coverage(&self) -> Coverage
    {
        self.coverage
    }

    /// The slice a rotating sweep visits when full; a rotating sweep prints
    /// it, so its failure names the night it visited.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rotation(&self) -> Rotation
    {
        self.rotation
    }

    /// The candidates the sweep visits: every one under [`Coverage::Full`],
    /// `sample`'s selection otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `candidates` whole under [`Coverage::Full`];
    ///   [`Sample::select`] over the change otherwise.
    /// - provides: the sources a sweep test visits, in the candidates' order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full sweep returns every candidate and a sampled
    ///   one its sample's selection; swapping the arms changes a count.
    /// - witness: `tests::a_full_sweep_visits_every_candidate`
    #[spec(ensures: |ret| self.coverage != Coverage::Full || ret.len() == candidates.len())]
    #[inline]
    #[must_use]
    pub fn visit(
        &self,
        sample: Sample,
        candidates: &[Source],
    ) -> Vec<Source>
    {
        match self.coverage {
            Coverage::Full => candidates.to_vec(),
            Coverage::Sampled => sample.select(candidates, &self.changed),
        }
    }

    /// The candidates a rotating sweep visits: those the night's slice of
    /// `nights` holds under [`Coverage::Full`], `sample`'s selection
    /// otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: under [`Coverage::Full`], exactly the candidates
    ///   [`Rotation::holds`] for `sample`'s name over `nights`, every one under
    ///   [`Rotation::Whole`]; [`Sample::select`] over the change otherwise.
    /// - provides: the sources a sweep too costly to visit whole every night
    ///   visits, in the candidates' order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nightly sweep over the corpus on `nights`
    ///   consecutive nights, a whole one and a sampled one; a rotation applied
    ///   to a sampled run or ignored by a full one, or a night count ignored,
    ///   changes a count.
    /// - witness: `tests::a_rotating_sweep_covers_the_corpus_over_its_nights`
    #[spec(ensures: |ret| self.coverage != Coverage::Full || ret.len() == candidates.iter().filter(|candidate| self.rotation.holds(sample.name, nights, candidate) == Held::Tonight).count())]
    #[inline]
    #[must_use]
    pub fn visit_rotating(
        &self,
        sample: Sample,
        nights: Nights,
        candidates: &[Source],
    ) -> Vec<Source>
    {
        match self.coverage {
            Coverage::Full => candidates
                .iter()
                .filter(|candidate| {
                    self.rotation.holds(sample.name, nights, candidate) == Held::Tonight
                })
                .cloned()
                .collect(),
            Coverage::Sampled => sample.select(candidates, &self.changed),
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::Changed;
    use super::Coverage;
    use super::Night;
    use super::Nights;
    use super::Rotation;
    use super::Sample;
    use super::SampleName;
    use super::SampleSize;
    use super::Sweep;
    use super::corpus::sources;

    #[test]
    fn a_full_sweep_visits_every_candidate()
    {
        let corpus = sources().expect("the corpus reads");
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(3),
        };
        let tonight = Rotation::Night(Night(0));
        assert_eq!(
            Sweep::new(Coverage::Full, Changed::default(), tonight).visit(sample, &corpus),
            corpus,
            "a sweep that does not rotate visits everything on every night"
        );
        let sampled = Sweep::new(Coverage::Sampled, Changed::default(), Rotation::Whole)
            .visit(sample, &corpus);
        assert!(
            sampled.len() < corpus.len() && sampled.len() >= 3,
            "{} of {}",
            sampled.len(),
            corpus.len()
        );
        let asked = Sweep::asked().expect("the run's sweep resolves");
        assert_eq!(asked.coverage(), Coverage::asked());
    }

    #[test]
    fn a_rotating_sweep_covers_the_corpus_over_its_nights()
    {
        let corpus = sources().expect("the corpus reads");
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(3),
        };
        let nights = Nights(6);
        let mut visits = 0_usize;
        let mut covered = alloc::collections::BTreeSet::new();
        for night in 0 .. nights.0 {
            let sweep = Sweep::new(
                Coverage::Full,
                Changed::default(),
                Rotation::Night(Night(night)),
            );
            let visited = sweep.visit_rotating(sample, nights, &corpus);
            assert!(
                visited.len() < corpus.len(),
                "night {night} visits a slice: {} of {}",
                visited.len(),
                corpus.len()
            );
            visits = visits.saturating_add(visited.len());
            covered.extend(visited.into_iter().map(|source| source.name));
        }
        assert_eq!(visits, corpus.len(), "no source is visited twice");
        assert_eq!(covered.len(), corpus.len(), "every source is visited");
        assert_eq!(
            Sweep::new(Coverage::Full, Changed::default(), Rotation::Whole)
                .visit_rotating(sample, nights, &corpus),
            corpus,
            "the whole rotation visits every source"
        );
        let sampled = Sweep::new(
            Coverage::Sampled,
            Changed::default(),
            Rotation::Night(Night(0)),
        )
        .visit_rotating(sample, nights, &corpus);
        assert_eq!(
            sampled,
            sample.select(&corpus, &Changed::default()),
            "a sampled run draws its sample, whatever the night"
        );
    }
}
