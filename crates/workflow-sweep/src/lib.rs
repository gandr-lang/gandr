//! **Sweeps**: the corpus sources a sweep test visits. A sweep drives the
//! whole corpus through one feature — typing and erasing every source,
//! formatting it, molding every token drop — and runs in two budgets: a
//! stated sample on every pull request and every merge-queue entry, plain
//! and with specifications enforced, within the 30 s every test is held to,
//! and the whole corpus nightly under the `sweeps` nextest profile.
//!
//! - [`coverage`] reads which budget a run is in from the nextest profile.
//! - [`corpus`] walks the corpus and names each source's class.
//! - [`changed`] lists the corpus sources a change touches.
//! - [`sample`] draws a sample's hashed, stratified slice.
//!
//! A sweep test asks [`Sweep::asked`] once, filters [`corpus::sources`] to
//! its candidates, and visits what [`Sweep::visit`] returns:
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
//! test in `NEXTEST_PROFILE`; the `sweeps` profile means the whole corpus and
//! every other profile, or a run outside nextest, the sample. A sweep is
//! selected by the `sweeps` module it sits in, so that profile's filter names
//! no test. The alternative was a variable per lane, which a task forgets to
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
//! **Reversal**: a runner that takes the whole sweeps between nightlies, or
//! nextest's own test partitioning by input, makes the sample unnecessary.
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-sweep/README.md).

extern crate alloc;

pub mod changed;
pub mod corpus;
pub mod coverage;
pub mod error;
pub mod sample;

use anodized::spec;

pub use crate::changed::Changed;
pub use crate::corpus::Class;
pub use crate::corpus::CorpusName;
pub use crate::corpus::Source;
pub use crate::coverage::Coverage;
pub use crate::error::SweepError;
pub use crate::sample::Sample;
pub use crate::sample::SampleName;
pub use crate::sample::SampleSize;

/// What a run asks a sweep to visit: its coverage, and, when sampled, the
/// sources the change touches.
///
/// # Specification
/// - provides: [`Sweep::visit`], the one selection every sweep test applies.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sweep
{
    /// The budget the run is in.
    coverage: Coverage,
    /// The changed corpus sources; empty under [`Coverage::Full`], which
    /// visits every one.
    changed: Changed,
}

impl Sweep
{
    /// The sweep the running profile asks for.
    ///
    /// # Specification
    /// - requires: when sampled, as [`Changed::asked`].
    /// - ensures: the coverage [`Coverage::asked`] reads; when sampled, the
    ///   change [`Changed::asked`] lists against the corpus directory.
    /// - provides: what a sweep test reads once before choosing its inputs.
    /// - fails: [`SweepError::Walk`] when the corpus directory cannot be
    ///   resolved, and [`SweepError::Git`] when the change cannot be listed.
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
        let changed = match coverage {
            Coverage::Full => Changed::default(),
            Coverage::Sampled => Changed::asked(&corpus::directory()?)?,
        };
        Ok(Self { coverage, changed })
    }

    /// A sweep of `coverage` over a change touching `changed`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        coverage: Coverage,
        changed: Changed,
    ) -> Self
    {
        Self { coverage, changed }
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
}

#[cfg(test)]
mod tests
{
    use super::Changed;
    use super::Coverage;
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
        assert_eq!(
            Sweep::new(Coverage::Full, Changed::default()).visit(sample, &corpus),
            corpus
        );
        let sampled = Sweep::new(Coverage::Sampled, Changed::default()).visit(sample, &corpus);
        assert!(
            sampled.len() < corpus.len() && sampled.len() >= 3,
            "{} of {}",
            sampled.len(),
            corpus.len()
        );
        let asked = Sweep::asked().expect("the run's sweep resolves");
        assert_eq!(asked.coverage(), Coverage::asked());
    }
}
