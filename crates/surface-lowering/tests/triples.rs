//! The pairs of each reading of a block that a critical triple connects below
//! their peak, beside the pairs of the composite class.
//!
//! A critical pair is two steps `f` and `h` from its peak `s`. A third step
//! `g` from `s`, by a rule of the reading at a command position of `s`, makes
//! `f`, `g` and `h` a critical triple whose peak is `s`. The pairs `(f, g)`
//! and `(g, h)` then connect `f` and `h` through terms below `s`, which is the
//! chain criterion. So the confluence of the pair is a redundant cell, and the
//! triple is its partner. A third step strictly below the seam of the pair is
//! the composite criterion, so each composite pair is a connected pair. An
//! idle symmetry rewrites nothing, so it is no third step.
//!
//! # References
//!
//! - `Ara-2025-polygraphs_rewriting_higher_categories` — dependency: § 7.5, the
//!   reduction of a homotopy basis by its critical triples.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use std::path::Path;

use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::critical_triples;
use gandr_theory_computads::TermAlphabet;
use gandr_workflow_sweep::Sample;
use gandr_workflow_sweep::SampleName;
use gandr_workflow_sweep::SampleSize;
use gandr_workflow_sweep::Sweep;
use quenchant_shape::shape::Maybe;

use crate::squier::Kept;
use crate::squier::Reading;
use crate::squier::certified;
use crate::squier::each_block;
use crate::squier::readings;
use crate::squier::swept;

/// The steps of a triple, each as its position and its cell, in order: the
/// identity of a triple over the orders of its steps.
type TripleKey = Vec<(Vec<PositionStep>, CellId)>;

/// Where a pair of a reading has a third step from its peak.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Third
{
    /// No rule of the reading fires at the peak but the two of the pair.
    None,
    /// A rule fires at the peak, and none strictly below the seam.
    Beside,
    /// A rule fires strictly below the seam.
    Below,
}

/// The key of the three steps `steps`.
///
/// # Specification
/// trivial.
fn key<A>(steps: [(CellId, &A::Pos); 3]) -> TripleKey
where
    A: CellAlphabet,
{
    let mut key: TripleKey = steps
        .iter()
        .map(|&(cell, at)| (A::position_steps(at).to_vec(), cell))
        .collect();
    key.sort();
    key
}

/// The third steps of `overlap`: the cells of `rules` that match its peak at a
/// command position, other than the two steps of the pair. The answer is
/// [`Third::Below`] where one stands strictly below the seam, and whether the
/// three steps of one of them are a triple of `triples`.
///
/// # Specification
/// trivial.
fn third<A>(
    store: &CellStore<A>,
    rules: &BTreeSet<CellId>,
    overlap: &Overlap<A>,
    triples: &BTreeSet<TripleKey>,
) -> (Third, bool)
where
    A: CellAlphabet,
{
    let root = A::root_position();
    let held = [(overlap.left, &root), (overlap.right, &overlap.seam)];
    let mut found = Third::None;
    let mut partnered = false;
    for at in A::command_positions(&overlap.peak) {
        let Maybe::Present(subterm) = A::subterm_cmd_at(&overlap.peak, &at)
        else {
            continue;
        };
        for (id, cell) in store.iter() {
            if !rules.contains(&id)
                || held
                    .iter()
                    .any(|&(step, step_at)| step == id && *step_at == at)
            {
                continue;
            }
            let (lhs, _) =
                A::rename_apart((&overlap.peak, &overlap.peak), (cell.lhs(), cell.rhs()));
            if !bool::from(A::match_cmd(&lhs, &subterm, &mut A::Subst::default())) {
                continue;
            }
            partnered = partnered || triples.contains(&key::<A>([held[0], held[1], (id, &at)]));
            if A::position_order(&overlap.seam, &at) == PositionOrder::Encloses {
                found = Third::Below;
            }
            else if found == Third::None {
                found = Third::Beside;
            }
        }
    }
    (found, partnered)
}

/// The counts of one reading.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Counts
{
    /// The critical pairs of the reading: those that completion joins, and
    /// those that it skips as composite.
    pairs: usize,
    /// The pairs that completion skips as composite.
    composite: usize,
    /// The pairs with a third step from their peak.
    connected: usize,
    /// The connected pairs with no third step strictly below the seam.
    beside: usize,
    /// The connected pairs whose three steps are a critical triple of the
    /// store: the three left sides cover the peak and overlap. The others
    /// have a third step apart from the two of the pair.
    partnered: usize,
}

impl Counts
{
    /// Count one pair whose third step is `third`, with a critical triple as
    /// its partner where `partnered`.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &mut self,
        third: Third,
        partnered: bool,
    )
    {
        self.pairs = self.pairs.saturating_add(1);
        if partnered {
            self.partnered = self.partnered.saturating_add(1);
        }
        match third {
            Third::None => {},
            Third::Beside => {
                self.connected = self.connected.saturating_add(1);
                self.beside = self.beside.saturating_add(1);
            },
            Third::Below => self.connected = self.connected.saturating_add(1),
        }
    }
}

/// The counts of each reading with rules of each block of `text`. Each pair
/// that completion skips as composite has a third step below its seam. The
/// commands reading has no triple of its store in the count.
///
/// # Specification
/// trivial.
fn counted(text: &str) -> Vec<(Reading, Counts)>
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut out = Vec::new();
    let _lowering = each_block(&grammar, SourceText::from(text), |cells| {
        let Some(certificates) = certified(cells)
        else {
            return;
        };
        for (reading, read) in readings(cells, &certificates) {
            let Some(read) = read
            else {
                continue;
            };
            if read.rules.is_empty() {
                continue;
            }
            let mut counts = Counts::default();
            match reading {
                Reading::Terms => {
                    let Maybe::Present(ref presented) = cells.presented
                    else {
                        continue;
                    };
                    let store = &presented.store;
                    let rules: BTreeSet<CellId> = read.index.keys().copied().collect();
                    let triples: BTreeSet<TripleKey> = critical_triples(store)
                        .iter()
                        .map(|triple| {
                            let [ref first, ref second, ref last] = triple.steps;
                            key::<TermAlphabet>([
                                (first.cell, &first.at),
                                (second.cell, &second.at),
                                (last.cell, &last.at),
                            ])
                        })
                        .collect();
                    let composite = certificates
                        .composite_terms
                        .iter()
                        .map(|pair| (&pair.overlap, true));
                    let joined = certificates.terms.iter().map(|pair| (&pair.overlap, false));
                    for (overlap, skipped) in joined.chain(composite) {
                        let (found, partnered) = third(store, &rules, overlap, &triples);
                        if skipped {
                            assert_eq!(
                                found,
                                Third::Below,
                                "a composite pair has a third step below its seam: {:?}",
                                overlap.peak
                            );
                            counts.composite = counts.composite.saturating_add(1);
                        }
                        counts.add(found, partnered);
                    }
                },
                Reading::Commands => {
                    let store = cells.rewriting();
                    let rules: BTreeSet<CellId> =
                        read.index.keys().chain(&read.structural).copied().collect();
                    for pair in &certificates.commands {
                        let (found, _) = third(&store, &rules, &pair.overlap, &BTreeSet::new());
                        counts.add(found, false);
                    }
                },
            }
            out.push((reading, counts));
        }
    });
    out
}

/// The block of the laws of a group: the most pairs of the corpus.
const GROUP_LAWS: &str = "model/identity/group-laws.gandr";

/// The laws of a group: 607 pairs in one reading. Completion skips 295 as
/// composite. A triple connects 574 below their peak, and 228 of those have
/// their third step beside the seam, which the composite criterion does not
/// see. For 573 of the 574, the three steps are a critical triple of the
/// store, which is the partner of the pair.
#[test]
fn the_pairs_of_the_group_laws_that_a_triple_connects_below_their_peak()
{
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus")
        .join(GROUP_LAWS);
    let text = std::fs::read_to_string(&path).expect("the source reads");
    assert_eq!(counted(&text), [(Reading::Terms, Counts {
        pairs: 607,
        composite: 295,
        connected: 574,
        beside: 228,
        partnered: 573,
    })]);
}

/// The sample of the readings whose pairs are counted.
const COUNTED: Sample = Sample {
    name: SampleName("each_count_of_connected_pairs_is_within_the_pairs"),
    size: SampleSize(32),
};

/// Each reading of the sources that `sweep` asks for: each composite pair is
/// connected below its seam, a pair with a critical triple as its partner is
/// connected, and no reading has more connected pairs than pairs.
///
/// # Specification
/// trivial.
fn connected_pairs_are_within_the_pairs(sweep: &Sweep)
{
    for path in swept(sweep, COUNTED, &[Kept(GROUP_LAWS)]) {
        let text = std::fs::read_to_string(&path).expect("a corpus source reads");
        for (reading, counts) in counted(&text) {
            assert!(
                counts.composite <= counts.connected
                    && counts.partnered <= counts.connected
                    && counts.connected <= counts.pairs,
                "{}: {reading:?} {counts:?}",
                path.display()
            );
        }
    }
}

/// A pull request reads the sample, and the nightly reads the corpus whole.
mod sweeps
{
    use gandr_workflow_sweep::Sweep;

    use super::connected_pairs_are_within_the_pairs;

    #[test]
    fn each_count_of_connected_pairs_is_within_the_pairs()
    {
        connected_pairs_are_within_the_pairs(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn each_count_of_connected_pairs_is_within_the_pairs_changed()
    {
        connected_pairs_are_within_the_pairs(
            &Sweep::asked().expect("the run's sweep resolves").changed(),
        );
    }
}
