//! The timings layer: a recheck at the timings sink samples each phase of the
//! document and each declaration it judges or admits, and a ring folds its
//! last window of samples into its p50 and its p99.

use alloc::collections::BTreeSet;
use core::time::Duration;

use gandr_core_checker::Polled;
use gandr_core_checker::Unretired;
use gandr_core_checker::bridge::AllocationCount;
use gandr_core_checker::bridge::Spent;
use gandr_core_checker::bridge::metered;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_kernel_term::ConstantIndex;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_session::Phase;
use gandr_surface_session::RowRings;
use gandr_surface_session::SampleRing;
use gandr_surface_session::Session;
use gandr_surface_session::Timings;
use gandr_surface_session::WINDOW;
use gandr_surface_session::untimed;
use gandr_surface_syntax::SourceText;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use crate::common::session;

/// The source the witnesses recheck, judged on its own: it leads with no
/// closure, so no other session of the process shares a run of closure
/// declarations with it.
const SOURCE: &str = include_str!("../../surface-corpus/strict/functions.gandr");

/// Judge [`SOURCE`] in `session` at a fresh timings sink, then admit it at
/// another and settle. Answers the position of each item that the judgement
/// judged.
///
/// # Specification
/// trivial.
fn recheck(
    session: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>
) -> BTreeSet<ConstantIndex>
{
    let mut judging = Timings::default();
    let Ok(Polled::Whole(_)) = session.judge_reading_retiring(
        SourceText::from(SOURCE),
        |_| (),
        (&Unretired, &mut judging),
    )
    else {
        panic!("the revision is judged whole");
    };
    let judged = judging
        .column()
        .judged()
        .iter()
        .map(|&(constant, _)| constant)
        .collect();
    let Maybe::Present(detached) = session.admission()
    else {
        panic!("the judgement left its admission");
    };
    let ran = detached.run(&Unretired, &mut Timings::default()).whole();
    let Ok(Maybe::Present(_)) = session.settle(ran)
    else {
        panic!("the admission settles");
    };
    judged
}

/// The rings of each row of the account, by its position, in order.
///
/// # Specification
/// trivial.
fn rows(
    session: &Session<MemoryCheckpointStore, InMemoryBlockStore>
) -> Vec<(ConstantIndex, RowRings)>
{
    let account = session.account();
    account
        .rows()
        .map(|(constant, ..)| match account.timings_at(constant) {
            Maybe::Present(rings) => (constant, rings.clone()),
            Maybe::Absent(reason) => panic!("the row at {constant:?} is sampled: {reason:?}"),
        })
        .collect()
}

/// The sum of the walls a ring holds.
///
/// # Specification
/// trivial.
fn total(ring: &SampleRing) -> Duration
{
    ring.samples()
        .map(|sample| sample.wall())
        .fold(Duration::ZERO, Duration::saturating_add)
}

/// The phases a recheck runs for the document.
const PHASES: [Phase; 4] = [Phase::Parse, Phase::Lower, Phase::Judge, Phase::Admit];

/// A corpus source, judged on its own, rechecked
/// twice at the timings sink. After each recheck each phase of the document
/// holds one more sample. The first recheck judges and admits each
/// declaration, so each row holds one sample of each. The second recheck of
/// the same text adopts the items whose checkpoints hold, and a row's
/// judgement ring grows by one sample exactly when the pass judged its item
/// again. The admission offers each declaration to the kernel again, so each
/// row holds a second admission sample. The pass judges each item inside the
/// judgement, and the kernel admits each declaration inside the admission, so
/// the rows' samples of the first recheck sum to no more than the document's
/// sample of that phase. A pass that sampled an adopted item, a boundary read
/// outside its phase, a sample kept at the wrong row, or an account that lost a
/// ring between rechecks changes a count or breaks a sum.
#[test]
fn a_recheck_samples_each_phase_and_each_judged_declaration()
{
    let mut session = session(SourceRoot::Strict);
    let _judged = recheck(&mut session);
    let document = session.account().document_timings().clone();
    for phase in PHASES {
        assert_eq!(
            usize::from(document.ring(phase).held()),
            1,
            "the first recheck samples the {phase:?} of the document once"
        );
    }
    let first = rows(&session);
    assert!(
        !first.is_empty(),
        "the source declares something of its own"
    );
    for &(constant, ref rings) in &first {
        assert_eq!(
            (
                usize::from(rings.judge().held()),
                usize::from(rings.admit().held())
            ),
            (1, 1),
            "the first recheck judges and admits the declaration at {constant:?} once: {rings:?}"
        );
    }
    for phase in [Phase::Judge, Phase::Admit] {
        let rows_total = first
            .iter()
            .map(|&(_, ref rings)| {
                total(if phase == Phase::Judge {
                    rings.judge()
                }
                else {
                    rings.admit()
                })
            })
            .fold(Duration::ZERO, Duration::saturating_add);
        assert!(
            rows_total <= total(document.ring(phase)),
            "the rows' {phase:?} samples, {rows_total:?}, fall inside the document's: {document:?}"
        );
    }
    let judged = recheck(&mut session);
    for phase in PHASES {
        assert_eq!(
            usize::from(session.account().document_timings().ring(phase).held()),
            2,
            "the second recheck samples the {phase:?} of the document once more"
        );
    }
    let second = rows(&session);
    assert_eq!(second.len(), first.len(), "the same declarations hold rows");
    assert!(
        first
            .iter()
            .any(|&(constant, _)| !judged.contains(&constant)),
        "the second recheck adopts an item of its own: it judged {judged:?}"
    );
    for (&(constant, ref before), &(_, ref after)) in first.iter().zip(&second) {
        assert_eq!(
            usize::from(after.judge().held()),
            usize::from(before.judge().held())
                .saturating_add(usize::from(judged.contains(&constant))),
            "the judgement ring of {constant:?} grows exactly when the pass judged it: {judged:?}"
        );
        assert_eq!(
            usize::from(after.admit().held()),
            1,
            "the second admission keeps each declaration and samples no admission of it: \
             {after:?}"
        );
    }
}

/// This test process installs no counting allocator, so the dispatcher's
/// probe finds no count, and each sample of a recheck says that it counted no
/// allocation, rather than a count of zero. Each ring's fold then answers
/// the walls' percentiles and no allocations' percentiles. A sink that read
/// the meter of an uncounting process, or a fold that answered zero
/// allocations for an unmetered ring, breaks the comparison.
#[test]
fn a_process_with_no_counting_allocator_counts_no_allocation()
{
    let mut session = session(SourceRoot::Strict);
    let _judged = recheck(&mut session);
    let document = session.account().document_timings().clone();
    let rows = rows(&session);
    let rings = PHASES.iter().map(|&phase| document.ring(phase)).chain(
        rows.iter()
            .flat_map(|&(_, ref rings)| [rings.judge(), rings.admit()]),
    );
    for ring in rings {
        for sample in ring.samples() {
            assert_eq!(
                sample.allocations(),
                Maybe::Absent(metered::Absent::Unmetered),
                "an uncounting process counts no allocation: {ring:?}"
            );
        }
        let Maybe::Present(spread) = ring.spread()
        else {
            panic!("a sampled ring folds: {ring:?}");
        };
        assert_eq!(
            spread.allocations(),
            Maybe::Absent(metered::Absent::Unmetered),
            "an unmetered ring folds no allocations: {ring:?}"
        );
    }
}

/// A percent of a percentile.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Percent(usize);

/// The nearest-rank percentile `percent` of the sorted `values`.
///
/// # Specification
/// trivial.
fn nearest<T>(
    values: &[T],
    Percent(percent): Percent,
) -> T
where
    T: Copy + Ord,
{
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let rank = sorted.len().saturating_mul(percent).div_ceil(100).max(1);
    sorted[rank.saturating_sub(1)]
}

proptest! {
    /// Any sequence of up to 80 samples, each counted or not, pushed into a
    /// ring. The ring reads back the last 32 in order, and its latest is the
    /// last pushed. Its fold answers the nearest-rank p50 and p99 of a sorted
    /// copy of the walls it holds, and of their counts when each counted,
    /// else no count. A slot read off by one, a window that kept a sample
    /// older than the last 32, a selection at the wrong rank, or a fold that
    /// counted an unmetered sample as zero breaks the comparison.
    #[test]
    fn a_ring_folds_its_last_window_into_its_p50_and_p99(
        pushed in prop::collection::vec(
            (0_u64 .. 1_000_000, prop::option::of(0_u64 .. 10_000)),
            0 ..= 80,
        )
    ) {
        let samples: Vec<Spent> = pushed
            .iter()
            .map(|&(nanos, allocations)| Spent::new(
                Duration::from_nanos(nanos),
                allocations.map_or(
                    Maybe::Absent(metered::Absent::Unmetered),
                    |count| Maybe::Present(AllocationCount::from(count)),
                ),
            ))
            .collect();
        let mut ring = SampleRing::default();
        for &sample in &samples {
            ring.push(sample);
        }
        let window = &samples[samples.len().saturating_sub(WINDOW) ..];
        prop_assert_eq!(usize::from(ring.held()), window.len());
        prop_assert_eq!(ring.samples().collect::<Vec<_>>(), window.to_vec());
        match window.last() {
            None => {
                prop_assert_eq!(ring.latest(), Maybe::Absent(untimed::Absent::Unsampled));
                prop_assert_eq!(ring.spread(), Maybe::Absent(untimed::Absent::Unsampled));
            },
            Some(&last) => {
                prop_assert_eq!(ring.latest(), Maybe::Present(last));
                let Maybe::Present(spread) = ring.spread()
                else {
                    panic!("a sampled ring folds");
                };
                let walls: Vec<Duration> = window.iter().map(Spent::wall).collect();
                prop_assert_eq!(usize::from(spread.held()), window.len());
                prop_assert_eq!(
                    (spread.wall().p50(), spread.wall().p99()),
                    (nearest(&walls, Percent(50)), nearest(&walls, Percent(99)))
                );
                let counts: Option<Vec<AllocationCount>> = window
                    .iter()
                    .map(|sample| match sample.allocations() {
                        Maybe::Present(count) => Some(count),
                        Maybe::Absent(_) => None,
                    })
                    .collect();
                if let Some(counts) = counts {
                    let Maybe::Present(allocations) = spread.allocations()
                    else {
                        panic!("a ring of counted samples folds its counts");
                    };
                    prop_assert_eq!(
                        (allocations.p50(), allocations.p99()),
                        (nearest(&counts, Percent(50)), nearest(&counts, Percent(99)))
                    );
                }
                else {
                    prop_assert_eq!(
                        spread.allocations(),
                        Maybe::Absent(metered::Absent::Unmetered)
                    );
                }
            },
        }
    }
}
