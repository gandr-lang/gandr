//! The counts layer: a recheck at the counts sink counts, in each row of the
//! account, what the engine did for the declaration, the checker's and the
//! kernel's apart.

use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::Polled;
use gandr_core_checker::Unretired;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::measure;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::Counts;
use gandr_surface_session::DeclarationCounts;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::Text;
use crate::common::session;

/// The corpus source the witness rechecks.
///
/// # Specification
/// trivial.
fn source() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus/strict/functions.gandr")
}

/// Judge `text`, the source at `path`, in `session` as the hub judges it:
/// laid out after its closure, the prelude first. The judgement runs at a
/// fresh counts sink, and the admission at another; then the settle. Answers
/// the counts of each row of the account, in order.
///
/// # Specification
/// trivial.
fn recheck(
    session: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>,
    (path, Text(text)): (&Path, Text<'_>),
) -> Vec<DeclarationCounts>
{
    let laid = lay_out(&GRAMMAR, path, SourceRoot::Strict, SourceText::from(text));
    let slot = ClosureSlot::new();
    let Ok(Polled::Whole(_)) = session.judge_unit_reading_retiring(
        SourceText::from(laid.text.as_str()),
        (&laid.unit, laid.base),
        &slot,
        |_| (),
        (&Unretired, &mut Counts::default()),
    )
    else {
        panic!("the revision is judged whole");
    };
    let Maybe::Present(detached) = session.admission()
    else {
        panic!("the judgement left its admission");
    };
    let ran = detached.run(&Unretired, &mut Counts::default()).whole();
    let Ok(Maybe::Present(_)) = session.settle(ran)
    else {
        panic!("the admission settles");
    };
    session
        .account()
        .rows()
        .map(|(constant, _, row)| match row.counts() {
            Maybe::Present(counts) => counts,
            Maybe::Absent(reason) => panic!("the row at {constant:?} is counted: {reason:?}"),
        })
        .collect()
}

/// The kernel's goals of one declaration's check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Goals
{
    /// The goals that the kernel expanded.
    expanded: u64,
    /// The goals that the kernel's memo recalled.
    recalled: u64,
    /// The goals that a kept outcome of an earlier admission answered.
    kept: u64,
}

/// A row's work before the kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Work
{
    /// The items that the incremental pass judged.
    judged: u64,
    /// The forms that the parse molded.
    molded: u64,
    /// The checker's memo hits.
    hits: u64,
    /// The checker's memo misses.
    misses: u64,
    /// The declarations that the admission offered to the kernel.
    crossed: u64,
}

/// Each declaration that `gandr check --measure` reads of the source, by
/// name, with the goals of the kernel's check of it.
///
/// # Specification
/// trivial.
fn measured(path: PathBuf) -> Vec<(String, Goals)>
{
    let mut goals = Vec::new();
    let ControlFlow::Continue(_) = Walk::new(vec![path]).measuring().visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source { ref composed, .. } = step
            else {
                panic!("the source is read: {step:?}");
            };
            let Composed::Settled { .. } = *composed
            else {
                panic!("the source is judged and admitted");
            };
            let Ok(Maybe::Present(rows)) = measure(composed)
            else {
                panic!("the source is measured");
            };
            for row in &rows {
                if let Maybe::Present(census) = row.census() {
                    goals.push((row.name().to_string(), Goals {
                        expanded: u64::from(census.expansions()),
                        recalled: u64::from(census.recalls()),
                        kept: u64::from(census.kept()),
                    }));
                }
            }
            ControlFlow::Continue(())
        },
    );
    goals
}

/// The kernel's goals of one row.
///
/// # Specification
/// trivial.
fn kernel(counts: &DeclarationCounts) -> Goals
{
    Goals {
        expanded: u64::from(counts.expanded()),
        recalled: u64::from(counts.recalled()),
        kept: u64::from(counts.kept()),
    }
}

/// A row's work before the kernel.
///
/// # Specification
/// trivial.
fn work(counts: &DeclarationCounts) -> Work
{
    Work {
        judged: u64::from(counts.judged()),
        molded: u64::from(counts.molded()),
        hits: u64::from(counts.hits()),
        misses: u64::from(counts.misses()),
        crossed: u64::from(counts.crossed()),
    }
}

/// A corpus source, laid out after the prelude as the hub lays it, rechecked
/// twice at the counts sink. The first recheck judges each declaration, molds
/// its form, consults the checker's memo and offers it to the kernel after
/// the prelude's declarations, so each row's kernel goals are the goals that
/// `gandr check --measure` reads of the same declaration: as many expanded,
/// recalled and kept. The second recheck of the same text adopts each item
/// and molds no form, so each row counts no judged item, no memo consult and
/// no molded form, and the admission offers each declaration to the kernel
/// again. That readmission resumes after the prelude from its record, which
/// hands on the outcomes that the prelude's admission kept, so each row
/// charges the goals of the measure again. A column read at the wrong
/// position, a pass that counted an adopted item as judged, a fold that added
/// the second recheck's counts to the first's, or a record that hands on no
/// kept outcome (#6468) changes a row.
#[test]
fn a_second_recheck_counts_no_judged_item()
{
    let path = source();
    let text = std::fs::read_to_string(&path).expect("the corpus source is read");
    let mut session = session(SourceRoot::Strict);
    let first = recheck(&mut session, (&path, Text(&text)));
    assert!(
        !first.is_empty(),
        "the source declares something of its own"
    );
    for counts in &first {
        let done = work(counts);
        assert_eq!(
            (done.judged, done.molded, done.crossed),
            (1, 1, 1),
            "a first recheck judges, molds and offers each declaration: {counts:?}"
        );
        assert!(
            done.hits.saturating_add(done.misses) > 0 && u64::from(counts.nodes()) > 0,
            "each judgement consults the memo and names nodes: {counts:?}"
        );
    }
    let walked = measured(path.clone());
    assert_eq!(
        first.iter().map(kernel).collect::<Vec<_>>(),
        walked.iter().map(|&(_, goals)| goals).collect::<Vec<_>>(),
        "each row charges the goals the measure reads of its declaration: {walked:?}"
    );
    let second = recheck(&mut session, (&path, Text(&text)));
    assert_eq!(second.len(), first.len(), "the same declarations hold rows");
    for counts in &second {
        assert_eq!(
            work(counts),
            Work {
                judged: 0,
                molded: 0,
                hits: 0,
                misses: 0,
                crossed: 1,
            },
            "a second recheck adopts each item and molds no form: {counts:?}"
        );
    }
    assert_eq!(
        second.iter().map(kernel).collect::<Vec<_>>(),
        walked.iter().map(|&(_, goals)| goals).collect::<Vec<_>>(),
        "the resumed readmission charges each row the goals the measure reads: {walked:?}"
    );
}
