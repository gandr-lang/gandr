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
use gandr_kernel_core::verdict::KernelSigner;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::VerdictCache;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::measure;
use gandr_surface_evaluate::Evaluator;
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
    let ControlFlow::Continue(_) = Walk::new(vec![path]).measuring().visit::<Evaluator, _, _>(
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
/// recalled and kept. The second recheck of the same text adopts each item,
/// molds no form and keeps each declaration that the first admitted (#6847),
/// so each row counts no judged item, no memo consult, no molded form, no
/// offer to the kernel and no kernel goal. A column read at the wrong
/// position, a pass that counted an adopted item as judged, a fold that added
/// the second recheck's counts to the first's, or a readmission that offered
/// a kept declaration again changes a row.
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
                crossed: 0,
            },
            "a second recheck adopts each item, molds no form and keeps each declaration: \
             {counts:?}"
        );
    }
    assert!(
        second.iter().all(|counts| kernel(counts)
            == Goals {
                expanded: 0,
                recalled: 0,
                kept: 0,
            }),
        "a kept declaration charges no kernel goal: {second:?}"
    );
}

/// #6536: two sessions judge two corpus sources laid out after the same
/// closure, each on its own thread, and recheck each unchanged text twice.
/// Both sessions lower the closure at once, and the process's store keeps
/// the lowering that the later keep gives it. The adoption of an item reads
/// only the session's own checkpoints and the content of the closure, so
/// each second recheck judges no item. A session that resumes after the
/// lead of the other session's lowering judges its first item again.
#[test]
fn a_second_recheck_judges_no_item_when_another_session_keeps_the_closure_6536()
{
    let sources = ["functions.gandr", "values.gandr"].map(|name| {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus/strict")
            .join(name);
        let text = std::fs::read_to_string(&path).expect("the corpus source is read");
        (path, text)
    });
    for round in 0_u8 .. 50 {
        std::thread::scope(|scope| {
            let runs = sources.each_ref().map(|&(ref path, ref text)| {
                scope.spawn(move || {
                    let mut session = session(SourceRoot::Strict);
                    let _first = recheck(&mut session, (path, Text(text)));
                    recheck(&mut session, (path, Text(text)))
                })
            });
            for (run, &(ref path, _)) in runs.into_iter().zip(&sources) {
                let second = run.join().expect("the session's thread ends");
                for counts in &second {
                    assert_eq!(
                        work(counts).judged,
                        0,
                        "round {round}: a second recheck of {} judges no item: {counts:?}",
                        path.display()
                    );
                }
            }
        });
    }
}

/// #6566: in a process that holds its kernel's verdicts, as the language
/// server does, the first recheck of a corpus source checks each declaration,
/// expanding goals, and records each one's verdict. The second and the third
/// recheck of the same text adopt each item and keep each declaration that
/// the first admitted (#6847). So no row of either expands, recalls or keeps a
/// goal. A readmission that offered a kept declaration again and checked it,
/// or a key that a recheck does not reproduce, changes a row.
#[test]
fn a_held_process_expands_no_goal_for_an_adopted_declaration_6566()
{
    gandr_surface_dispatcher::install_verdict_cache(VerdictCache::held(KernelSigner::from(
        [3_u8; 32],
    )))
    .expect("no cache is installed before the witness's");
    let path = source();
    let text = std::fs::read_to_string(&path).expect("the corpus source is read");
    let mut session = session(SourceRoot::Strict);
    let first = recheck(&mut session, (&path, Text(&text)));
    assert!(
        first.iter().all(|counts| work(counts).crossed == 1)
            && first.iter().any(|counts| kernel(counts).expanded > 0),
        "the first recheck offers each declaration and the kernel checks it: {first:?}"
    );
    let none = Goals {
        expanded: 0,
        recalled: 0,
        kept: 0,
    };
    // The second and the third readmission keep each declaration the first
    // admitted.
    for later in ["second", "third"] {
        let rows = recheck(&mut session, (&path, Text(&text)));
        assert_eq!(rows.len(), first.len(), "the same declarations hold rows");
        for counts in &rows {
            assert_eq!(
                (work(counts).judged, work(counts).crossed, kernel(counts)),
                (0, 0, none),
                "a {later} recheck adopts each item and expands no kernel goal: {counts:?}"
            );
        }
    }
}

/// #6847: a declaration inserted before the source's own declarations moves
/// each of them one place on. The readmission keeps each of them in place and
/// offers the kernel the inserted declaration alone. So the row of the
/// inserted declaration counts the one offer, and no other row counts an
/// offer or a kernel goal. A reader that counted a kept entry as offered
/// charges each row after the insertion with the goals of its earlier check.
#[test]
fn an_edit_charges_the_rows_of_its_reach_alone_6847()
{
    let path = source();
    let text = std::fs::read_to_string(&path).expect("the corpus source is read");
    let mut session = session(SourceRoot::Strict);
    let first = recheck(&mut session, (&path, Text(&text)));
    let inserted = format!("def inserted : Integer = 1; {text}");
    let rows = recheck(&mut session, (&path, Text(&inserted)));
    assert_eq!(
        rows.len(),
        first.len().saturating_add(1),
        "the inserted declaration holds a row"
    );
    let offered: Vec<usize> = rows
        .iter()
        .enumerate()
        .filter(|&(_, counts)| work(counts).crossed > 0)
        .map(|(at, _)| at)
        .collect();
    assert_eq!(
        offered,
        vec![0_usize],
        "the admission offers the inserted declaration alone: {rows:?}"
    );
    let none = Goals {
        expanded: 0,
        recalled: 0,
        kept: 0,
    };
    assert!(
        rows.iter().skip(1).all(|counts| kernel(counts) == none),
        "a kept declaration charges no kernel goal: {rows:?}"
    );
}
