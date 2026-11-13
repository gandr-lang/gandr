//! Throwaway #7231 probe: the cost of a clone of a revision's admission, and
//! of the whole readmission that a background build runs over the clone.

use std::time::Instant;

use gandr_core_checker::HostGrant;
use gandr_core_checker::Unretired;
use gandr_core_checker::bridge;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Reuse;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::judge;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::built_in;
use gandr_surface_session::FormCount;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::large::module;

fn rank(
    sorted: &[u128],
    percent: usize,
) -> u128
{
    let at = (sorted.len() * percent).div_ceil(100).saturating_sub(1);
    sorted[at.min(sorted.len() - 1)]
}

fn forms() -> usize
{
    std::env::var("PROBE_FORMS")
        .ok()
        .and_then(|forms| forms.parse().ok())
        .unwrap_or(2_000)
}

fn editor(
    root: SourceRoot
) -> gandr_surface_session::Session<
    gandr_core_incremental::DiscardingCheckpointStore,
    gandr_storage_records::InMemoryBlockStore,
>
{
    gandr_surface_session::Session::new(
        crate::common::grammar(),
        root,
        gandr_core_incremental::DiscardingCheckpointStore,
        gandr_storage_records::InMemoryBlockStore::default(),
        crate::common::backend(),
    )
}

#[test]
#[ignore = "probe"]
fn probe_7231_clone()
{
    let grammar = built_in().expect("the built-in grammar builds");
    for forms in [400_usize, 2_000] {
        let generated = module(FormCount::from(forms), SourceRoot::Strict);
        let text = generated.text();
        let Lowered::Module { module, arena } = lower_source(
            &grammar,
            SourceText::from(text.as_str()),
            &mut LoweringCount::default(),
        )
        .expect("the module lowers")
        .into_lowered()
        else {
            panic!("the module is not refused whole");
        };
        let admission = judge::<Evaluator>(
            CorpusRoot::Strict,
            (module, SourceText::from(text.as_str())),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .into_parts()
        .1;
        let mut clones = Vec::new();
        for _ in 0 .. 30 {
            let started = Instant::now();
            let cloned = admission.clone();
            clones.push(started.elapsed().as_nanos());
            drop(cloned);
        }
        clones.sort_unstable();
        let mut cloned = None;
        let clone_heap = allocation_counter::measure(|| cloned = Some(admission.clone()));
        drop(cloned);
        let mut builds = Vec::new();
        let mut build_peak = 0_u64;
        for _ in 0 .. 10 {
            let copy = admission.clone();
            let started = Instant::now();
            let mut wall = 0_u128;
            let heap = allocation_counter::measure(|| {
                let polled = copy.admit_retiring(
                    Reuse::Leading(
                        bridge::LeadingCount::NONE,
                        Maybe::Absent(bridge::crossed::Absent::Unasked),
                    ),
                    &Unretired,
                );
                wall = started.elapsed().as_nanos();
                drop(polled);
            });
            builds.push(wall);
            build_peak = build_peak.max(heap.bytes_max);
        }
        builds.sort_unstable();
        println!(
            "PROBE7231 forms={forms} clone_us p50={} p99={} clone_bytes={} build_ms p50={:.1} p99={:.1} build_peak_bytes={build_peak}",
            rank(&clones, 50) / 1_000,
            rank(&clones, 99) / 1_000,
            clone_heap.bytes_total,
            rank(&builds, 50) as f64 / 1.0e6,
            rank(&builds, 99) as f64 / 1.0e6,
        );
    }
}

#[test]
#[ignore = "probe"]
fn probe_7231_long()
{
    use std::num::NonZeroUsize;
    use std::sync::Arc;

    use gandr_core_checker::bridge::Outgrown;
    use gandr_surface_dispatcher::Pool;
    use gandr_surface_dispatcher::Threads;
    use gandr_surface_dispatcher::Width;

    use crate::large::FormEdit;
    use crate::large::Position;

    let threads: usize = std::env::var("PROBE_THREADS")
        .ok()
        .and_then(|threads| threads.parse().ok())
        .unwrap_or(4);
    let edits: usize = std::env::var("PROBE_EDITS")
        .ok()
        .and_then(|edits| edits.parse().ok())
        .unwrap_or(400);
    let forms = forms();
    let root = SourceRoot::Strict;
    let mut generated = module(FormCount::from(forms), root);
    let pool = Arc::new(Pool::new(Width::Threads(Threads::from(
        NonZeroUsize::new(threads).unwrap(),
    ))));
    let mut session = crate::common::session(root).with_pool(pool);
    let text = generated.text();
    let _judged = session
        .judge(SourceText::from(text.as_str()))
        .expect("the module is judged");
    let _admitted = session.admit();
    let counts = |session: &gandr_surface_session::Session<
        gandr_core_incremental::MemoryCheckpointStore,
        gandr_storage_records::InMemoryBlockStore,
    >| match session.record() {
        Maybe::Present(record) => {
            let entries = record.environment().entries();
            let retired = usize::from(entries.retired());
            (
                retired,
                usize::from(entries.admitted()).saturating_sub(retired),
                format!("{:?}", record.environment().arena().watermark()),
                record.outgrown(),
            )
        },
        Maybe::Absent(_) => (0, 0, String::new(), Outgrown::Within),
    };
    let (mut starts, mut flight, mut none) = (Vec::new(), Vec::new(), Vec::new());
    let mut building = false;
    let mut swaps = 0_usize;
    for step in 0 .. edits {
        let edit = match step % 4 {
            0 => FormEdit::Change(Position(step * 37)),
            1 => FormEdit::Insert(Position(step * 53)),
            2 => FormEdit::Delete(Position(step * 53)),
            _ => FormEdit::Move(Position(step * 11), Position(step * 29)),
        };
        generated.edit(&edit);
        let text = generated.text();
        let (retired_before, _, _, outgrown) = counts(&session);
        let _judged = session
            .judge(SourceText::from(text.as_str()))
            .expect("the revision is judged");
        let started = Instant::now();
        let Maybe::Present(detached) = session.admission()
        else {
            panic!("the judgement left its admission");
        };
        let (retired_swapped, ..) = counts(&session);
        if building && retired_swapped < retired_before {
            swaps += 1;
            building = false;
        }
        let ran = detached
            .run(
                &gandr_core_checker::Unretired,
                &mut gandr_surface_session::Silent,
            )
            .whole();
        let _settled = session.settle(ran);
        let wall = started.elapsed().as_nanos();
        if outgrown == Outgrown::Reached && retired_swapped >= retired_before {
            starts.push(wall);
            building = true;
        }
        else if building {
            flight.push(wall);
        }
        else {
            none.push(wall);
        }
        if step % 25 == 24 {
            let (retired, live, arena, _) = counts(&session);
            println!(
                "PROBE7231L step={} retired={retired} live={live} arena={arena} swaps={swaps}",
                step + 1
            );
        }
    }
    for (class, walls) in [
        ("starts", &mut starts),
        ("flight", &mut flight),
        ("none", &mut none),
    ] {
        walls.sort_unstable();
        if walls.is_empty() {
            println!("PROBE7231L class={class} n=0");
            continue;
        }
        println!(
            "PROBE7231L class={class} n={} p50={:.2} ms p99={:.2} ms",
            walls.len(),
            rank(walls, 50) as f64 / 1.0e6,
            rank(walls, 99) as f64 / 1.0e6,
        );
    }
    println!("PROBE7231L threads={threads} edits={edits} swaps={swaps}");
}

#[test]
#[ignore = "probe"]
fn probe_7231_flight()
{
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use crate::large::FormEdit;
    use crate::large::Position;

    let edits: usize = std::env::var("PROBE_EDITS")
        .ok()
        .and_then(|edits| edits.parse().ok())
        .unwrap_or(200);
    let forms = forms();
    let root = SourceRoot::Strict;
    let grammar = built_in().expect("the built-in grammar builds");
    let mut generated = module(FormCount::from(forms), root);
    let text = generated.text();
    let Lowered::Module {
        module: lowered,
        arena,
    } = lower_source(
        &grammar,
        SourceText::from(text.as_str()),
        &mut LoweringCount::default(),
    )
    .expect("the module lowers")
    .into_lowered()
    else {
        panic!("the module is not refused whole");
    };
    let admission = judge::<Evaluator>(
        CorpusRoot::Strict,
        (lowered, SourceText::from(text.as_str())),
        arena,
        &HostGrant::UNBOUNDED,
    )
    .into_parts()
    .1;
    let active = Arc::new(AtomicBool::new(false));
    let stop = Arc::new(AtomicBool::new(false));
    let builds = Arc::new(AtomicUsize::new(0));
    let builder = {
        let (active, stop, builds) = (Arc::clone(&active), Arc::clone(&stop), Arc::clone(&builds));
        std::thread::spawn(move || {
            while !stop.load(Ordering::Acquire) {
                if active.load(Ordering::Acquire) {
                    drop(admission.clone().admit_retiring(
                        Reuse::Leading(
                            bridge::LeadingCount::NONE,
                            Maybe::Absent(bridge::crossed::Absent::Unasked),
                        ),
                        &Unretired,
                    ));
                    builds.fetch_add(1, Ordering::Relaxed);
                }
                else {
                    std::thread::sleep(std::time::Duration::from_micros(100));
                }
            }
        })
    };
    let mut session = crate::common::session(root);
    let _judged = session
        .judge(SourceText::from(text.as_str()))
        .expect("the module is judged");
    let _admitted = session.admit();
    let (mut flight, mut none) = (Vec::new(), Vec::new());
    for step in 0 .. edits {
        generated.edit(&FormEdit::Change(Position(step * 37)));
        let text = generated.text();
        let _judged = session
            .judge(SourceText::from(text.as_str()))
            .expect("the revision is judged");
        let in_flight = step % 2 == 1;
        active.store(in_flight, Ordering::Release);
        if in_flight {
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        let started = Instant::now();
        let _admitted = session.admit();
        let wall = started.elapsed().as_nanos();
        active.store(false, Ordering::Release);
        if in_flight {
            flight.push(wall)
        }
        else {
            none.push(wall)
        }
    }
    stop.store(true, Ordering::Release);
    builder.join().expect("the builder ends");
    for (class, walls) in [("flight", &mut flight), ("none", &mut none)] {
        walls.sort_unstable();
        println!(
            "PROBE7231F class={class} n={} p50={:.2} ms p99={:.2} ms",
            walls.len(),
            rank(walls, 50) as f64 / 1.0e6,
            rank(walls, 99) as f64 / 1.0e6,
        );
    }
    println!("PROBE7231F builds={}", builds.load(Ordering::Relaxed));
}

#[test]
#[ignore = "probe"]
fn probe_7231_commit()
{
    let forms = forms();
    let root = SourceRoot::Strict;
    let grammar = built_in().expect("the built-in grammar builds");
    let generated = module(FormCount::from(forms), root);
    let text = generated.text();
    let Lowered::Module {
        module: lowered,
        arena,
    } = lower_source(
        &grammar,
        SourceText::from(text.as_str()),
        &mut LoweringCount::default(),
    )
    .expect("the module lowers")
    .into_lowered()
    else {
        panic!("the module is not refused whole");
    };
    let admission = judge::<Evaluator>(
        CorpusRoot::Strict,
        (lowered, SourceText::from(text.as_str())),
        arena,
        &HostGrant::UNBOUNDED,
    )
    .into_parts()
    .1;
    let declarations = admission.verdicts().judged().len();
    let keys = vec![Maybe::Absent(bridge::keyed::Absent::Opaque); declarations];
    let copy = admission.clone();
    let copied = allocation_counter::measure(|| drop(admission.clone()));
    let mut record = None;
    let mut artifact = None;
    let made = allocation_counter::measure(|| {
        let gandr_core_checker::Polled::Whole(resumption) = copy.admit_retiring(
            Reuse::Keeping(&keys, Maybe::Absent(bridge::crossed::Absent::Unasked)),
            &Unretired,
        );
        artifact = resumption.artifact.ok();
        record = Some(resumption.crossed);
    });
    let artifact = artifact.expect("the kernel re-derives the module");
    let committed = artifact.as_ref().len();
    let mut decoded = None;
    let started = Instant::now();
    let loaded = allocation_counter::measure(|| {
        decoded = Some(gandr_kernel_term::decode(artifact.as_image()).expect("the image decodes"));
    });
    let load_us = started.elapsed().as_micros();
    let held = i64::try_from(made.bytes_current).unwrap()
        + i64::try_from(copied.bytes_total).unwrap()
        - i64::try_from(committed).unwrap();
    println!(
        "PROBE7231C forms={forms} declarations={declarations} committed={committed} \
         record_about={held} made_current={} copy={} load_current={} load_peak={} load_us={load_us} present={}",
        made.bytes_current,
        copied.bytes_total,
        loaded.bytes_current,
        loaded.bytes_max,
        record.is_some_and(|record| matches!(record, Maybe::Present(_))),
    );
}

#[test]
#[ignore = "probe"]
fn probe_7231_resident()
{
    use crate::large::FormEdit;
    use crate::large::Position;

    let forms: usize = std::env::var("PROBE_FORMS")
        .ok()
        .and_then(|forms| forms.parse().ok())
        .unwrap_or(2_000);
    let edits: usize = std::env::var("PROBE_EDITS")
        .ok()
        .and_then(|edits| edits.parse().ok())
        .unwrap_or(400);
    let root = SourceRoot::Strict;
    let mut last = String::new();
    let mut kept = None;
    let started = Instant::now();
    let resident = allocation_counter::measure(|| {
        let mut generated = module(FormCount::from(forms), root);
        let mut session = editor(root);
        let _judged = session
            .judge(SourceText::from(generated.text().as_str()))
            .expect("the module is judged");
        drop(session.admit());
        for step in 0 .. edits {
            let edit = match step % 4 {
                0 => FormEdit::Change(Position(step * 37)),
                1 => FormEdit::Insert(Position(step * 53)),
                2 => FormEdit::Delete(Position(step * 53)),
                _ => FormEdit::Move(Position(step * 11), Position(step * 29)),
            };
            generated.edit(&edit);
            let _judged = session
                .judge(SourceText::from(generated.text().as_str()))
                .expect("the revision is judged");
            drop(session.admit());
        }
        last = generated.text();
        kept = Some(session);
    });
    let wall = started.elapsed().as_millis();
    let mut whole = None;
    let fresh = allocation_counter::measure(|| {
        let mut session = editor(root);
        let _judged = session
            .judge(SourceText::from(last.as_str()))
            .expect("the last revision is judged");
        drop(session.admit());
        whole = Some(session);
    });
    println!(
        "PROBE7231R forms={forms} edits={edits} resident={} whole={} text={} wall_ms={wall}",
        resident.bytes_current,
        fresh.bytes_current,
        last.capacity(),
    );
}
