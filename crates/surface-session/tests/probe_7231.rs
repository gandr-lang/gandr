//! Throwaway #7231 probe, before the change: the same long session, its
//! admission walls and its record's retired and live entries.

use std::num::NonZeroUsize;
use std::sync::Arc;
use std::time::Instant;

use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Width;
use gandr_surface_session::FormCount;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::large::FormEdit;
use crate::large::Position;
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
fn probe_7231_long()
{
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
    let mut walls = Vec::new();
    for step in 0 .. edits {
        let edit = match step % 4 {
            0 => FormEdit::Change(Position(step * 37)),
            1 => FormEdit::Insert(Position(step * 53)),
            2 => FormEdit::Delete(Position(step * 53)),
            _ => FormEdit::Move(Position(step * 11), Position(step * 29)),
        };
        generated.edit(&edit);
        let text = generated.text();
        let _judged = session
            .judge(SourceText::from(text.as_str()))
            .expect("the revision is judged");
        let started = Instant::now();
        let _admitted = session.admit();
        walls.push(started.elapsed().as_nanos());
        if step % 25 == 24 {
            let (retired, live, arena) = match session.record() {
                Maybe::Present(record) => {
                    let entries = record.environment().entries();
                    let live = entries.iter().count();
                    (
                        usize::from(entries.admitted()).saturating_sub(live),
                        live,
                        format!("{:?}", record.environment().arena().watermark()),
                    )
                },
                Maybe::Absent(_) => (0, 0, String::new()),
            };
            println!(
                "PROBE7231B step={} retired={retired} live={live} arena={arena}",
                step + 1
            );
        }
    }
    walls.sort_unstable();
    println!(
        "PROBE7231B threads={threads} edits={edits} p50={:.2} ms p99={:.2} ms",
        rank(&walls, 50) as f64 / 1.0e6,
        rank(&walls, 99) as f64 / 1.0e6,
    );
}

#[test]
#[ignore = "probe"]
fn probe_7231_resident()
{
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
