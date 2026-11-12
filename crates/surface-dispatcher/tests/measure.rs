//! Each declaration a settled source writes, measured in its component's
//! kernel artifact and in its admission's tally.

use alloc::collections::BTreeMap;
use core::convert::Infallible;
use core::ops::ControlFlow;
use core::time::Duration;
use std::path::PathBuf;

use gandr_core_fork::Dependence;
use gandr_kernel_term::ArtifactImage;
use gandr_kernel_term::ByteCount;
use gandr_kernel_term::ExpandedWork;
use gandr_kernel_term::TableEntryCount;
use gandr_kernel_term::decode_measured;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::measure;
use gandr_surface_dispatcher::measured;
use gandr_surface_dispatcher::schedule;
use quenchant_shape::shape::Maybe;

/// The sizes of every declaration a component's artifact holds, by the last
/// segment of its structured name. A later declaration of a name replaces an
/// earlier one, so a source's own declaration replaces any its closure holds.
///
/// # Specification
/// trivial.
fn sizes_by_name(
    image: ArtifactImage<'_>
) -> BTreeMap<String, (ByteCount, TableEntryCount, ExpandedWork)>
{
    let (artifact, measures) = decode_measured(image).expect("the admitted artifact decodes");
    let mut sizes = BTreeMap::new();
    for ((declaration, span), measure) in artifact
        .declarations()
        .iter()
        .zip(artifact.segments().declaration_segments())
        .zip(&measures)
    {
        if let Some(last) = declaration.declaration().name().segments().last() {
            let _replaced = sizes.insert(
                last.as_ref().to_owned(),
                (
                    ByteCount::from(usize::from(span.end).saturating_sub(usize::from(span.start))),
                    measure.entries(),
                    measure.expanded_work(),
                ),
            );
        }
    }
    sizes
}

/// Each source of `std.math` measures the declarations it writes, in the
/// order it writes them, and none of the closure it imports. Each row reads
/// the sizes of the artifact's declaration of that name, the census the
/// kernel's check of it charged and the time its admission took. Some row
/// stands on an earlier admission's kept outcomes. A walk not asked to
/// measure records no positions, and says so rather than measuring nothing.
#[test]
fn a_source_measures_the_declarations_it_writes_and_none_it_imports()
{
    let math = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../library/std/src/math");
    let mut written = BTreeMap::new();
    let mut kept = 0_u64;
    let ControlFlow::Continue(_) = Walk::new(vec![math.clone()]).measuring().visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path, ref composed, ..
            } = step
            else {
                panic!("each std.math source is read: {step:?}");
            };
            let Composed::Settled {
                kernel: Maybe::Present(ref kernel),
                ..
            } = *composed
            else {
                panic!("{} is judged and admitted", path.display());
            };
            let Ok(Maybe::Present(rows)) = measure(composed)
            else {
                panic!("{} is measured", path.display());
            };
            let sizes = sizes_by_name(kernel.as_image());
            for row in &rows {
                assert_eq!(
                    sizes.get(row.name().as_ref()),
                    Some(&(row.bytes(), row.shared(), row.unshared())),
                    "{}'s row for {} reads that declaration's segment",
                    path.display(),
                    row.name()
                );
                assert!(
                    u64::try_from(usize::from(row.shared()))
                        .is_ok_and(|shared| shared <= u64::from(row.unshared())),
                    "a segment adds no more entries than its roots' trees hold"
                );
                let Maybe::Present(census) = row.census()
                else {
                    panic!(
                        "{}'s {} is checked, no cache recalling it: {:?}",
                        path.display(),
                        row.name(),
                        row.census()
                    );
                };
                assert!(
                    u64::from(census.expansions())
                        .saturating_add(u64::from(census.recalls()))
                        .saturating_add(u64::from(census.kept()))
                        > 0,
                    "{}'s check of {} charges at least its declared type's formation",
                    path.display(),
                    row.name()
                );
                kept = kept.saturating_add(u64::from(census.kept()));
                assert!(
                    matches!(row.took(), Maybe::Present(_)),
                    "{}'s admission of {} is timed: {:?}",
                    path.display(),
                    row.name(),
                    row.took()
                );
            }
            let names: Vec<String> = rows.iter().map(|row| row.name().to_string()).collect();
            let _replaced = written.insert(
                path.file_name()
                    .map(|name| name.to_string_lossy().into_owned())
                    .unwrap_or_default(),
                names,
            );
            ControlFlow::Continue(())
        },
    );
    assert_eq!(
        written.get("cylinder.gandr").map(Vec::as_slice),
        Some(
            [
                "cylinderComposite2".to_owned(),
                "cylinderStack2".to_owned(),
                "coneComposite2".to_owned(),
                "chainComposite".to_owned(),
                "cylinderFill2".to_owned(),
                "cylinderFillAt2".to_owned(),
                "cylinderFillOver2".to_owned(),
                "liftHorizontal".to_owned(),
                "cylinderFill3".to_owned(),
                "cylinderCompositeCells2".to_owned(),
                "cylinderStackCells2".to_owned(),
                "coneCompositeCells2".to_owned(),
                "interchangeRight".to_owned(),
                "interchangeLeft".to_owned(),
                "cylinderSuspended3".to_owned(),
                "coneOpposite2".to_owned(),
                "coneSuspended3".to_owned()
            ]
            .as_slice()
        ),
        "std.math.cylinder measures the composites it writes, none of std.math.path's"
    );
    assert!(
        kept > 0,
        "a declaration of std.math stands on the outcomes an earlier admission kept"
    );
    let mut unasked = 0_usize;
    let ControlFlow::Continue(_) = Walk::new(vec![math]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path, ref composed, ..
            } = step
            else {
                panic!("each std.math source is read: {step:?}");
            };
            assert!(
                matches!(
                    measure(composed),
                    Ok(Maybe::Absent(measured::Absent::Unpositioned))
                ),
                "{} recorded no positions unasked",
                path.display()
            );
            unasked = unasked.saturating_add(1);
            ControlFlow::Continue(())
        },
    );
    assert_eq!(
        unasked,
        written.len(),
        "the unasked walk reaches every source the measuring one did"
    );
}

/// The checks of a source whose definitions read each other in a chain, with
/// one beside the chain: each job waits on exactly the jobs that its
/// definition names. The chain of the critical path is a path of
/// dependences, and the critical path covers the costs of the written chain.
/// The schedule names each job of its chain by the artifact's name.
#[test]
fn a_component_s_schedule_waits_on_the_references_of_each_job()
{
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "tests/measure/fixtures/a-component-s-schedule-waits-on-the-references-of-each-job.gandr",
    );
    let mut scheduled = 0_usize;
    let ControlFlow::Continue(_) = Walk::new(vec![source]).measuring().visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source { ref composed, .. } = step
            else {
                panic!("the source is read: {step:?}");
            };
            let Composed::Settled {
                ref report,
                positions: Maybe::Present(ref positions),
                ..
            } = *composed
            else {
                panic!("the source is judged, admitted and positioned");
            };
            let Ok(Maybe::Present(row)) = schedule(composed)
            else {
                panic!("a measured admission reads its schedule");
            };
            let checks = row.schedule();
            let Ok(Maybe::Present(rows)) = measure(composed)
            else {
                panic!("the source is measured");
            };
            // Each written definition's job, and the time its admission took.
            let job = |name: &str| -> (usize, Duration) {
                let declaration = report
                    .declarations()
                    .iter()
                    .find(|declaration| declaration.name().as_ref() == name)
                    .unwrap_or_else(|| panic!("the source writes {name}"));
                let Maybe::Present(placed) = positions.placed(declaration.constant())
                else {
                    panic!("{name} crosses into the kernel");
                };
                let at = checks
                    .jobs()
                    .binary_search(&placed.position())
                    .unwrap_or_else(|_| panic!("{name} is a job"));
                let Some(Maybe::Present(took)) = rows
                    .iter()
                    .find(|row| row.name().as_ref() == name)
                    .map(gandr_surface_dispatcher::Measure::took)
                else {
                    panic!("{name}'s admission is timed");
                };
                (at, took.wall())
            };
            let [first, second, third, beside] = ["first", "second", "third", "beside"].map(job);
            let written = [first.0, second.0, third.0, beside.0];
            let among: Vec<(usize, usize)> = checks
                .dependences()
                .edges()
                .iter()
                .map(|edge| (edge.before, edge.after))
                .filter(|&(before, after)| written.contains(&before) && written.contains(&after))
                .collect();
            assert_eq!(
                among,
                [(first.0, second.0), (second.0, third.0)],
                "second waits on first and third on second; beside waits on none of them"
            );
            let bound = checks.bound();
            for pair in bound.chain().windows(2) {
                let &[before, after] = pair
                else {
                    unreachable!("a window of two holds two items");
                };
                // `Dependences` keeps its edges sorted, so one search finds each.
                assert!(
                    checks
                        .dependences()
                        .edges()
                        .binary_search(&Dependence {
                            before: usize::from(before),
                            after: usize::from(after)
                        })
                        .is_ok(),
                    "the chain of the critical path follows the dependences: {pair:?}"
                );
            }
            assert!(
                bound.critical() >= first.1.saturating_add(second.1).saturating_add(third.1),
                "the critical path covers the written chain"
            );
            assert!(
                bound.critical() <= bound.folded() && bound.folded() <= bound.serial(),
                "no schedule passes the serial cost, and the fold waits at least for the chain"
            );
            assert!(
                checks.untimed().is_empty(),
                "a source with no mutual block times each job: {:?}",
                checks.untimed()
            );
            let on_chain: Vec<_> = bound
                .chain()
                .iter()
                .filter_map(|&item| checks.jobs().get(usize::from(item)).copied())
                .collect();
            assert_eq!(
                row.chain()
                    .iter()
                    .map(|&(position, _)| position)
                    .collect::<Vec<_>>(),
                on_chain,
                "the schedule names each job of its chain, in order"
            );
            for (written, at) in [
                ("first", first.0),
                ("second", second.0),
                ("third", third.0),
                ("beside", beside.0),
            ] {
                if let Some(&(_, ref name)) = row
                    .chain()
                    .iter()
                    .find(|&&(position, _)| checks.jobs().get(at) == Some(&position))
                {
                    assert!(
                        name.rsplit('.').next() == Some(written),
                        "the chain names {written} by the artifact's name: {name}"
                    );
                }
            }
            scheduled = scheduled.saturating_add(1);
            ControlFlow::Continue(())
        },
    );
    assert_eq!(scheduled, 1, "the walk reads the one source");
}
