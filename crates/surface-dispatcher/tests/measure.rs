//! Each declaration a settled source writes, measured in its component's
//! kernel artifact and in its admission's tally.

use alloc::collections::BTreeMap;
use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::PathBuf;

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

/// Each source of `library/math` measures the declarations it writes, in the
/// order it writes them, and none of the closure it imports. Each row reads
/// the sizes of the artifact's declaration of that name, the census the
/// kernel's check of it charged and the time its admission took. Some row
/// stands on an earlier admission's kept outcomes. A walk not asked to
/// measure records no positions, and says so rather than measuring nothing.
#[test]
fn a_source_measures_the_declarations_it_writes_and_none_it_imports()
{
    let math = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../library/math");
    let mut written = BTreeMap::new();
    let mut kept = 0_u64;
    let ControlFlow::Continue(_) = Walk::new(vec![math.clone()]).measuring().visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path, ref composed, ..
            } = step
            else {
                panic!("each math source is read: {step:?}");
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
                "liftRight".to_owned(),
                "liftLeft".to_owned(),
                "liftHorizontal".to_owned(),
                "cylinderFill3".to_owned()
            ]
            .as_slice()
        ),
        "math.cylinder measures the composites it writes, none of math.path's"
    );
    assert!(
        kept > 0,
        "a declaration of math stands on the outcomes an earlier admission kept"
    );
    let mut unasked = 0_usize;
    let ControlFlow::Continue(_) = Walk::new(vec![math]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path, ref composed, ..
            } = step
            else {
                panic!("each math source is read: {step:?}");
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
