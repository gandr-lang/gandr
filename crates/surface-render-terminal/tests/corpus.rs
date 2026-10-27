//! The rendered refusals of the corpus's refusing sources, each pinned as
//! the text a face prints.
//!
//! The cases, in a `cfg(test)` module so the crate's lint wall reads them as
//! test code rather than as shipping code.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use expect_test::expect_file;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Refusals;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::entries;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::render;

/// The corpus directories whose sources state refusals: the pathological
/// twins, and one exemplar per refusal name.
const REFUSING: [&str; 2] = ["pathological", "ledger/diagnostics"];

/// The checkout's root, as the walk reaches it.
///
/// # Specification
/// trivial.
fn repository() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the checkout's root resolves")
}

/// Every `.txt` file under `dir`, in path order.
///
/// # Specification
/// trivial.
fn goldens_under(dir: &Path) -> Vec<PathBuf>
{
    let mut files = Vec::new();
    let mut pending = vec![dir.to_owned()];
    while let Some(next) = pending.pop() {
        let Ok(entries) = std::fs::read_dir(&next)
        else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("a directory entry reads").path();
            if path.is_dir() {
                pending.push(path);
            }
            else if path.extension().is_some_and(|held| held == "txt") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Every refusing source's refusals as `gandr check` prints an unexpected
/// one, by the source's path under `corpus/`: each diagnostic plain at the
/// user's verbosity, in the order the source prints them, a blank line
/// between two. A source that prints nothing has no entry.
///
/// # Specification
/// trivial.
fn rendered(repository: &Path) -> BTreeMap<PathBuf, String>
{
    let corpus = repository.join("corpus");
    let prefix = format!("{}/", repository.display());
    let roots = REFUSING.map(|directory| corpus.join(directory)).to_vec();
    let mut rendered = BTreeMap::new();
    let mut faults = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(roots).visit(
        &Pool::new(Width::PerformanceCores),
        |step| -> ControlFlow<Infallible> {
            match step {
                Step::Source { path, .. } => {
                    let mut text = String::new();
                    for diagnostic in
                        entries(&step, Verb::Check(Goals::Gated)).refusals(Refusals::Every)
                    {
                        if !text.is_empty() {
                            text.push('\n');
                        }
                        text.push_str(
                            render(&diagnostic, RenderStyle::Plain, Verbosity::User).as_ref(),
                        );
                        text.push('\n');
                    }
                    if !text.is_empty() {
                        let relative = path
                            .strip_prefix(&corpus)
                            .expect("a walked source lies under the corpus")
                            .to_path_buf();
                        drop(rendered.insert(relative, text.replace(&prefix, "")));
                    }
                },
                Step::Fault { path, .. } => faults.push(path.to_path_buf()),
            }
            ControlFlow::Continue(())
        },
    );
    assert!(faults.is_empty(), "every refusing source reads: {faults:?}");
    rendered
}

/// Every refusing source's rendered refusals match its golden under
/// `tests/golden/corpus/`, at its path in the corpus, so the text a reader
/// is shown for each refusal name is a reviewed public surface. A golden
/// whose source is gone, or prints nothing, fails the suite;
/// `UPDATE_EXPECT=1` rewrites the goldens and deletes those.
#[test]
fn every_refusing_source_renders_as_its_golden()
{
    let repository = repository();
    let goldens = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden/corpus");
    let update = std::env::var_os("UPDATE_EXPECT").is_some();
    let mut expected: BTreeSet<PathBuf> = BTreeSet::new();
    for (relative, text) in rendered(&repository) {
        let golden = goldens.join(relative).with_extension("txt");
        if update && let Some(parent) = golden.parent() {
            std::fs::create_dir_all(parent).expect("the golden's directory is created");
        }
        expect_file![golden.clone()].assert_eq(&text);
        let _new = expected.insert(golden);
    }
    assert!(
        !expected.is_empty(),
        "the refusing sources print their refusals"
    );
    let orphans: Vec<PathBuf> = goldens_under(&goldens)
        .into_iter()
        .filter(|golden| !expected.contains(golden))
        .collect();
    if update {
        for orphan in &orphans {
            std::fs::remove_file(orphan).expect("an orphaned golden is removed");
        }
        return;
    }
    assert!(
        orphans.is_empty(),
        "goldens with no refusing source, to delete or rewrite with `UPDATE_EXPECT=1`: \
         {orphans:?}"
    );
}
