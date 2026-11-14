//! The test fixtures that the crate's tests and the run stage's tests share,
//! and the items of the crate that its `tests` target reads beside its
//! public ones.
//!
//! The crate's lib tests compile this module under `cfg(test)`. A test target
//! of another crate, and the crate's own `tests` target, read it through the
//! `fixture` feature. A test that composes a fixture names the engine
//! that runs its declarations. A test that composes, walks or judges a source
//! stands in the `tests` target, beside the run stage's engine, and reads a
//! crate item through this module.

#![expect(
    clippy::expect_used,
    clippy::missing_panics_doc,
    clippy::panic,
    reason = "a fixture refuses loudly a source or a tree the test did not mean, and its specification states each panic"
)]

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::HostGrant;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::bridge;
use gandr_core_term::CoreArena;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::SettleReport;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

pub use crate::component::Member;
use crate::compose::Composed;
pub use crate::compose::Keeping;
use crate::compose::LoweringCount;
use crate::compose::Reuse;
pub use crate::compose::inferred_runs;
pub use crate::compose::judge_component;
use crate::compose::judge_lowering;
pub use crate::compose::located;
use crate::compose::lower_unit_source;
pub use crate::compose::readmitted;
pub use crate::compose::unstatable;
pub use crate::compose::unused_binders;
use crate::engine::Engine;
use crate::entry::exercised::Exercised;
pub use crate::entry::obstruction;
use crate::entry::report::RunReport;
pub use crate::manifold::Translation;
use crate::program::Program;
use crate::root::SourceRoot;
use crate::walk::Standing;

/// The lines a source writes to import the module of every host interface
/// (#4523), after its own text.
pub const HOSTING: &str = include_str!("lib/unformatted/hosting.gandr");

/// A readmission that resumes nothing and records nothing.
pub const WHOLE: Reuse<'static> = Reuse::Leading(
    bridge::LeadingCount::NONE,
    Maybe::Absent(bridge::crossed::Absent::Unasked),
);

/// A unit of one source, starting at the text's first byte.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn alone() -> Unit
{
    Unit::new(vec![UnitSource::new(ByteOffset::from(0_usize), Vec::new())])
        .expect("one source makes a unit")
}

/// A source laid after `std.list`.
///
/// The driver lays a source after the module it imports in the same way: the
/// module's text first, then the source, whose path imports each resolve to it
/// (#4520). The module declares nothing, so it stands in for the host
/// interfaces' modules as well (#4523).
pub struct Listed
{
    /// The unit's text.
    pub text: alloc::string::String,
    /// Where each source starts and what the source's imports resolve to.
    pub unit: Unit,
    /// Where the source's own text starts in `text`.
    pub base: ByteOffset,
}

impl Listed
{
    /// `source` laid after the standard library's `std.list`.
    ///
    /// # Specification
    /// - requires: each line of the source opening with `import ` is a path
    ///   import of a module that declares nothing it reads by name.
    /// - ensures: the text ends with `source`, which starts at `base`.
    /// - provides: a source naming `List` or a host interface composed where it
    ///   resolves.
    /// - fails: never.
    /// - panics: if the standard library is not checked out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the type table of a laid source answers for a binder
    ///   of the source's own text, at the source's own offsets.
    /// - witness: `typed::tests::an_unread_binder_of_a_list_a_model_or_a_bind_answers_2181`
    #[spec(ensures: |ref ret| ret.text.ends_with(<&str>::from(source)) && ret.text.len() == usize::from(ret.base).saturating_add(<&str>::from(source).len()))]
    #[inline]
    #[must_use]
    pub fn new(source: SourceText<'_>) -> Self
    {
        let module = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../library/std/src/list.gandr"),
        )
        .expect("the standard library is checked out");
        let written: &str = source.into();
        let imports = written
            .lines()
            .filter(|line| line.starts_with("import "))
            .count();
        let base = ByteOffset::from(module.len());
        let unit = Unit::new(alloc::vec![
            UnitSource::new(ByteOffset::from(0_usize), alloc::vec::Vec::new()),
            UnitSource::new(
                base,
                alloc::vec![ImportTarget::Source(SourceIndex::from(0_usize)); imports]
            ),
        ])
        .expect("the source imports the module before it");
        Self {
            text: alloc::format!("{module}{written}"),
            unit,
            base,
        }
    }

    /// `source`, then [`HOSTING`], laid as [`Listed::new`] lays a source.
    ///
    /// # Specification
    /// - requires: as [`Listed::new`].
    /// - ensures: the text ends with [`HOSTING`], and `source` starts at
    ///   `base`.
    /// - provides: a source naming host interfaces composed where they resolve.
    /// - fails: never.
    /// - panics: as [`Listed::new`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a writer of a laid source that imports every host
    ///   interface schedules as its own declarations say.
    /// - witness: `schedule::tests::a_writer_answering_a_kept_value_stays_fused_2954`
    #[spec(ensures: |ref ret| ret.text.ends_with(HOSTING))]
    #[inline]
    #[must_use]
    pub fn hosted<Source>(source: Source) -> Self
    where
        Source: core::fmt::Display,
    {
        let written = alloc::format!("{source}{HOSTING}");
        Self::new(SourceText::from(written.as_str()))
    }

    /// The laid source composed as [`crate::compose()`] composes one source
    /// alone, under `root`, its declarations run by the engine `E`.
    ///
    /// # Specification
    /// - requires: the unit lowers and judges without a fault.
    /// - ensures: the composition of the source at `base`.
    /// - provides: the listed counterpart of [`crate::compose()`].
    /// - fails: never.
    /// - panics: on a composition fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an effectful declaration of a laid source composes
    ///   and settles on the checker's side.
    /// - witness: `tests::compose::an_effectful_declaration_stays_on_the_checkers_side`
    #[spec(requires: !self.text.is_empty())]
    #[inline]
    #[must_use]
    pub fn composed<E>(
        &self,
        root: CorpusRoot,
    ) -> Composed<'_>
    where
        E: Engine,
    {
        let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
        let text = SourceText::from(self.text.as_str());
        lower_unit_source(&grammar, text, &self.unit, &mut LoweringCount::default())
            .and_then(|lowering| {
                judge_lowering::<E>(root, (lowering, text), &HostGrant::UNBOUNDED, self.base)
            })
            .unwrap_or_else(|fault| panic!("the listed source composes: {fault}"))
    }
}

/// The program of `module`, as the composition builds it from `verdicts`
/// over `core` (`Program::new`).
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn program<'source>(
    core: &CoreArena,
    module: &LoweredModule<'source>,
    verdicts: &ModuleReport,
) -> Program<'source>
{
    Program::new(core, module, verdicts)
}

/// Count `composed` into `report` as one source read under `root`, standing
/// as `standing` (`RunReport::read`).
///
/// # Specification
/// trivial.
#[inline]
pub fn read(
    report: &mut RunReport,
    root: SourceRoot,
    composed: &Composed<'_>,
    standing: Standing,
)
{
    report.read(root, composed, standing);
}

/// Count one faulted path into `report` (`RunReport::faulted`).
///
/// # Specification
/// trivial.
#[inline]
pub fn fault(report: &mut RunReport)
{
    report.faulted();
}

/// The rows the settled declarations of `report` exercise, read beside the
/// lowered `module` over `arena` (`Exercised::of`).
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn exercised(
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    report: &SettleReport<'_>,
) -> Exercised
{
    Exercised::of(arena, module, report)
}

/// How [`damage`] changes a chunk's record on disk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Damage
{
    /// Cut the record's segment one byte short of the record's end.
    Truncate,
    /// Flip the low bit of the record's last byte.
    Flip,
}

/// Damage the latest record of the chunk that `pointer` names in the value
/// plane of the store at `store`.
///
/// A record is a header of 64 bytes, its magic `gsg1`, its length as four
/// little-endian bytes and its digest first, then the object's bytes. The
/// segments are read in the order of their names, and a later record of one
/// digest replaces an earlier one, as the store reads them.
///
/// # Specification
/// - requires: the store at `store` holds a record of the pointer's chunk.
/// - ensures: the latest such record is cut short or holds one changed byte.
/// - fails: never.
/// - panics: if no segment holds the chunk, or a segment cannot be read or
///   written.
/// - executable: none — the outcome is the file system's.
///
/// # Adequacy
/// - hypothesis: L3 — a store refuses a damaged chunk, and a later commit
///   writes it afresh.
/// - witness: `receipts::tests::a_damaged_receipt_is_passed_over_until_it_is_kept_again`
#[inline]
pub fn damage(
    store: &Path,
    pointer: gandr_storage_values::ContentPtr,
    damage: Damage,
)
{
    use std::os::unix::fs::FileExt as _;

    let digest = pointer.digest();
    let mut segments: Vec<PathBuf> = std::fs::read_dir(store.join("chunks"))
        .expect("the value plane lists")
        .map(|entry| entry.expect("an entry reads").path())
        .collect();
    segments.sort();
    let mut latest = None;
    for segment in segments {
        let bytes = std::fs::read(&segment).expect("a segment reads");
        let mut rest = bytes.as_slice();
        let mut at = 0_u64;
        while let Some((magic, after)) = rest.split_first_chunk::<4>()
            && magic == b"gsg1"
            && let Some((length, after)) = after.split_first_chunk::<4>()
            && let Some((named, after)) = after.split_first_chunk::<32>()
            && let Some((_place, after)) = after.split_first_chunk::<24>()
            && let Ok(body) = usize::try_from(u32::from_le_bytes(*length))
            && let Some(next) = after.get(body ..)
        {
            let end = at
                .saturating_add(64_u64)
                .saturating_add(u64::from(u32::from_le_bytes(*length)));
            if named.as_slice() == digest.as_ref() {
                latest = Some((segment.clone(), end));
            }
            at = end;
            rest = next;
        }
    }
    let (segment, end) = latest.expect("a segment holds the chunk");
    let last = end.checked_sub(1_u64).expect("a record has bytes");
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&segment)
        .expect("the segment opens");
    match damage {
        Damage::Truncate => file.set_len(last).expect("the segment is cut"),
        Damage::Flip => {
            let mut byte = [0_u8; 1];
            file.read_exact_at(&mut byte, last)
                .expect("the last byte reads");
            let [ref mut changed] = byte;
            *changed ^= 0x01_u8;
            file.write_all_at(&byte, last)
                .expect("the last byte is changed");
        },
    }
}

/// A fresh scratch directory, removed when dropped. The field is the
/// directory, which a test joins its paths to.
#[repr(transparent)]
pub struct Scratch(pub PathBuf);

impl Scratch
{
    /// An empty directory named for `test` and this process.
    ///
    /// # Specification
    /// - requires: the derived temporary path is exclusively owned by this
    ///   fixture, may be replaced and has a writable parent.
    /// - ensures: returns an empty readable directory at that path.
    /// - fails: never.
    /// - panics: if a stale directory cannot be removed or a new one created.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — isolated trees accept the fixture's nested files, and
    ///   exact walk rows observe their contents. These witnesses use fresh
    ///   temporary namespaces, not hostile permissions or interference.
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `tests::walk::a_tree_is_read_when_visited`
    #[spec(ensures: |ref ret|
        std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()))]
    #[inline]
    #[must_use]
    pub fn new(test: &Path) -> Self
    {
        let root = std::env::temp_dir().join(alloc::format!(
            "gandr-dispatcher-{}-{}",
            test.display(),
            std::process::id()
        ));
        if root.exists() {
            std::fs::remove_dir_all(&root).expect("a stale scratch directory is removed");
        }
        std::fs::create_dir_all(&root).expect("the scratch directory is created");
        Self(root)
    }

    /// The directory.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> &Path
    {
        &self.0
    }

    /// Write `text` at `relative`, creating its directories.
    ///
    /// # Specification
    /// - requires: `relative` names a writable file below the owned fixture
    ///   using a nonempty relative sequence of normal path components.
    /// - ensures: creates the required parent directories and writes `text`.
    /// - fails: never.
    /// - panics: if a parent is absent from the path or filesystem creation or
    ///   writing fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested source files have their complete bytes and
    ///   resulting walk outcomes observed. This separates missing parents and
    ///   wrong contents for the fixture paths, not arbitrary path shapes or
    ///   external filesystem mutation.
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `tests::walk::a_tree_is_read_when_visited`
    /// - witness: `tests::walk::an_explicit_link_uses_its_target_root_and_keeps_its_path`
    #[spec(requires: relative.is_relative() && relative.file_name().is_some()
        && relative.components().all(|component|
            matches!(component, std::path::Component::Normal(_))))]
    #[inline]
    pub fn file(
        &self,
        relative: &Path,
        text: SourceText<'_>,
    )
    {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().expect("a file has a parent"))
            .expect("the directories are created");
        std::fs::write(path, text.as_ref()).expect("the file is written");
    }
}

impl Drop for Scratch
{
    /// Remove the directory and everything under it.
    ///
    /// # Specification
    /// - requires: the fixture exclusively owns its removable directory.
    /// - ensures: the fixture directory is absent.
    /// - fails: never.
    /// - panics: if removal fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a populated tree's path is retained across drop and
    ///   observed absent afterward. This detects omitted cleanup on normal
    ///   exit, not unwinding or external permission changes.
    /// - witness: `tests::walk::a_tree_is_read_when_visited`
    #[spec(ensures: self.0.try_exists().is_ok_and(|exists| !exists))]
    #[inline]
    fn drop(&mut self)
    {
        let removed = std::fs::remove_dir_all(&self.0);
        assert!(removed.is_ok(), "the scratch directory is removed");
    }
}
