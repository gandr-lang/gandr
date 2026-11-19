//! The locality of a checkpoint: an item's checkpoint is a function of its own
//! source and of the sources that source reaches. The checkpoint set of an
//! import closure then holds, for each item of a source the closure reaches,
//! the checkpoint that a fresh check of that source's own closure gives. So
//! the set restricts by keys alone to the set of each closure inside it.

use alloc::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::CheckBudget;
use gandr_core_incremental::Bundle;
use gandr_core_incremental::ContentKey;
use gandr_core_incremental::ItemCheckpoint;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::Program;
use gandr_core_incremental::SourceKeys;
use gandr_core_incremental::SourceRun;
use gandr_core_incremental::check_program;
use gandr_core_incremental::content_key;
use gandr_core_incremental::resume_from;
use gandr_core_incremental::unheld;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Unshadowed;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::item_program;
use gandr_surface_dispatcher::item_sources;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The import closure of `source`, laid out as `gandr check` lays it, the
/// item program its lowering gives and the program's sources: the paths of
/// the closure's sources, the prelude first and `source` last.
///
/// # Specification
/// trivial.
fn closure(
    grammar: &Pbg,
    source: &Path,
) -> Option<(Vec<PathBuf>, Program, Vec<SourceRun>)>
{
    let text = std::fs::read_to_string(source).ok()?;
    let laid = lay_out_shadowed(
        grammar,
        source,
        classify(source),
        SourceText::from(text.as_str()),
        &Unshadowed,
    );
    let lowering = lower_unit_source(
        grammar,
        SourceText::from(laid.text.as_str()),
        &laid.unit,
        &mut LoweringCount::default(),
    )
    .ok()?;
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        return None;
    };
    let sources = item_sources(&module);
    let program = item_program(&module, arena).ok()?;
    Some((laid.paths, program, sources))
}

/// One item of a sub-closure whose checkpoint differs from its fresh check's.
struct Differs
{
    /// The closure's root.
    closure: PathBuf,
    /// The sub-closure's root.
    sub: PathBuf,
    /// The item's ordinal in the sub-closure.
    ordinal: usize,
    /// How it differs.
    how: How,
}

impl core::fmt::Display for Differs
{
    /// How the item differs, at its ordinal in the sub-closure under the
    /// closure.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{}: item {} of {} under {}",
            self.how,
            self.ordinal,
            self.sub.display(),
            self.closure.display()
        )
    }
}

/// How a checkpoint of a sub-closure differs from its fresh check's.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum How
{
    /// The closure's set holds no checkpoint at the item's content key.
    Unkeyed,
    /// The closure's set holds checkpoints at the key, none of them the fresh
    /// one.
    Unequal,
    /// The walk of the closure's set onto the sub-closure gives the item
    /// another checkpoint than the fresh check gives.
    Walked,
    /// The bundle of the closure's set restricts to another set than the
    /// fresh check gives, first apart at the item.
    Restricted,
    /// The bundle of the closure's set holds no run under a key of the
    /// sub-closure, and each source of the sub-closure has a key.
    Unheld,
}

impl core::fmt::Display for How
{
    /// The word that names how the item differs.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Unkeyed => "unkeyed",
            Self::Unequal => "unequal",
            Self::Walked => "walked",
            Self::Restricted => "restricted",
            Self::Unheld => "unheld",
        })
    }
}

/// The checkpoints of `program`'s checked set by content key: an item whose
/// content is opaque has no key and is left out.
///
/// # Specification
/// trivial.
fn keyed(
    program: &Program,
    checkpoints: &[ItemCheckpoint],
) -> BTreeMap<ContentKey, Vec<ItemCheckpoint>>
{
    let mut keyed: BTreeMap<ContentKey, Vec<ItemCheckpoint>> = BTreeMap::new();
    for (ordinal, checkpoint) in checkpoints.iter().enumerate() {
        if let Maybe::Present(key) = content_key(program, ItemOrdinal::from(ordinal)) {
            keyed.entry(key).or_default().push(checkpoint.clone());
        }
    }
    keyed
}

/// The sweep of the locality: the closures of the corpus that reach another
/// source of it, under every profile as `gandr-workflow-sweep` draws them.
mod sweeps
{
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Portion;
    use gandr_workflow_sweep::Rotation;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;

    use super::*;

    /// The sample: sixty-four closures, ranked by their BLAKE3 digest under
    /// this name, at least one of each corpus class, and, in the companion,
    /// every source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). A candidate is a corpus source that writes a
    /// path import. The nightly profile checks the night's slice of the
    /// candidates. The `sweeps` profile checks each source under `corpus/`
    /// that writes a path import, a wider set than the candidates.
    const SAMPLE: Sample = Sample {
        name: SampleName("a_sub_closure_keeps_the_checkpoints_of_its_fresh_check_6522"),
        size: SampleSize(64),
    };

    /// The nights the nightly profile takes to check every candidate: a
    /// seventh a night, the count the nightly's sweeps share (#3013). Each
    /// source under `corpus/` that writes a path import, 794 pairs of a
    /// closure and a source it reaches, took 21.5 s in one local run of the
    /// test profile.
    const NIGHTS: Nights = Nights(7);

    /// Each source under `corpus/` that writes a path import, in path order:
    /// the root of an import closure that reaches another source of the
    /// corpus.
    ///
    /// # Specification
    /// trivial.
    fn importers() -> Vec<PathBuf>
    {
        let mut sources = Vec::new();
        let mut pending = vec![
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .canonicalize()
                .expect("the tree resolves")
                .join("corpus"),
        ];
        while let Some(directory) = pending.pop() {
            for entry in std::fs::read_dir(&directory).expect("the directory reads") {
                let path = entry.expect("the entry reads").path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
                    && std::fs::read_to_string(&path)
                        .expect("the source reads")
                        .lines()
                        .any(|line| line.starts_with("import \""))
                {
                    sources.push(path);
                }
            }
        }
        sources.sort();
        sources
    }

    /// #6522: every corpus closure that reaches another source of the
    /// corpus, checked whole, and each source it reaches between the prelude
    /// and its root, checked fresh on its own closure. Each item of the
    /// sub-closure whose content has a key finds the fresh check's checkpoint
    /// at that key in the closure's set. The walk of the closure's set onto
    /// the sub-closure gives the fresh check's set, so the closure's set
    /// restricts as the sub-closure's own set does. An item whose content is
    /// opaque has no key, so the walk alone reads its checkpoint. A number of
    /// a checkpoint that counts over the whole closure — a hole's form, a
    /// name's occurrence, the locus of the program — or an answer that the
    /// whole closure gives in place of the sub-closure's changes a key or a
    /// checkpoint. #6512: the bundle of the closure's set restricts by the
    /// sub-closure's source keys to the fresh check's set, unless a source of
    /// the sub-closure has no key; a source key that the bundle lacks, or a
    /// restriction apart from the fresh set, fails.
    #[test]
    fn a_sub_closure_keeps_the_checkpoints_of_its_fresh_check_6522()
    {
        keeps_fresh(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn a_sub_closure_keeps_the_checkpoints_of_its_fresh_check_6522_changed()
    {
        keeps_fresh(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Each closure `sweep` visits keeps, for each source it reaches, the
    /// checkpoints of that source's fresh check.
    ///
    /// # Specification
    /// trivial.
    fn keeps_fresh(sweep: &Sweep)
    {
        let roots = match (sweep.portion(), sweep.coverage(), sweep.rotation()) {
            (Portion::Fixed, Coverage::Full, Rotation::Whole) => importers(),
            (Portion::Fixed, Coverage::Full, Rotation::Night(_))
            | (Portion::Fixed, Coverage::Sampled, _)
            | (Portion::Changed, ..) => {
                let candidates: Vec<_> = gandr_workflow_sweep::corpus::sources()
                    .expect("the corpus reads")
                    .into_iter()
                    .filter(|source| {
                        std::fs::read_to_string(&source.path)
                            .expect("the source reads")
                            .lines()
                            .any(|line| line.starts_with("import \""))
                    })
                    .collect();
                eprintln!("{}", sweep.rotation());
                let visited = sweep.visit_rotating(SAMPLE, NIGHTS, &candidates);
                // A night's slice of the candidates can hold fewer than a
                // sample, so only a sampled run asserts its sample.
                assert!(
                    sweep.coverage() == Coverage::Full || visited.len() >= sweep.drawn(SAMPLE).0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                visited.into_iter().map(|source| source.path).collect()
            },
        };
        let grammar = built_in().expect("the built-in grammar builds");
        let mut pairs = 0_usize;
        let (mut restricts, mut unkeyed) = (0_usize, 0_usize);
        let (mut items, mut keyless) = (0_usize, 0_usize);
        let mut differs = Vec::new();
        for root in roots {
            let Some((paths, mut whole_program, whole_sources)) = closure(&grammar, &root)
            else {
                continue;
            };
            let Ok(whole) = check_program(&mut whole_program, CheckBudget::DEFAULT)
            else {
                continue;
            };
            let by_key = keyed(&whole_program, whole.checkpoints().items());
            let bundle = Bundle::of(whole.checkpoints(), &whole_sources)
                .expect("the sources lay the set out");
            let reached = paths.len().saturating_sub(2);
            for sub in paths.iter().skip(1).take(reached) {
                let (Some((_, mut fresh_program, fresh_sources)), Some((_, mut walked_program, _))) =
                    (closure(&grammar, sub), closure(&grammar, sub))
                else {
                    continue;
                };
                let keys = SourceKeys::of(&fresh_program, &fresh_sources)
                    .expect("the sources lay the program out");
                let Ok(fresh) = check_program(&mut fresh_program, CheckBudget::DEFAULT)
                else {
                    continue;
                };
                let Ok(walked) = resume_from(whole.checkpoints(), &mut walked_program)
                else {
                    continue;
                };
                pairs = pairs.saturating_add(1);
                let differ = |ordinal: usize, how: How| Differs {
                    closure: root.clone(),
                    sub: sub.clone(),
                    ordinal,
                    how,
                };
                items = items.saturating_add(fresh.checkpoints().items().len());
                for (run, key) in fresh_sources.iter().zip(keys.keys()) {
                    if let Maybe::Absent(_) = *key {
                        keyless = keyless.saturating_add(usize::from(run.items()));
                    }
                }
                match bundle.restrict(&keys) {
                    Maybe::Present(ref restricted) if restricted == fresh.checkpoints() => {
                        restricts = restricts.saturating_add(1);
                    },
                    Maybe::Present(restricted) => {
                        let apart = restricted
                            .items()
                            .iter()
                            .zip(fresh.checkpoints().items())
                            .position(|(restricted, fresh)| restricted != fresh)
                            .unwrap_or_else(|| restricted.items().len());
                        differs.push(differ(apart, How::Restricted));
                    },
                    Maybe::Absent(unheld::Absent::Unkeyed) => unkeyed = unkeyed.saturating_add(1),
                    Maybe::Absent(unheld::Absent::Unheld) => differs.push(differ(0, How::Unheld)),
                }
                for (ordinal, checkpoint) in fresh.checkpoints().items().iter().enumerate() {
                    if let Maybe::Present(key) =
                        content_key(&fresh_program, ItemOrdinal::from(ordinal))
                    {
                        match by_key.get(&key) {
                            None => differs.push(differ(ordinal, How::Unkeyed)),
                            Some(held) if !held.contains(checkpoint) => {
                                differs.push(differ(ordinal, How::Unequal));
                            },
                            Some(_) => {},
                        }
                    }
                }
                for (ordinal, (walked_item, fresh_item)) in walked
                    .checkpoints()
                    .items()
                    .iter()
                    .zip(fresh.checkpoints().items())
                    .enumerate()
                {
                    if walked_item != fresh_item {
                        differs.push(differ(ordinal, How::Walked));
                    }
                }
            }
        }
        eprintln!(
            "checked {pairs} pairs of a closure and a source it reaches: {restricts} restrict by \
             key, {unkeyed} hold a source with no key, and {keyless} of their {items} items sit in \
             a source with no key"
        );
        assert!(
            pairs > 0 || sweep.portion() == Portion::Changed,
            "the corpus holds a closure that reaches another source"
        );
        let mut counts: BTreeMap<How, usize> = BTreeMap::new();
        for differ in &differs {
            let count = counts.entry(differ.how).or_default();
            *count = count.saturating_add(1);
        }
        assert!(
            differs.is_empty(),
            "over {pairs} pairs, {}; the first:\n{}",
            counts
                .iter()
                .map(|(how, count)| format!("{how} {count}"))
                .collect::<Vec<_>>()
                .join(", "),
            differs
                .iter()
                .take(8)
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}
