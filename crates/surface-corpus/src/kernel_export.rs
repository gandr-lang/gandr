//! The kernel export over the whole corpus: every source of both roots
//! exported, committed as artifact records and read back through the kernel's
//! decoder, and every declaration classified by what became of it at the
//! kernel boundary.
//!
//! The sweep lists `strict/` and `corpus/` itself — `.gandr` files, links not
//! followed, as the dispatcher's walk lists them — and runs the composition a
//! driver runs: parse, lower, check, readmit, export. Nothing here pins a
//! count: each root is asserted to export a declaration, so a source added to
//! either moves a count and reddens nothing.
//!
//! # The kernel export suite
//!
//! `kernel_export` takes each readable source through parse, lower, check,
//! readmission and export. Each sweep runs as eight tests, `_in_shard_0` to
//! `_in_shard_7`, each over every eighth source of each root.
//! `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
//! checks repeat-sweep byte and identity determinism, decoder/re-encoder
//! agreement, record-plane readback and admission from each root.
//! `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
//! checks that withheld dependencies did not cross, the manifest contains one
//! record per crossed declaration beside its header, and the decoded
//! declarations are exactly the admitted names in order. These are L3 witnesses
//! over the current corpus; repeating the same pipeline is not an independent
//! semantic oracle.
//!
//! `kernel_export::kernel_generative_distinctness::the_generative_distinctness_golden`
//! pins what generativity leaves in an artifact: the classic functor pair
//! (`corpus/model/modules/functor-pair.gandr`) exports the argument's atom
//! and one atom per application, the header's minted-atom table names the
//! three apart, and each application's members are typed at its own atom by a
//! node the other's do not share.
//! `kernel_export::kernel_generative_distinctness::an_artifact_whose_applications_share_an_atom_is_refused`
//! rewrites that table so the second application claims the first's atom, and
//! the kernel's decoder refuses it at the table by name: two instances sharing
//! an atom is a refusal at admission, not a convention of the producer.
//!
//! `kernel_export::kernel_ride_readmission::a_ride_dialogue_reading_the_wrong_unfolding_is_refused_by_name`
//! readmits `corpus/model/higher-cells/ua-by-hand.gandr`, whose `rides`
//! relates a ride along the named flow `opposite_dir_by_hand` to its image by
//! the dialogue the checker recorded, then tampers that dialogue so it reads
//! the flow's unfolding on the wrong side: the kernel refuses `rides` at that
//! decision, naming the endpoint and the replay refusal, rather than finding
//! the unfolding itself.
//!
//! `kernel_export::kernel_transport_readmission::a_returned_endpoint_read_as_fibre_evidence_is_refused_by_name`
//! readmits `corpus/model/identity/transport-path.gandr`, whose `moved_end`
//! stands a reflexive transport at a path-type motive as an endpoint of a
//! path between paths, then forges a twin relating a transported unit to
//! itself at that path type: the kernel reads the returned endpoint by the
//! type it returns, as the checker does when it refuses `unit_end`, and
//! refuses the twin as a value-type mismatch naming the path type and the
//! unit.
//!
//! `kernel_export::kernel_here_congruence_readmission::reflexivities_related_through_the_wrong_side_are_refused_by_name`
//! readmits `corpus/model/identity/here-congruence.gandr`, whose
//! `here_two_up` relates `here(two)` to `here(here(2))` by the dialogue that
//! decomposes the two reflexivities to their points and unfolds `two`, then
//! tampers that dialogue so it reads the unfolding on the other point: the
//! kernel refuses `here_two_up` at that decision, naming the endpoint and the
//! replay refusal.
//!
//! `kernel_export::kernel_discard_readmission::an_unread_call_readmits_and_a_discard_on_the_other_side_is_refused_by_name`
//! readmits `corpus/model/control/divergence.gandr`, whose `unreadApplied`
//! relates a function that calls `g` and never reads the result to `f` by the
//! dialogue that drops the call, then tampers that dialogue so the drop names
//! the other side: the kernel refuses `unreadApplied` at that decision, naming
//! the endpoint and the replay refusal.
//!
//! `kernel_export::kernel_presented_readmission::a_circle_read_without_or_against_its_rules_is_refused_by_name`
//! readmits `corpus/model/identity/loop-words.gandr`, whose `cancelled_word`
//! relates `Loop(Unloop(Loop(Nil)))` to `Loop(Nil)` by reflexivity alone: the
//! kernel reads both endpoints by their normal forms under the words' rules. A
//! twin whose `Words` carries no rules is refused at `cancelled_word`, naming
//! the endpoint the point does not reach; a twin whose `Words` carries a rule
//! that grows its word is refused at `Words`, naming the rule and its fault.
//!
//! `kernel_export::kernel_presented_readmission::a_section_at_a_variable_readmits_and_a_tampered_twin_is_refused_by_name`
//! readmits the round trips at a variable at both strata:
//! `corpus/model/identity/loop-space.gandr`'s `sectWords`, a fold into
//! `Path(Words, spinWords(windWords(c)), c)`, and the identity base's `sect`,
//! which `corpus/model/identity/circle.gandr` imports, a fold over the words
//! into `Path(Path(Circle, Base, Base), spin(wind(p)), p)`, each with respect
//! obligations that are cong chains the kernel reads as their paths, then the
//! retraction and the equivalence that holds them (`retrWords` and
//! `wordsWinding`; `retr` and `winding`). A twin whose section carries the
//! loop's path along the inverse is refused at the section, naming the
//! computation type its loop arm does not answer.
//!
//! `kernel_export::kernel_open_fold_readmission::a_step_case_read_through_a_swapped_fold_is_refused_by_name`
//! readmits `corpus/model/identity/open-fold.gandr`, whose `wind_unfolded`
//! relates `windWords(Loop(x))` to `S(windWords(x))` at a variable: the kernel
//! reads the `Loop` arm's bind over the stuck `windWords(x)` itself. A twin
//! whose fold swaps its two loop arms still respects the words' rules and
//! readmits, and, replayed up to the fold and then the step case alone, is
//! refused at `wind_unfolded`, naming the endpoint the point no longer
//! reaches.
//!
//! `kernel_export::kernel_presented_readmission::a_loop_readmits_as_its_words_and_dropped_cancellations_are_refused_by_name`
//! readmits `corpus/model/identity/circle.gandr`, whose `loop : Base <-> Base`
//! crosses as one type of words over the circle's point and whose `cancelled`
//! relates `then(loop, back(loop))` to `here(Base)` by reflexivity alone: the
//! kernel re-mints the words from their cell and reads the path type at the
//! point as them. A twin whose words keep their cell but drop the cancellations
//! is refused at the words, naming the fault.
//!
//! `kernel_export::kernel_presented_readmission::an_absurd_case_readmits_by_apartness_and_forged_twins_are_refused_by_name`
//! readmits `corpus/model/data/empty.gandr`, whose `not_zero` eliminates a
//! path between `S(Z)` and `Z` by a case of no branch: the kernel decides the
//! endpoints apart itself, from the integers' rules. It readmits
//! `corpus/model/identity/circle-apart.gandr` the same way, the loop apart
//! from the empty word at the circle's words. A twin stating the path between
//! `S(P(Z))` and `Z` is refused at `not_zero`, the endpoints named as
//! agreeing; a twin presenting the integers by two rules that rewrite one
//! redex apart is refused there too, naming the critical pair that does not
//! join.
//!
//! `kernel_export::kernel_effect_tree_readmission::a_program_over_its_row_readmits_and_one_performing_outside_it_is_refused_by_name`
//! readmits `corpus/model/effects/tree-rows.gandr`, where effects are data:
//! a program is a tree over its row, a sum of operation types, and each
//! handler a fold. A twin whose `quiet`, a program over state alone,
//! performs `failing`'s `Raise(4)` is refused at `quiet` as a value-type
//! mismatch: the kernel re-derives the row a program claims.
//!
//! The suite derives its expectations from admission and storage semantics
//! rather than checked-in sizes, identities, class thresholds or corpus
//! cardinalities. Exact kernel format goldens belong to `gandr-kernel-term`;
//! this crate checks their composition with real surface sources. The
//! alternative is a generated snapshot for each source, which would also freeze
//! incidental counts. A snapshot becomes appropriate when it can detect a
//! required invariant that admission, roundtrip and repeat-sweep checks cannot
//! distinguish.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use std::fs;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::NameSegment;
use gandr_kernel_term::StructuredName;
use gandr_storage_artifact::ArtifactManifest;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::build;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::TreeParams;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use crate::fixture::declarations;
use crate::refusal::Refusal;
use crate::refusal::RefusalName;

/// The corpus root a source was listed under.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Identifies the strict or fixture tree from which the sweep
///   obtained a source.
/// - panics: none.
/// - executable: none — The enum has no path or filesystem observation;
///   `sources` and `corpus` supply those relationships.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Root
{
    /// `strict/`.
    Strict,
    /// `corpus/`, the pending set among it.
    Fixture,
}

/// What became of one declaration at the kernel boundary.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Distinguishes definitions and assumptions that enter the artifact
///   from marked, withheld, static, unfinished, session, located, world,
///   unrepresentable and never-offered declarations.
/// - panics: none.
/// - executable: none — The enum holds no checker/readmission pair or artifact;
///   `class_of`, `export` and the partition witness establish its
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Class
{
    /// The checker accepted it whole and the kernel admitted it as a
    /// definition.
    Defined,
    /// The checker owed its body and the kernel admitted its signature as an
    /// axiom.
    Assumed,
    /// The checker formed its native signature and the kernel admitted it as
    /// a nominal declaration.
    Data,
    /// The checker refused it, under this name, and it crossed as its mark
    /// alone.
    Marked(RefusalName),
    /// The checker accepted it, and it names a declaration that did not cross.
    Withheld,
    /// The checker accepted it as a type operator, which stays on the
    /// checker's side for the instances that name it.
    Static,
    /// The checker accepted it with a hole or the unknown type, which the
    /// kernel has no image of: an unfinished program crosses nothing.
    Unfinished,
    /// The checker suspended it on a hole its module owes, which nothing
    /// crosses for until a fill resumes it.
    Suspended,
    /// The checker accepted it holding a session, which the kernel has no
    /// former for: it stays on the checker's side.
    Session,
    /// The checker accepted it, and it holds this former, which the pure
    /// kernel has no rule for: an effectful declaration — a capability, its
    /// exercise, its scope — stays on the checker's side.
    Unrepresentable(UnadmittedFormer),
    /// The checker accepted it at a world, holding a handle or a migration,
    /// which the kernel has no former for: it stays on the checker's side.
    Located,
    /// A world declaration, which names a place and lowers to no term: it
    /// stays on the checker's side for the declarations that name it.
    World,
    /// The lowering refused it, under this name, and nothing was offered.
    NeverOffered(RefusalName),
}

/// One source the lowering read, exported.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Associates a source path and root with declaration classes,
///   withheld dependencies, admitted names and their canonical artifact.
/// - panics: none.
/// - executable: none — The record has no original source, module or judgement
///   sequence; `export` establishes its structural invariants and the partition
///   witness compares its admitted names to the artifact.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
struct Exported
{
    /// Where the source sits.
    path: PathBuf,
    /// The root it was listed under.
    root: Root,
    /// Each declaration's position and class, in admission order.
    classes: Vec<(ConstantIndex, Class)>,
    /// Each withheld declaration's position beside the position it names.
    withheld: Vec<(ConstantIndex, ConstantIndex)>,
    /// The structured name of each native operation the source uses; each one
    /// a crossing declaration reads crosses as an audited assumption just
    /// before the first such declaration.
    natives: BTreeSet<StructuredName>,
    /// The structured name of each declaration that crossed, in admission
    /// order.
    crossed_names: Vec<StructuredName>,
    /// The kernel artifact of what crossed.
    artifact: EncodedArtifact,
}

/// What one listed source came to.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Distinguishes a source exported after lowering from a source
///   refused as a whole before any declaration was offered.
/// - panics: none.
/// - executable: none — The enum carries no original lowering result; `export`
///   selects the case while the corpus consumers validate successful exports.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
enum Swept
{
    /// The lowering read it, and it was exported.
    Exported(Exported),
    /// The lowering refused it as a whole, so it offered nothing.
    RefusedWhole,
}

/// Every `.gandr` source under `root`, sorted, symbolic links not followed.
///
/// # Specification
/// - requires: the committed corpus roots remain readable and unchanged during
///   the sweep.
/// - ensures: returns the `.gandr` paths under the selected root, uniquely in
///   lexical order, without following symbolic links.
/// - panics: when a corpus directory, entry or file type cannot be read.
///
/// # Adequacy
/// - hypothesis: L3 — the checked-in strict and fixture trees feed the export
///   and record-plane witnesses. The predicate observes root membership,
///   extension, uniqueness and ordering without a second filesystem walk. The
///   witnesses cover the current corpus; they do not model concurrent
///   filesystem mutation.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
#[spec(
    ensures: |ret| {
    let directory = match root {
        Root::Strict => concat!(env!("CARGO_MANIFEST_DIR"), "/strict"),
        Root::Fixture => concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus"),
    };
    ret
        .iter()
        .all(|path| {
            path.starts_with(directory)
                && path.extension().is_some_and(|extension| extension == "gandr")
        })
        && ret.iter().zip(ret.iter().skip(1_usize)).all(|(first, second)| first < second)
},
)]
fn sources(root: Root) -> Vec<PathBuf>
{
    let directory = match root {
        Root::Strict => concat!(env!("CARGO_MANIFEST_DIR"), "/strict"),
        Root::Fixture => concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus"),
    };
    let mut pending = vec![PathBuf::from(directory)];
    let mut found = Vec::new();
    while let Some(directory) = pending.pop() {
        let entries = fs::read_dir(&directory).unwrap_or_else(|error| {
            panic!(
                "{}: the corpus directory lists: {error}",
                directory.display()
            )
        });
        for entry in entries {
            let entry = entry.expect("a corpus entry reads");
            let kind = entry.file_type().expect("a corpus entry has a type");
            let path = entry.path();
            if kind.is_dir() {
                pending.push(path);
            }
            else if !kind.is_symlink()
                && path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
            {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// What became of the declaration whose verdict is `verdict` and whose
/// readmission is `outcome`, which must agree.
///
/// # Specification
/// - requires: the checker verdict and kernel readmission agree: accepted
///   definitions or static operators, owed assumptions, matching refusal marks,
///   suspended declarations crossing as nothing, accepted/owed declarations
///   withheld by a dependency, accepted/owed declarations holding a hole or the
///   unknown type, accepted declarations holding a session, or accepted/owed
///   declarations holding a former the pure kernel has no rule for.
/// - ensures: returns exactly the corresponding boundary class, retaining the
///   checker refusal’s canonical name for a mark.
/// - panics: when the fixture’s verdict and readmission disagree.
///
/// # Adequacy
/// - hypothesis: L3 — the current corpus supplies readmitted definitions,
///   assumptions, refusal marks, static declarations, withheld dependencies,
///   holed declarations and suspended ones. Exact partition-to-artifact
///   membership distinguishes admitting excluded declarations or losing
///   admitted names; the predicate additionally states pair compatibility and
///   exact class selection.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
#[spec(
    requires: match (verdict, outcome) {
    (
        Verdict::Checked { .. } | Verdict::Synthesised { .. },
        &(bridge::Outcome::Defined { .. }
        | bridge::Outcome::Static
        | bridge::Outcome::Refused(
            bridge::Refusal::Withheld { .. }
            | bridge::Refusal::Hole { .. }
            | bridge::Refusal::Unknown { .. }
            | bridge::Refusal::Session { .. }
            | bridge::Refusal::Located { .. }
            | bridge::Refusal::OutOfFragment { .. }
        )),
    )
    | (
        Verdict::Owed(_),
        &(bridge::Outcome::Assumed { .. }
        | bridge::Outcome::Refused(
            bridge::Refusal::Withheld { .. }
            | bridge::Refusal::Hole { .. }
            | bridge::Refusal::Unknown { .. }
            | bridge::Refusal::Located { .. }
            | bridge::Refusal::OutOfFragment { .. }
        )),
    )
    | (Verdict::Data, &(bridge::Outcome::Data { .. } | bridge::Outcome::Static))
    | (Verdict::Suspended(_), &bridge::Outcome::Suspended) => true,
    (Verdict::Refused(refusal), &bridge::Outcome::Marked(mark)) => refusal == mark,
    _ => false,
},
    ensures: |ret| match (verdict, outcome, ret) {
    (_, &bridge::Outcome::Defined { .. }, Class::Defined)
    | (Verdict::Checked { .. } | Verdict::Synthesised { .. }, &bridge::Outcome::Static, Class::Static)
    | (_, &bridge::Outcome::Assumed { .. }, Class::Assumed)
    | (_, &bridge::Outcome::Data { .. }, Class::Data)
    | (
        _,
        &bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }),
        Class::Withheld,
    )
    | (
        _,
        &bridge::Outcome::Refused(bridge::Refusal::Hole { .. } | bridge::Refusal::Unknown { .. }),
        Class::Unfinished,
    )
    | (_, &bridge::Outcome::Refused(bridge::Refusal::Session { .. }), Class::Session)
    | (_, &bridge::Outcome::Refused(bridge::Refusal::Located { .. }), Class::Located)
    | (Verdict::Data, &bridge::Outcome::Static, Class::World)
    | (Verdict::Suspended(_), &bridge::Outcome::Suspended, Class::Suspended) => true,
    (
        _,
        &bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. }),
        Class::Unrepresentable(found),
    ) => former == found,
    (Verdict::Refused(refusal), &bridge::Outcome::Marked(mark), Class::Marked(name)) => {
        refusal == mark && name == Refusal::Checking(refusal).name()
    }
    _ => false,
},
)]
fn class_of(
    path: &Path,
    verdict: Verdict,
    outcome: &bridge::Outcome,
) -> Class
{
    match (verdict, outcome) {
        (
            Verdict::Checked { .. } | Verdict::Synthesised { .. },
            &bridge::Outcome::Defined { .. },
        ) => Class::Defined,
        (Verdict::Checked { .. } | Verdict::Synthesised { .. }, &bridge::Outcome::Static) => {
            Class::Static
        },
        (Verdict::Owed(_), &bridge::Outcome::Assumed { .. }) => Class::Assumed,
        (Verdict::Data, &bridge::Outcome::Data { .. }) => Class::Data,
        (Verdict::Data, &bridge::Outcome::Static) => Class::World,
        (Verdict::Suspended(_), &bridge::Outcome::Suspended) => Class::Suspended,
        (Verdict::Refused(refusal), &bridge::Outcome::Marked(mark)) if refusal == mark => {
            Class::Marked(Refusal::Checking(refusal).name())
        },
        (
            Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_),
            &bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }),
        ) => Class::Withheld,
        (
            Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_),
            &bridge::Outcome::Refused(
                bridge::Refusal::Hole { .. } | bridge::Refusal::Unknown { .. },
            ),
        ) => Class::Unfinished,
        (
            Verdict::Checked { .. } | Verdict::Synthesised { .. },
            &bridge::Outcome::Refused(bridge::Refusal::Session { .. }),
        ) => Class::Session,
        (
            Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_),
            &bridge::Outcome::Refused(bridge::Refusal::Located { .. }),
        ) => Class::Located,
        (
            Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_),
            &bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. }),
        ) => Class::Unrepresentable(former),
        (verdict, outcome) => panic!(
            "{}: the verdict {verdict:?} and the kernel's outcome {outcome:?} disagree",
            path.display()
        ),
    }
}

/// The source at `path` under `root`, parsed, lowered, checked, readmitted and
/// exported — over the siblings it imports, laid out by the dispatcher's
/// `lay_out`, when it imports any.
///
/// # Specification
/// - requires: `path` is a readable UTF-8 corpus source and `pbg` is its
///   grammar; the caller supplies the root it was listed under.
/// - ensures: a whole-source lowering refusal offers nothing. Otherwise
///   preserves the root, declaration admission order — an importer's siblings
///   first — boundary classes, withheld dependencies and exactly the names
///   admitted as definitions or assumptions alongside their artifact.
/// - panics: on unreadable source, parser failure, an engine fault, or
///   inconsistent checker/readmission positions.
///
/// # Adequacy
/// - hypothesis: L3 — every current corpus source that lowers is checked
///   against its decoded and record-backed artifact. Exact names, admission
///   order, record cardinality and withheld targets distinguish
///   inclusion/exclusion mistakes and lost dependencies. Repeat sweeps
///   establish determinism, not an independent semantic oracle; the predicate
///   does not reread source files.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
#[spec(
    ensures: |ret| match ret {
    Swept::RefusedWhole => true,
    Swept::Exported(ref exported) => {
        exported.root == root
            && exported
                .classes
                .iter()
                .zip(exported.classes.iter().skip(1_usize))
                .all(|(first, second)| first.0 < second.0)
            && exported.crossed_names.len()
                == exported
                    .classes
                    .iter()
                    .filter(|&&(_, class)| {
                        matches!(class, Class::Defined | Class::Assumed | Class::Data)
                    })
                    .count()
            && exported
                .withheld
                .iter()
                .all(|&(declaration, named)| {
                    exported
                        .classes
                        .iter()
                        .any(|&(constant, class)| {
                            constant == declaration && class == Class::Withheld
                        })
                        && !exported
                            .classes
                            .iter()
                            .any(|&(constant, class)| {
                                constant == named
                                    && matches!(class, Class::Defined | Class::Assumed | Class::Data)
                            })
                })
            && exported
                .classes
                .iter()
                .filter(|&&(_, class)| class == Class::Withheld)
                .count() == exported.withheld.len()
    }
},
)]
fn export(
    pbg: &Pbg,
    path: PathBuf,
    root: Root,
) -> Swept
{
    let read = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{}: the source reads: {error}", path.display()));
    // A source is exported over the prelude and the siblings it imports, laid
    // out as the walk lays it out, so its artifact holds theirs first.
    let laid = lay_out(pbg, &path, classify(&path), SourceText::from(read.as_str()));
    let (text, unit) = (laid.text, laid.unit);
    let tree = parse(pbg, SourceText::from(text.as_str()))
        .unwrap_or_else(|fault| panic!("{}: the parser commits a tree: {fault}", path.display()))
        .into_tree();
    let mut arena = CoreArena::new();
    let module = match lower_unit(
        pbg,
        &tree,
        &unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    ) {
        Ok(module) => module,
        Err(refusal) => {
            assert_ne!(
                refusal.classify(),
                FailureClass::EngineFault,
                "{}: the lowering faulted: {refusal}",
                path.display()
            );
            return Swept::RefusedWhole;
        },
    };
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations(&module),
    );
    let natives: BTreeSet<StructuredName> = arena
        .native_primitives()
        .map(|primitive| {
            StructuredName::from(
                primitive
                    .name()
                    .as_ref()
                    .split('.')
                    .filter_map(|segment| NameSegment::from_text(segment.into()))
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    let readmission = bridge::readmit(&mut arena, &verdicts);
    let names = module.structured_names();
    let mut judged = verdicts.judged().iter().zip(readmission.readmitted());
    let mut classes = Vec::new();
    let mut withheld = Vec::new();
    let mut crossed_names = Vec::new();
    for lowered in module.declarations() {
        let constant = lowered.constant();
        let class = if let DeclarationOutcome::Refused(refusal) = lowered.outcome() {
            Class::NeverOffered(Refusal::Lowering(refusal).name())
        }
        else {
            let Some((judgement, crossing)) = judged.next()
            else {
                panic!(
                    "{}: the declaration at {} was offered and has no verdict",
                    path.display(),
                    usize::from(constant)
                );
            };
            assert_eq!(
                (judgement.constant(), crossing.constant()),
                (constant, constant),
                "{}: the verdicts and the readmission keep admission order",
                path.display()
            );
            if let bridge::Outcome::Refused(bridge::Refusal::Withheld {
                constant: named, ..
            }) = *crossing.outcome()
            {
                withheld.push((constant, named));
            }
            class_of(&path, judgement.verdict(), crossing.outcome())
        };
        if matches!(class, Class::Defined | Class::Assumed | Class::Data) {
            crossed_names.push(names.get(&constant).cloned().unwrap_or_default());
        }
        classes.push((constant, class));
    }
    assert!(
        judged.next().is_none(),
        "{}: every verdict belongs to a declaration the lowering read",
        path.display()
    );
    let artifact = readmission.export(names);
    Swept::Exported(Exported {
        path,
        root,
        classes,
        withheld,
        natives,
        crossed_names,
        artifact,
    })
}

/// How many tests share each corpus sweep, each taking every eighth source of
/// each root. The export gate sweeps each source twice: four shards took
/// 22.7–24.1 s each on the queue's enforcing runner (`ci:timing`, #2547), and
/// 19–20 s alone on a local machine, where every gate at once pushed all four
/// past the 30 s per-test limit. An eighth stays well inside it under load.
const SHARDS: usize = 8;

/// Which of the `SHARDS` tests of a sweep a corpus source is exported in.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Shard(usize);

/// The sources of both roots in `shard` that the lowering reads, exported, in
/// root and then path order: every `SHARDS`-th source of each root's listing,
/// starting at the shard's own index.
///
/// # Specification
/// - requires: `shard` is below `SHARDS`; both committed corpus trees remain
///   readable and unchanged during the sweep.
/// - ensures: exports every source of `shard` that lowers, omitting
///   whole-source refusals, in strict-root then fixture-root path order without
///   duplicate paths.
/// - panics: on an invalid fixture or failed export precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the checked-in roots are swept twice and each resulting
///   artifact is decoded and read through its records. Root/path order and
///   unique membership are executable invariants; byte identity across sweeps
///   is determinism evidence, while the partition witness compares admitted
///   names to the reconstructed artifact. The `SHARDS` shards together take
///   every source of each root, each in one shard.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_3`
#[spec(
    requires: shard.0 < SHARDS,
    ensures: |ret| {
    ret
        .iter()
        .all(|exported| {
            exported
                .path
                .starts_with(
                    match exported.root {
                        Root::Strict => concat!(env!("CARGO_MANIFEST_DIR"), "/strict"),
                        Root::Fixture => concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus"),
                    },
                )
        })
        && ret
            .iter()
            .zip(ret.iter().skip(1_usize))
            .all(|(first, second)| {
                (first.root, &first.path) < (second.root, &second.path)
            })
},
)]
fn corpus(shard: Shard) -> Vec<Exported>
{
    let pbg = built_in().expect("the built-in grammar builds");
    let mut exported = Vec::new();
    for root in [Root::Strict, Root::Fixture] {
        for path in sources(root).into_iter().skip(shard.0).step_by(SHARDS) {
            if let Swept::Exported(source) = export(&pbg, path, root) {
                exported.push(source);
            }
        }
    }
    exported
}

/// `artifact` committed as records into a fresh block store, beside the
/// manifest naming them.
///
/// # Specification
/// - requires: `artifact` is a valid canonical kernel export whose record tree
///   fits the current profile.
/// - ensures: returns a fresh store containing the artifact’s record tree and
///   the manifest naming its root. Reading the manifest under the current
///   profile reconstructs the same artifact.
/// - panics: if the export cannot be segmented or the records cannot be
///   committed.
///
/// # Adequacy
/// - hypothesis: L3 — every current corpus export is committed, read through
///   the manifest and compared with the kernel-decoded artifact; its manifest
///   count also matches the independently observed admitted declarations. The
///   predicate verifies the returned manifest/store root association without
///   another whole-artifact reconstruction.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
#[spec(
    ensures: |ret| {
    gandr_storage_records::BlockStore::load(&ret.1, ret.0.root_node())
        .is_ok_and(|node| node.identity() == ret.0.root_node())
},
)]
fn commit(artifact: &EncodedArtifact) -> (ArtifactManifest, InMemoryBlockStore)
{
    let records = ArtifactRecordSet::from_artifact(artifact.as_image())
        .expect("an export cuts at its own segments");
    let mut store = InMemoryBlockStore::default();
    let manifest = build(&records, TreeParams::current(), &mut store).expect("the records commit");
    (manifest, store)
}

/// The export gate: every source's artifact is a function of its text, and
/// reads back through the record plane and the decoder as itself.
mod kernel_export_gate
{
    use alloc::collections::BTreeSet;

    use anodized::spec;
    use gandr_kernel_term::decode;
    use gandr_kernel_term::encode;
    use gandr_storage_records::TreeParams;

    use super::Class;
    use super::Root;
    use super::SHARDS;
    use super::Shard;
    use super::commit;
    use super::corpus;
    use super::sources;

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_0()
    {
        gate(Shard(0));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_1()
    {
        gate(Shard(1));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_2()
    {
        gate(Shard(2));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_3()
    {
        gate(Shard(3));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_4()
    {
        gate(Shard(4));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_5()
    {
        gate(Shard(5));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_6()
    {
        gate(Shard(6));
    }

    #[test]
    fn the_kernel_export_exit_gate_holds_in_shard_7()
    {
        gate(Shard(7));
    }

    /// The sources of `shard` exported twice: each artifact is a function of
    /// its text and reads back through the record plane and the decoder as
    /// itself.
    ///
    /// # Specification
    /// - requires: `shard` is below `SHARDS`.
    /// - ensures: both sweeps of `shard` export the same sources to the same
    ///   bytes and identities; each artifact decodes, re-encodes byte for byte
    ///   and reads back through its records; and the sources of `shard` export
    ///   a definition or an assumption from each root that has a source in
    ///   `shard` (the strict root's few sources fill only the first shards).
    /// - panics: when any of those fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `SHARDS` shards together take every source of
    ///   each root, each in one shard; a shard past `SHARDS` would take none.
    /// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_0`
    /// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds_in_shard_7`
    #[spec(requires: shard.0 < SHARDS)]
    fn gate(shard: Shard)
    {
        let first = corpus(shard);
        let second = corpus(shard);
        assert_eq!(
            first.len(),
            second.len(),
            "two sweeps read the same sources"
        );
        let mut exporting = BTreeSet::new();
        for (one, two) in first.iter().zip(&second) {
            let path = one.path.display();
            assert_eq!(
                one.artifact, two.artifact,
                "{path}: the export is a function of the source"
            );
            let (manifest, store) = commit(&one.artifact);
            let (again, _again_store) = commit(&two.artifact);
            assert_eq!(
                manifest.identity(),
                again.identity(),
                "{path}: the identity is a function of the source"
            );
            let decoded = decode(one.artifact.as_image())
                .unwrap_or_else(|refusal| panic!("{path}: the export decodes: {refusal}"));
            assert_eq!(
                one.artifact,
                encode(decoded.arena(), decoded.declarations()),
                "{path}: the decoding re-encodes byte for byte"
            );
            assert_eq!(
                Ok(decoded),
                manifest.read_under(&store, TreeParams::current()),
                "{path}: the records read back through the decoder as the export"
            );
            if one
                .classes
                .iter()
                .any(|&(_, class)| matches!(class, Class::Defined | Class::Assumed))
            {
                exporting.insert(one.root);
            }
        }
        let held: BTreeSet<Root> = [Root::Strict, Root::Fixture]
            .into_iter()
            .filter(|&root| sources(root).len() > shard.0)
            .collect();
        assert_eq!(
            held, exporting,
            "the sources of shard {} export a declaration from each root it holds a source of",
            shard.0
        );
    }
}

/// The partition: every declaration of the corpus classified once by what
/// became of it at the kernel boundary, against the artifact that holds what
/// crossed.
mod kernel_corpus_partition
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_term::StructuredName;
    use gandr_storage_records::RecordCount;
    use gandr_storage_records::TreeParams;

    use super::Class;
    use super::SHARDS;
    use super::Shard;
    use super::commit;
    use super::corpus;

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_0()
    {
        partition(Shard(0));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_1()
    {
        partition(Shard(1));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_2()
    {
        partition(Shard(2));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_3()
    {
        partition(Shard(3));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_4()
    {
        partition(Shard(4));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_5()
    {
        partition(Shard(5));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_6()
    {
        partition(Shard(6));
    }

    #[test]
    fn corpus_partition_matches_the_manifest_in_shard_7()
    {
        partition(Shard(7));
    }

    /// The sources of `shard` exported once, each declaration classified by
    /// what became of it at the kernel boundary and held against the artifact
    /// that holds what crossed.
    ///
    /// # Specification
    /// - requires: `shard` is below `SHARDS`.
    /// - ensures: no withheld declaration names one that crossed; each manifest
    ///   counts its header, every native signature, session assumption, free
    ///   model and declaration that crossed; each session assumption and each
    ///   free model is numbered in admission order; and besides them each
    ///   artifact holds the declarations that crossed, in admission order,
    ///   under their names, and between them only distinct natives the source
    ///   uses.
    /// - panics: when any of those fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `SHARDS` shards together take every source of
    ///   each root, each in one shard; a shard past `SHARDS` would take none.
    /// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
    /// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_7`
    #[spec(requires: shard.0 < SHARDS)]
    fn partition(shard: Shard)
    {
        let mut classes = BTreeMap::new();
        let mut seeded: BTreeSet<StructuredName> = BTreeSet::new();
        for exported in corpus(shard) {
            let path = exported.path.display();
            classes.clear();
            seeded.clear();
            classes.extend(exported.classes.iter().copied());
            for &(declaration, named) in &exported.withheld {
                assert!(
                    !matches!(
                        classes.get(&named),
                        Some(&(Class::Defined | Class::Assumed | Class::Data))
                    ),
                    "{path}: the declaration at {} is withheld for naming {}, which crossed",
                    usize::from(declaration),
                    usize::from(named)
                );
            }
            let (manifest, store) = commit(&exported.artifact);
            let read = manifest
                .read_under(&store, TreeParams::current())
                .unwrap_or_else(|refusal| panic!("{path}: the records read back: {refusal}"));
            // A received value or an offered choice crosses under an
            // assumption the readmission admits ahead of the first declaration
            // that reads it, named `session.receive.<n>` or `session.offer.<n>`
            // with `n` its admission ordinal; every other record is a native
            // or a declaration.
            let session_assumption = |name: &StructuredName| match *name.segments() {
                [ref session, ref action, ref ordinal]
                    if session.as_ref() == "session"
                        && matches!(action.as_ref(), "receive" | "offer") =>
                {
                    ordinal.as_ref().parse::<usize>().ok()
                },
                _ => None,
            };
            // A handled effect crosses through its free model, a data
            // declaration the readmission admits ahead of the first
            // declaration that handles it, named `effect.free.<n>` with `n`
            // its admission ordinal.
            let free_model = |name: &StructuredName| match *name.segments() {
                [ref effect, ref free, ref ordinal]
                    if effect.as_ref() == "effect" && free.as_ref() == "free" =>
                {
                    ordinal.as_ref().parse::<usize>().ok()
                },
                _ => None,
            };
            let (assumed, held): (Vec<&StructuredName>, Vec<&StructuredName>) = read
                .declarations()
                .iter()
                .map(|marked| marked.declaration().name())
                .partition(|&name| session_assumption(name).is_some());
            let (models, held): (Vec<&StructuredName>, Vec<&StructuredName>) = held
                .into_iter()
                .partition(|&name| free_model(name).is_some());
            for (ordinal, &name) in assumed.iter().enumerate() {
                assert_eq!(
                    session_assumption(name),
                    Some(ordinal),
                    "{path}: the session assumptions are numbered in admission order: {assumed:?}"
                );
            }
            for (ordinal, &name) in models.iter().enumerate() {
                assert_eq!(
                    free_model(name),
                    Some(ordinal),
                    "{path}: the free models are numbered in admission order: {models:?}"
                );
            }
            // Every other record is a declaration that crossed, in admission
            // order, or the signature of a native the source uses, seeded
            // just before the first declaration that reads it.
            let mut crossed_names = exported.crossed_names.iter().peekable();
            for &name in &held {
                if crossed_names.next_if(|&crossed| crossed == name).is_some() {
                    continue;
                }
                assert!(
                    exported.natives.contains(name) && seeded.insert(name.clone()),
                    "{path}: besides the session assumptions, the free models and the \
                     declarations that crossed, in admission order under their names, the \
                     artifact holds only distinct natives the source uses: {name:?} in {held:?} \
                     against {:?}",
                    exported.crossed_names,
                );
            }
            assert!(
                crossed_names.next().is_none(),
                "{path}: the artifact holds every declaration that crossed, in admission order: \
                 {:?} against {held:?}",
                exported.crossed_names,
            );
            let crossed = exported
                .classes
                .iter()
                .filter(|&&(_, class)| {
                    matches!(class, Class::Defined | Class::Assumed | Class::Data)
                })
                .count()
                .saturating_add(seeded.len())
                .saturating_add(assumed.len())
                .saturating_add(models.len());
            assert_eq!(
                RecordCount(
                    u64::try_from(crossed.saturating_add(1)).expect("a count fits sixty-four bits")
                ),
                manifest.record_count(),
                "{path}: the manifest counts the header, every native signature, every session \
                 assumption, every free model and every declaration that crossed"
            );
        }
    }
}

/// Generativity at the kernel boundary: the classic functor pair's two
/// applications export an atom each, the header's minted-atom table names both
/// beside the argument's, and an artifact whose table has the two applications
/// share one atom is refused by the decoder.
mod kernel_generative_distinctness
{
    use alloc::format;
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_kernel_term::ArtifactImage;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::DecodeError;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::ReservedSlot;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Exported;
    use super::Root;
    use super::Swept;
    use super::export;

    /// The offset of the header's minted-atom count: past the four-byte magic
    /// and the two-byte version.
    const MINTED_ATOM_TABLE_COUNT_OFFSET: usize = 6;
    /// The offset of the table's entry for the first application's atom, past
    /// the count and the argument's entry, each one byte in the functor pair.
    const FIRST_APPLICATION_ENTRY_OFFSET: usize = 8;
    /// The offset of the table's entry for the second application's atom.
    const SECOND_APPLICATION_ENTRY_OFFSET: usize = 9;

    /// The classic functor pair exported: `Seed` sealed, then `MkCounter`
    /// applied to it twice, as `A` and as `B`.
    ///
    /// # Specification
    /// trivial.
    fn functor_pair() -> Exported
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/modules/functor-pair.gandr"
        ));
        match export(&pbg, path, Root::Fixture) {
            Swept::Exported(exported) => exported,
            Swept::RefusedWhole => panic!("the functor pair lowers"),
        }
    }

    #[test]
    fn the_generative_distinctness_golden()
    {
        let named = |dotted: &str| {
            StructuredName::from(
                dotted
                    .split('.')
                    .filter_map(|segment| NameSegment::from_text(segment.into()))
                    .collect::<Vec<_>>(),
            )
        };
        let exported = functor_pair();
        let decoded =
            decode(exported.artifact.as_image()).expect("the functor pair's export decodes");
        let atoms: Vec<(usize, &StructuredName)> = decoded
            .declarations()
            .iter()
            .enumerate()
            .filter(|&(_, marked)| {
                matches!(
                    *marked.declaration().content(),
                    DeclarationContent::AbstractType { .. }
                )
            })
            .map(|(position, marked)| (position, marked.declaration().name()))
            .collect();
        assert_eq!(
            atoms
                .iter()
                .map(|&(_, name)| name.clone())
                .collect::<Vec<_>>(),
            ["Seed.T", "A.T", "B.T"].map(named),
            "the argument's atom, then one atom per application, in admission order"
        );
        let &[(seed, _), (first, _), (second, _)] = atoms.as_slice()
        else {
            panic!("three atoms");
        };
        let entry = |position: usize| u8::try_from(position).expect("a one-byte position");
        let image = Vec::from(exported.artifact);
        assert_eq!(
            image.get(MINTED_ATOM_TABLE_COUNT_OFFSET ..= SECOND_APPLICATION_ENTRY_OFFSET),
            Some([3_u8, entry(seed), entry(first), entry(second)].as_slice()),
            "the header's table carries each atom once, at its own position"
        );
        let mut seeds = Vec::new();
        for (instance, own, other) in [("A", first, second), ("B", second, first)] {
            let member = named(&format!("{instance}.seed"));
            let typed: Vec<_> = decoded
                .declarations()
                .iter()
                .filter(|marked| *marked.declaration().name() == member)
                .map(|marked| marked.declaration().declared_id())
                .collect();
            let at = |atom: usize| {
                typed.iter().copied().find(|&id| {
                    decoded.arena().value_type(id)
                        == Some(&ValueType::Abstract(ConstantIndex::from(atom)))
                })
            };
            let Some(own) = at(own)
            else {
                panic!("{instance}.seed is typed at its own application's atom");
            };
            assert_eq!(at(other), None, "and never at the other application's");
            seeds.push(own);
        }
        assert!(
            matches!(seeds.as_slice(), [first, second] if first != second),
            "no shared subterm merges the two instances' types: {seeds:?}"
        );
    }

    #[test]
    fn an_artifact_whose_applications_share_an_atom_is_refused()
    {
        let mut image = Vec::from(functor_pair().artifact);
        let first = *image
            .get(FIRST_APPLICATION_ENTRY_OFFSET)
            .expect("the first application's entry");
        *image
            .get_mut(SECOND_APPLICATION_ENTRY_OFFSET)
            .expect("the second application's entry") = first;
        assert_eq!(
            decode(ArtifactImage::from(image.as_slice())).map(|_decoded| ()),
            Err(DecodeError::ReservedSlotOccupied {
                slot: ReservedSlot::MintedAtomTable,
            }),
            "a table on which the second application claims the first's atom is refused by name"
        );
    }
}

/// The ride-in-a-type statement readmits by its recorded dialogue alone: a
/// twin whose dialogue reads the wrong unfolding is refused by name.
mod kernel_ride_readmission
{
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_core::EndpointSide;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::IdentityError;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayDecline;
    use gandr_kernel_core::ReplayRefusal;
    use gandr_kernel_core::TracePosition;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_ride_dialogue_reading_the_wrong_unfolding_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/higher-cells/ua-by-hand.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("ua-by-hand lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("ua-by-hand's export decodes");
        let mut declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("ua-by-hand readmits, `rides` by the dialogue the checker recorded");

        let rides = StructuredName::from(
            ["ByHand", "rides"]
                .into_iter()
                .filter_map(|segment| NameSegment::from_text(segment.into()))
                .collect::<Vec<_>>(),
        );
        let Some(position) = declarations
            .iter()
            .position(|marked| *marked.declaration().name() == rides)
        else {
            panic!("`rides` crossed");
        };
        let Some(statement) = declarations.get_mut(position)
        else {
            panic!("`rides` is a declaration");
        };
        let DeclarationContent::Def { declared, body } = *statement.declaration().content()
        else {
            panic!("`rides` is a definition");
        };
        let Some(Value::Here { point, dialogues }) = arena.value(body).cloned()
        else {
            panic!("`rides` crosses as the kernel's reflexivity");
        };
        // The ride stands on the left endpoint; the first reduction its
        // dialogue names is the named flow's unfolding.
        let mut tampered = (*dialogues).clone();
        let Some(misread) = tampered.left.iter().position(|decision| {
            matches!(
                decision,
                ConversionDecision::ReduceLeft { .. } | ConversionDecision::ReduceRight { .. }
            )
        })
        else {
            panic!("the dialogue unfolds `opposite_dir_by_hand`: {dialogues:?}");
        };
        if let Some(reduction) = tampered.left.get_mut(misread) {
            *reduction = match *reduction {
                ConversionDecision::ReduceLeft { .. } => {
                    ConversionDecision::ReduceRight { redex: () }
                },
                ConversionDecision::ReduceRight { .. }
                | ConversionDecision::ConstShortcut { .. }
                | ConversionDecision::Unfold { .. }
                | ConversionDecision::Postpone { .. }
                | ConversionDecision::Freeze { .. }
                | ConversionDecision::EtaExpand { .. }
                | ConversionDecision::ReturnEta { .. }
                | ConversionDecision::Reassociate { .. }
                | ConversionDecision::Discard { .. }
                | ConversionDecision::Force { .. }
                | ConversionDecision::ComparedShared { .. }
                | ConversionDecision::Decompose
                | ConversionDecision::NegativeSubgoal { .. } => {
                    ConversionDecision::ReduceLeft { redex: () }
                },
            };
        }
        let forged = arena.value_here_relating(point, Arc::new(tampered));
        let content = DeclarationBuilder::new(&mut arena).def(
            statement.declaration().levels().clone(),
            declared,
            forged,
        );
        *statement = MarkedDeclaration::new(
            statement.mark(),
            content.named(statement.declaration().name().clone()),
        );

        let refusal = Environment::replay(arena, &declarations)
            .expect_err("the unfolding read on the wrong side is refused");
        assert_eq!(usize::from(refusal.position()), position);
        assert!(
            matches!(
                *refusal.error(),
                KernelError::Identity(IdentityError::EndpointsDiffer {
                    side: EndpointSide::Left,
                    verdict: KernelVerdict::Declined(ReplayDecline::Refused(
                        ReplayRefusal::Inapplicable { at }
                    )),
                    ..
                }) if at == TracePosition::from(misread)
            ),
            "the kernel names the endpoint and the misread decision: {:?}",
            refusal.error()
        );
    }
}

/// The reflexive transport at a path-type motive readmits; a twin relating a
/// transported unit, the evidence of the fibre of its path type, to itself
/// at that path type is refused by name at the endpoint's type.
mod kernel_transport_readmission
{
    use alloc::vec;
    use std::path::PathBuf;

    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::ValueTypeHead;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_returned_endpoint_read_as_fibre_evidence_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/transport-path.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("transport-path lowers");
        };
        let decoded =
            decode(exported.artifact.as_image()).expect("transport-path's export decodes");
        let mut declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("transport-path readmits, `moved_end` at the path type its transport returns");

        let segment =
            NameSegment::from_text("moved_end".into()).expect("`moved_end` is a name segment");
        let moved_end = StructuredName::from(vec![segment]);
        let Some(position) = declarations
            .iter()
            .position(|marked| *marked.declaration().name() == moved_end)
        else {
            panic!("`moved_end` crossed");
        };
        let Some(statement) = declarations.get_mut(position)
        else {
            panic!("`moved_end` is a declaration");
        };
        let DeclarationContent::Def { declared, .. } = *statement.declaration().content()
        else {
            panic!("`moved_end` is a definition");
        };
        let Some(&ValueType::Path { domain, left, .. }) = arena.value_type(declared)
        else {
            panic!("`moved_end` is declared at a path type");
        };
        let Some(&Value::Returned(moved)) = arena.value(left)
        else {
            panic!("its left endpoint crosses as a returned endpoint");
        };
        let Some(&Computation::PathTransport { path, .. }) = arena.computation(moved)
        else {
            panic!("over the transport it erases");
        };
        // The same path carries the unit at the constant unit motive, and the
        // twin relates that returned unit to itself at the path type: the
        // endpoint returns the fibre's evidence, not a path, which the checker
        // refuses as `unit_end` and a kernel reading it as fibre evidence
        // admitted.
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let carried = arena.computation_path_transport(unit_type, path, unit);
        let carried = arena.value_returned(carried);
        let forged = arena.value_type_path(domain, carried, carried);
        let reflexive = arena.value_here(carried);
        let content = DeclarationBuilder::new(&mut arena).def(
            statement.declaration().levels().clone(),
            forged,
            reflexive,
        );
        *statement = MarkedDeclaration::new(
            statement.mark(),
            content.named(statement.declaration().name().clone()),
        );

        let refusal = Environment::replay(arena, &declarations)
            .expect_err("a returned unit does not stand at a path type");
        assert_eq!(usize::from(refusal.position()), position);
        assert!(
            matches!(
                *refusal.error(),
                KernelError::ValueTypeMismatch(mismatch)
                    if mismatch.expected().head() == ValueTypeHead::Path
                        && mismatch.actual().head() == ValueTypeHead::Product
            ),
            "the kernel names the path type expected and the unit found: {:?}",
            refusal.error()
        );
    }
}

/// Two reflexivities whose points differ by a definition's unfolding readmit
/// by the dialogue that decomposes them to their points; a twin whose
/// dialogue reads the unfolding on the wrong side is refused by name.
mod kernel_here_congruence_readmission
{
    use alloc::sync::Arc;
    use alloc::vec;
    use std::path::PathBuf;

    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_core::EndpointSide;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::IdentityError;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayDecline;
    use gandr_kernel_core::ReplayRefusal;
    use gandr_kernel_core::TracePosition;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn reflexivities_related_through_the_wrong_side_are_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/here-congruence.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("here-congruence lowers");
        };
        let decoded =
            decode(exported.artifact.as_image()).expect("here-congruence's export decodes");
        let mut declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations).expect(
            "here-congruence readmits, `here_two_up` by the points its dialogue decomposes to",
        );

        let segment =
            NameSegment::from_text("here_two_up".into()).expect("`here_two_up` is a name segment");
        let here_two_up = StructuredName::from(vec![segment]);
        let Some(position) = declarations
            .iter()
            .position(|marked| *marked.declaration().name() == here_two_up)
        else {
            panic!("`here_two_up` crossed");
        };
        let Some(statement) = declarations.get_mut(position)
        else {
            panic!("`here_two_up` is a declaration");
        };
        let DeclarationContent::Def { declared, body } = *statement.declaration().content()
        else {
            panic!("`here_two_up` is a definition");
        };
        let Some(Value::Here { point, dialogues }) = arena.value(body).cloned()
        else {
            panic!("`here_two_up` crosses as the kernel's reflexivity");
        };
        // The right endpoint `here(here(2))` meets the point `here(two)`: the
        // dialogue decomposes the two reflexivities and unfolds `two` on the
        // left, which the twin reads on the right instead.
        let mut tampered = (*dialogues).clone();
        let Some(misread) = tampered
            .right
            .iter()
            .position(|decision| matches!(decision, ConversionDecision::ReduceLeft { .. }))
        else {
            panic!("the dialogue unfolds `two` on the left: {dialogues:?}");
        };
        if let Some(reduction) = tampered.right.get_mut(misread) {
            *reduction = ConversionDecision::ReduceRight { redex: () };
        }
        let forged = arena.value_here_relating(point, Arc::new(tampered));
        let content = DeclarationBuilder::new(&mut arena).def(
            statement.declaration().levels().clone(),
            declared,
            forged,
        );
        *statement = MarkedDeclaration::new(
            statement.mark(),
            content.named(statement.declaration().name().clone()),
        );

        let refusal = Environment::replay(arena, &declarations)
            .expect_err("the unfolding read on the wrong side is refused");
        assert_eq!(usize::from(refusal.position()), position);
        assert!(
            matches!(
                *refusal.error(),
                KernelError::Identity(IdentityError::EndpointsDiffer {
                    side: EndpointSide::Right,
                    verdict: KernelVerdict::Declined(ReplayDecline::Refused(
                        ReplayRefusal::Inapplicable { at }
                    )),
                    ..
                }) if at == TracePosition::from(misread)
            ),
            "the kernel names the endpoint and the misread decision: {:?}",
            refusal.error()
        );
    }
}

/// An unread call readmits by the dialogue that discards it and then unfolds
/// a definition, which the kernel's own reading does not do under a binder; a
/// twin whose dialogue discards on the side that holds no call is refused by
/// name.
mod kernel_discard_readmission
{
    use alloc::sync::Arc;
    use alloc::vec;
    use std::path::PathBuf;

    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    use gandr_kernel_core::EndpointSide;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::IdentityError;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayDecline;
    use gandr_kernel_core::ReplayRefusal;
    use gandr_kernel_core::TracePosition;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn an_unread_call_readmits_and_a_discard_on_the_other_side_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/control/divergence.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("divergence lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("divergence's export decodes");
        let mut declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("divergence readmits, `unreadApplied` by the discard its dialogue names");

        let segment = NameSegment::from_text("unreadApplied".into())
            .expect("`unreadApplied` is a name segment");
        let unread_applied = StructuredName::from(vec![segment]);
        let Some(position) = declarations
            .iter()
            .position(|marked| *marked.declaration().name() == unread_applied)
        else {
            panic!("`unreadApplied` crossed");
        };
        let Some(statement) = declarations.get_mut(position)
        else {
            panic!("`unreadApplied` is a declaration");
        };
        let DeclarationContent::Def { declared, body } = *statement.declaration().content()
        else {
            panic!("`unreadApplied` is a definition");
        };
        // `unreadApplied` is a function of four parameters returning the
        // reflexivity: its body thunks four lambdas over a `return`.
        let Some(&Value::Thunk(mut focus)) = arena.value(body)
        else {
            panic!("`unreadApplied` crosses as a thunk");
        };
        let mut binders = 0_usize;
        while let Some(&Computation::Lambda(inner)) = arena.computation(focus) {
            focus = inner;
            binders = binders.saturating_add(1);
        }
        let Some(&Computation::Return(returned)) = arena.computation(focus)
        else {
            panic!("`unreadApplied` returns under its parameters");
        };
        let Some(Value::Here { point, dialogues }) = arena.value(returned).cloned()
        else {
            panic!("`unreadApplied` returns the kernel's reflexivity");
        };
        // The left endpoint calls `g` and drops its value before it calls
        // `apply`: the dialogue relating the point `f` to it discards that
        // call on the endpoint's side, which the twin names on the point's.
        let mut tampered = (*dialogues).clone();
        let Some(misread) = tampered.left.iter().position(|decision| {
            *decision
                == ConversionDecision::Discard {
                    side: ConversionSide::Right,
                }
        })
        else {
            panic!("the dialogue discards the call on the endpoint's side: {dialogues:?}");
        };
        if let Some(discard) = tampered.left.get_mut(misread) {
            *discard = ConversionDecision::Discard {
                side: ConversionSide::Left,
            };
        }
        let forged = arena.value_here_relating(point, Arc::new(tampered));
        let mut rebuilt = arena.computation_return(forged);
        for _ in 0 .. binders {
            rebuilt = arena.computation_lambda(rebuilt);
        }
        let forged = arena.value_thunk(rebuilt);
        let content = DeclarationBuilder::new(&mut arena).def(
            statement.declaration().levels().clone(),
            declared,
            forged,
        );
        *statement = MarkedDeclaration::new(
            statement.mark(),
            content.named(statement.declaration().name().clone()),
        );

        let refusal = Environment::replay(arena, &declarations)
            .expect_err("a discard on the side that holds no call is refused");
        assert_eq!(usize::from(refusal.position()), position);
        assert!(
            matches!(
                *refusal.error(),
                KernelError::Identity(IdentityError::EndpointsDiffer {
                    side: EndpointSide::Left,
                    verdict: KernelVerdict::Declined(ReplayDecline::Refused(
                        ReplayRefusal::Inapplicable { at }
                    )),
                    ..
                }) if at == TracePosition::from(misread)
            ),
            "the kernel names the endpoint and the misread decision: {:?}",
            refusal.error()
        );
    }
}

/// A presented type's cancellation readmits by its normal forms; a circle
/// without its rules, or with a rule that does not present it, is refused by
/// name; a fold over the circle readmits when it respects the rules, and a
/// twin whose arm breaks one is refused by name; a fold that rests on laws
/// readmits on them, and a twin whose laws are forged — each stating the
/// other rule's path — is refused by the first rule; a section at a variable,
/// over the circle's terms or over its words, readmits by its cong chains,
/// and a twin carrying the wrong loop is refused by name; a loop's words
/// readmit as their cell mints them, and a twin without the cancellations is
/// refused by name; a case of no branch over a path readmits when its
/// endpoints are apart, and twins whose endpoints agree or whose rules
/// diverge are refused by name.
mod kernel_presented_readmission
{
    use alloc::vec;
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_kernel_core::EndpointSide;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::IdentityError;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_term::Apartness;
    use gandr_kernel_term::CellFault;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::PresentedRule;
    use gandr_kernel_term::RuleFault;
    use gandr_kernel_term::RuleIndex;
    use gandr_kernel_term::RuleNode;
    use gandr_kernel_term::RuleRefusal;
    use gandr_kernel_term::RuleVariable;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_circle_read_without_or_against_its_rules_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/loop-words.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the circle lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the circle's export decodes");
        let declarations = decoded.declarations().to_vec();
        let arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("the circle readmits, `cancelled_word` by its endpoints' normal forms");
        let position = |name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            let named = StructuredName::from(vec![segment]);
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{name}` crossed"))
        };
        let circle = position("Words");
        let cancelled = position("cancelled_word");
        // The declarations with the circle presented by `presentation`.
        let presenting = |presentation: Presentation| {
            let mut twin = declarations.clone();
            let Some(marked) = twin.get_mut(circle)
            else {
                panic!("the circle is a declaration");
            };
            *marked = MarkedDeclaration::new(
                marked.mark(),
                marked.declaration().clone().presented(presentation),
            );
            twin
        };

        let free = presenting(Presentation::default());
        let refusal = Environment::replay(arena.clone(), &free)
            .expect_err("over a free circle the two words are two terms");
        assert_eq!(usize::from(refusal.position()), cancelled);
        assert!(
            matches!(
                *refusal.error(),
                KernelError::Identity(IdentityError::EndpointsDiffer {
                    side: EndpointSide::Left,
                    ..
                })
            ),
            "the kernel names the endpoint the point does not reach: {:?}",
            refusal.error()
        );

        let x = RuleNode::Variable(RuleVariable::from(0_u32));
        let loop_ = RuleNode::Constructor(ConstructorTag::from(1_usize));
        let growing = Presentation::new(vec![PresentedRule::new(
            [loop_, x].into(),
            [loop_, loop_, x].into(),
        )]);
        let grown = presenting(growing);
        let refusal = Environment::replay(arena, &grown)
            .expect_err("a rule that grows its word does not present the circle");
        assert_eq!(usize::from(refusal.position()), circle);
        assert_eq!(
            *refusal.error(),
            KernelError::RuleNotPresentable(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault: RuleFault::NotDecreasing,
            }),
            "the kernel names the rule and its fault"
        );
    }

    #[test]
    fn a_loop_readmits_as_its_words_and_dropped_cancellations_are_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/circle.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the circle with a loop lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the export decodes");
        let declarations = decoded.declarations().to_vec();
        let arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations).expect(
            "the words readmit as their loop mints them, and `cancelled` by the cancellation",
        );
        let worded: Vec<usize> = declarations
            .iter()
            .enumerate()
            .filter(|&(_, marked)| marked.declaration().presentation().cells().is_some())
            .map(|(position, _)| position)
            .collect();
        let [words] = *worded
        else {
            panic!("one type of words crosses, the loops at the circle's point: {worded:?}");
        };
        let mut dropped = declarations;
        let Some(marked) = dropped.get_mut(words)
        else {
            panic!("the words are a declaration");
        };
        let Some(cells) = marked.declaration().presentation().cells().cloned()
        else {
            panic!("the words carry their cells");
        };
        *marked = MarkedDeclaration::new(
            marked.mark(),
            marked
                .declaration()
                .clone()
                .presented(Presentation::default().carrying(cells)),
        );
        let refusal = Environment::replay(arena, &dropped)
            .expect_err("words without their cancellations are not the words the loop mints");
        assert_eq!(usize::from(refusal.position()), words);
        assert_eq!(
            *refusal.error(),
            KernelError::WordsRefused(CellFault::NotMinted),
            "the kernel names the words and their fault"
        );
    }

    #[test]
    fn an_absurd_case_readmits_by_apartness_and_forged_twins_are_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/data/empty.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the empty type lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("every absurd case readmits: its endpoints are apart");
        let circle = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/circle-apart.gandr"
        ));
        let Swept::Exported(circle) = export(&pbg, circle, Root::Fixture)
        else {
            panic!("the circle lowers");
        };
        let circle = decode(circle.artifact.as_image()).expect("the export decodes");
        Environment::replay(circle.arena().clone(), circle.declarations())
            .expect("the loop is apart from the empty word, its square and its inverse");
        let position = |name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            let named = StructuredName::from(vec![segment]);
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{name}` crossed"))
        };
        let integers = position("Int");
        let not_zero = position("not_zero");

        // The twin states `not_zero` at `Path(Int, S(P(Z)), Z)`: the same
        // case of no branch, its endpoints forged to agree.
        let marked = &declarations[not_zero];
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("`not_zero` is a definition");
        };
        let Some(&ValueType::Thunk(arrow)) = arena.value_type(declared)
        else {
            panic!("`not_zero` is a thunk");
        };
        let Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) =
            arena.comp_type(arrow)
        else {
            panic!("`not_zero` takes the path");
        };
        let dependent = matches!(arena.comp_type(arrow), Some(CompType::Pi { .. }));
        let Some(&ValueType::Path {
            domain: carrier,
            left,
            right,
        }) = arena.value_type(domain)
        else {
            panic!("`not_zero` takes a path");
        };
        let Some(Value::Constructor {
            datatype,
            tag,
            fields,
        }) = arena.value(left).cloned()
        else {
            panic!("`S(Z)` is a constructor");
        };
        let predecessor = arena.value_constructor(datatype, ConstructorTag::from(2_usize), fields);
        let cancelled = arena.value_constructor(datatype, tag, vec![predecessor]);
        let forged = arena.value_type_path(carrier, cancelled, right);
        let forged = if dependent {
            arena.comp_type_pi(forged, codomain)
        }
        else {
            arena.comp_type_arrow(forged, codomain)
        };
        let forged = arena.value_type_thunk(forged);
        let twin_declaration = DeclarationBuilder::new(&mut arena)
            .def(marked.declaration().levels().clone(), forged, body)
            .named(marked.declaration().name().clone());
        let mut twin = declarations.clone();
        twin[not_zero] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena.clone(), &twin)
            .expect_err("`S(P(Z))` is `Z`: no apartness separates them");
        assert_eq!(usize::from(refusal.position()), not_zero);
        assert_eq!(
            *refusal.error(),
            KernelError::NotApart(Apartness::Agree),
            "the kernel names the forged endpoints' reason"
        );

        // The twin presents the integers by two rules rewriting one redex
        // apart: admission takes them, each linear and decreasing, and the
        // apartness rule refuses to read their normal forms as elements.
        let x = RuleNode::Variable(RuleVariable::from(0_u32));
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let divergent = Presentation::new(vec![
            PresentedRule::new([c(1), c(2), x].into(), [x].into()),
            PresentedRule::new([c(1), c(2), x].into(), [c(0)].into()),
        ]);
        let mut twin = declarations.clone();
        let Some(marked) = twin.get_mut(integers)
        else {
            panic!("the integers are a declaration");
        };
        *marked = MarkedDeclaration::new(
            marked.mark(),
            marked.declaration().clone().presented(divergent),
        );
        let refusal = Environment::replay(arena, &twin)
            .expect_err("divergent rules give no normal form to compare");
        assert_eq!(usize::from(refusal.position()), not_zero);
        assert_eq!(
            *refusal.error(),
            KernelError::NotApart(Apartness::Diverges {
                outer: RuleIndex::from(0_usize),
                inner: RuleIndex::from(1_usize),
            }),
            "the kernel joins the critical pairs itself and names the pair that does not join"
        );
    }

    #[test]
    fn a_fold_whose_arm_breaks_a_rule_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/loop-words.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the circle lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the circle's export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("`mirror` readmits: it respects both cancellations");
        let segment = NameSegment::from_text("mirror".into()).expect("a name segment");
        let named = StructuredName::from(vec![segment]);
        let mirror = declarations
            .iter()
            .position(|marked| *marked.declaration().name() == named)
            .expect("`mirror` crossed");
        let marked = &declarations[mirror];
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("`mirror` is a definition");
        };
        let Some(&Value::Thunk(fixpoint)) = arena.value(body)
        else {
            panic!("`mirror` is a thunk");
        };
        let Some(&Computation::Fixpoint {
            body: lambda,
            evidence,
        }) = arena.computation(fixpoint)
        else {
            panic!("`mirror` is a fixpoint");
        };
        let Some(&Computation::Lambda(case)) = arena.computation(lambda)
        else {
            panic!("`mirror` opens with a lambda");
        };
        let Some(Computation::DataCase {
            scrutinee,
            motive,
            branches,
            ..
        }) = arena.computation(case).cloned()
        else {
            panic!("`mirror` cases on its argument");
        };
        // The twin reads `Unloop(x)` with the `Loop(x)` arm: both letters
        // become `Unloop`, so `Loop(Unloop(x))` is sent two letters from `x`.
        let broken = vec![branches[0], branches[1], branches[1]];
        let case = arena.computation_data_case(scrutinee, motive, broken);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, evidence);
        let body = arena.value_thunk(fixpoint);
        let twin_declaration = DeclarationBuilder::new(&mut arena)
            .def(marked.declaration().levels().clone(), declared, body)
            .named(named);
        let mut twin = declarations.clone();
        twin[mirror] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("the broken arm does not respect the circle's rules");
        assert_eq!(usize::from(refusal.position()), mirror);
        assert_eq!(
            *refusal.error(),
            KernelError::RuleNotRespected(RuleIndex::from(0_usize)),
            "the kernel names the rule the twin breaks"
        );
    }

    #[test]
    fn a_fold_resting_on_a_forged_law_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/loop-winding.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the circle lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the circle's export decodes");
        let declarations = decoded.declarations().to_vec();
        let arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("`native_wind` readmits on the native model's two laws");
        let segment = NameSegment::from_text("native_wind".into()).expect("a name segment");
        let named = StructuredName::from(vec![segment]);
        let wind = declarations
            .iter()
            .position(|marked| *marked.declaration().name() == named)
            .expect("`native_wind` crossed");
        let marked = &declarations[wind];
        let &[first, second] = marked.declaration().laws()
        else {
            panic!(
                "`native_wind` rests on one law per rule: {:?}",
                marked.declaration().laws()
            );
        };
        // The twin cites each law for the other's rule: `unturn(turn(n)) = n`
        // where `Loop(Unloop(x))` computes `turn(unturn(f(x)))`.
        let forged = marked.declaration().clone().lawful(vec![second, first]);
        let mut twin = declarations.clone();
        twin[wind] = MarkedDeclaration::new(marked.mark(), forged);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("a law stating another rule's path does not relate this one's sides");
        assert_eq!(usize::from(refusal.position()), wind);
        assert_eq!(
            *refusal.error(),
            KernelError::RuleNotRespected(RuleIndex::from(0_usize)),
            "the kernel names the rule the forged law fails"
        );
    }

    #[test]
    fn forged_operation_rules_are_refused_by_the_kernel_322()
    {
        use gandr_kernel_term::OperationNode;
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/desc/rules-overlap-joinable.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the overlapping naturals lower");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the export decodes");
        let declarations = decoded.declarations().to_vec();
        let arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("`add` readmits: the kernel joins both of its critical pairs");
        let add = declarations
            .iter()
            .position(|marked| marked.declaration().operation_rules().rules().len() == 3)
            .expect("`add` crosses carrying its three rules");
        let marked = &declarations[add];
        let rules = marked.declaration().operation_rules().rules();
        let Some(&OperationNode::Constructor { family, .. }) =
            rules.first().and_then(|zero| zero.left().get(1))
        else {
            panic!("`add(Zero, n)` reads `Zero` first: {rules:?}");
        };
        // The twin rewrites `add(m, Zero)` to `Succ(m)`, as the pathological
        // `rules-diverge` source writes it: at `add(Zero, Zero)` the first rule
        // gives `Zero` and the second `Succ(Zero)`.
        let mut forged = rules.to_vec();
        forged[1] = gandr_kernel_term::OperationRule::new(
            rules[1].left().into(),
            [
                OperationNode::Constructor {
                    family,
                    tag: gandr_kernel_term::ConstructorTag::from(1_usize),
                },
                OperationNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32)),
            ]
            .into(),
        );
        let twin_declaration = marked
            .declaration()
            .clone()
            .ruled(gandr_kernel_term::OperationRules::new(forged));
        let mut twin = declarations.clone();
        twin[add] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("the forged rules rewrite `add(Zero, Zero)` two ways");
        assert_eq!(usize::from(refusal.position()), add);
        assert_eq!(
            *refusal.error(),
            KernelError::OperationRulesRefused(gandr_kernel_term::OperationRuleRefusal {
                rule: RuleIndex::from(1_usize),
                fault: gandr_kernel_term::OperationRuleFault::Diverges(
                    gandr_kernel_term::Overlapped::Operation(RuleIndex::from(0_usize))
                ),
            }),
            "the kernel names the forged rule and the rule it parts from"
        );
    }

    #[test]
    fn rules_the_body_does_not_compute_are_refused_by_the_kernel_322()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/desc/rules-overlap-joinable.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("the overlapping naturals lower");
        };
        let decoded = decode(exported.artifact.as_image()).expect("the export decodes");
        let declarations = decoded.declarations().to_vec();
        let arena = decoded.arena().clone();
        let add = declarations
            .iter()
            .position(|marked| marked.declaration().operation_rules().rules().len() == 3)
            .expect("`add` crosses carrying its three rules");
        let marked = &declarations[add];
        let &[ref zero, _, ref recursion] = marked.declaration().operation_rules().rules()
        else {
            panic!("`add` carries its three rules");
        };
        // Without `add(m, Zero) ==> m` the other two rules still converge, but
        // the body's leaf at `add(Succ(m), Zero)` returns its first input, which
        // the recursion `add(Succ(m), n) ==> Succ(add(m, n))` does not.
        let twin_declaration =
            marked
                .declaration()
                .clone()
                .ruled(gandr_kernel_term::OperationRules::new(vec![
                    zero.clone(),
                    recursion.clone(),
                ]));
        let mut twin = declarations.clone();
        twin[add] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("the body computes a rule the twin dropped");
        assert_eq!(usize::from(refusal.position()), add);
        assert_eq!(
            *refusal.error(),
            KernelError::OperationBodyUnlinked(gandr_kernel_core::OperationBodyFault::Apart(
                RuleIndex::from(1_usize)
            )),
            "the kernel names the rule the leaf is not"
        );
    }

    #[test]
    fn a_section_at_a_variable_readmits_and_a_tampered_twin_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        // The loop space on terms, and the book's circle, whose `sect` (written
        // in the identity base it imports) is the same fold one stratum up,
        // over the words. Each names its section, retraction and winding.
        for (path, [sect, retr, winding]) in [
            (
                concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../../corpus/model/identity/loop-space.gandr"
                ),
                ["sectWords", "retrWords", "wordsWinding"],
            ),
            (
                concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../../corpus/model/identity/circle.gandr"
                ),
                ["sect", "retr", "winding"],
            ),
        ] {
            let Swept::Exported(exported) = export(&pbg, PathBuf::from(path), Root::Fixture)
            else {
                panic!("{path} lowers");
            };
            let decoded = decode(exported.artifact.as_image()).expect("the export decodes");
            let declarations = decoded.declarations().to_vec();
            let mut arena = decoded.arena().clone();
            let position = |name: &str| {
                let segment = NameSegment::from_text(name.into()).expect("a name segment");
                let named = StructuredName::from(vec![segment]);
                declarations
                    .iter()
                    .position(|marked| *marked.declaration().name() == named)
                    .unwrap_or_else(|| panic!("`{name}` crossed from {path}"))
            };
            let (sect, _retr, _winding) = (position(sect), position(retr), position(winding));
            Environment::replay(arena.clone(), &declarations).unwrap_or_else(|refusal| {
                panic!(
                    "the round trips at a variable readmit from {path}, each respect \
                     obligation fusing its cong chain: {refusal:?}"
                )
            });
            let marked = &declarations[sect];
            let DeclarationContent::Def { declared, body } = *marked.declaration().content()
            else {
                panic!("`sect` is a definition");
            };
            let Some(&Value::Thunk(fixpoint)) = arena.value(body)
            else {
                panic!("`sect` is a thunk");
            };
            let Some(&Computation::Fixpoint {
                body: lambda,
                evidence,
            }) = arena.computation(fixpoint)
            else {
                panic!("`sect` is a fixpoint");
            };
            let Some(&Computation::Lambda(case)) = arena.computation(lambda)
            else {
                panic!("`sect` opens with a lambda");
            };
            let Some(Computation::DataCase {
                scrutinee,
                motive,
                branches,
                ..
            }) = arena.computation(case).cloned()
            else {
                panic!("`sect` cases on its argument");
            };
            // The twin carries the loop's path along the inverse: the loop
            // arm then relates `Unloop(spinWords(windWords(x)))` to
            // `Unloop(x)`, or `back(loop) ∷ spin(wind(q))` to `back(loop) ∷ q`,
            // not the motive at the loop.
            let tampered = vec![branches[0], branches[2], branches[2]];
            let case = arena.computation_data_case(scrutinee, motive, tampered);
            let lambda = arena.computation_lambda(case);
            let fixpoint = arena.computation_fixpoint(lambda, evidence);
            let body = arena.value_thunk(fixpoint);
            let named = marked.declaration().name().clone();
            let twin_declaration = DeclarationBuilder::new(&mut arena)
                .def(marked.declaration().levels().clone(), declared, body)
                .named(named);
            let mut twin = declarations.clone();
            twin[sect] = MarkedDeclaration::new(marked.mark(), twin_declaration);
            let refusal = Environment::replay(arena, &twin)
                .expect_err("the tampered arm does not answer the motive at the loop");
            assert_eq!(usize::from(refusal.position()), sect, "{path}");
            assert!(
                matches!(*refusal.error(), KernelError::ComputationTypeMismatch(_)),
                "the kernel refuses the arm at the motive it does not answer in {path}: {:?}",
                refusal.error()
            );
        }
    }
}

/// A step case at a variable readmits by the kernel's own reading of the bind
/// over the stuck call; a twin whose fold swaps its loop arms is refused by
/// name at the step case it no longer meets.
mod kernel_open_fold_readmission
{
    use alloc::vec;
    use std::path::PathBuf;

    use gandr_kernel_core::EndpointSide;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::IdentityError;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_step_case_read_through_a_swapped_fold_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/open-fold.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("open-fold lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("open-fold's export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .expect("open-fold readmits, `wind_unfolded` by the bind its endpoint reads through");
        let position = |name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            let named = StructuredName::from(vec![segment]);
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{name}` crossed"))
        };
        let wind = position("windWords");
        let unfolded = position("wind_unfolded");
        let marked = &declarations[wind];
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("`wind` is a definition");
        };
        let Some(&Value::Thunk(fixpoint)) = arena.value(body)
        else {
            panic!("`wind` is a thunk");
        };
        let Some(&Computation::Fixpoint {
            body: lambda,
            evidence,
        }) = arena.computation(fixpoint)
        else {
            panic!("`wind` is a fixpoint");
        };
        let Some(&Computation::Lambda(case)) = arena.computation(lambda)
        else {
            panic!("`wind` opens with a lambda");
        };
        let Some(Computation::DataCase {
            scrutinee,
            motive,
            branches,
            ..
        }) = arena.computation(case).cloned()
        else {
            panic!("`wind` cases on its argument");
        };
        // The twin's `Loop` arm returns `P(n)` and its `Unloop` arm `S(n)`: it
        // still respects both cancellations, but `windWords(Loop(x))` now
        // reads as `P(windWords(x))`, which `wind_unfolded` does not meet.
        let swapped = vec![branches[0], branches[2], branches[1]];
        let case = arena.computation_data_case(scrutinee, motive, swapped);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, evidence);
        let body = arena.value_thunk(fixpoint);
        let twin_declaration = DeclarationBuilder::new(&mut arena)
            .def(marked.declaration().levels().clone(), declared, body)
            .named(marked.declaration().name().clone());
        // The twin replays the declarations up to the fold, then the step case
        // alone: the loop space's closed runs of the fold that stand between
        // them (`wound_twice` first) would refuse the swap at a closed word,
        // before the reading at a variable is reached.
        let mut twin = declarations[..= wind].to_vec();
        twin[wind] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        twin.push(declarations[unfolded].clone());
        let refusal = Environment::replay(arena, &twin)
            .expect_err("the swapped fold reads `windWords(Loop(x))` as a predecessor");
        assert_eq!(
            usize::from(refusal.position()),
            wind + 1,
            "the step case refuses"
        );
        assert!(
            matches!(
                refusal.error(),
                KernelError::Identity(IdentityError::EndpointsDiffer {
                    side: EndpointSide::Left,
                    ..
                })
            ),
            "the kernel names the endpoint the swapped fold no longer reaches: {refusal:?}"
        );
    }
}

/// A case over the circle readmits by the kernel's own reading of its loop
/// obligation; a twin whose flip drops its loop arm leaves `involutive`
/// owing a loop it no longer respects, and is refused by name there.
mod kernel_loop_elimination_readmission
{
    use alloc::vec;
    use std::path::PathBuf;

    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_term::CellIndex;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_loop_elimination_readmits_and_its_tampered_twin_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/identity/circle-elim.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("circle-elim lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("circle-elim's export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations).unwrap_or_else(|refusal| {
            panic!(
                "circle-elim readmits, each case's loop owed by conversion or by its \
                 loop arm: {refusal:?}"
            )
        });
        let position = |name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            let named = StructuredName::from(vec![segment]);
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{name}` crossed"))
        };
        let flip = position("invLooper");
        let involutive = position("involutive");
        let marked = &declarations[flip];
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("`invLooper` is a definition");
        };
        let Some(&Value::Thunk(lambda)) = arena.value(body)
        else {
            panic!("`invLooper` is a thunk");
        };
        let Some(&Computation::Lambda(case)) = arena.computation(lambda)
        else {
            panic!("`invLooper` opens with a lambda");
        };
        let Some(Computation::DataCase {
            scrutinee,
            motive,
            branches,
            ..
        }) = arena.computation(case).cloned()
        else {
            panic!("`invLooper` cases on its argument");
        };
        assert_eq!(branches.len(), 2, "the point's branch, then the loop arm");
        // The twin keeps the point's branch and drops the loop arm: it still
        // checks, a non-dependent case owing nothing, but now sends the loop to
        // reflexivity, so `invLooper(invLooper(x))` no longer follows `x`
        // round the loop and `involutive`'s answer at `Base` is not carried
        // to itself.
        let collapsed = vec![branches[0]];
        let case = arena.computation_data_case(scrutinee, motive, collapsed);
        let lambda = arena.computation_lambda(case);
        let body = arena.value_thunk(lambda);
        let twin_declaration = DeclarationBuilder::new(&mut arena)
            .def(marked.declaration().levels().clone(), declared, body)
            .named(marked.declaration().name().clone());
        let mut twin = declarations.clone();
        twin[flip] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("the collapsed flip leaves `involutive` short of its loop");
        assert_eq!(usize::from(refusal.position()), involutive);
        assert_eq!(
            *refusal.error(),
            KernelError::LoopNotRespected(CellIndex::from(0_usize)),
            "the kernel names the loop `involutive` no longer respects"
        );
    }
}

/// A presentation's rules are decided at readmission as its value states them:
/// `Unital` readmits, and a twin carrying a second law that rewrites the
/// unit's call apart is refused naming the pair; `Group` readmits from the
/// derived rules and peaks its value carries.
mod kernel_presentation_readmission
{
    use alloc::vec;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::RuleIndex;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::TheoryRuleFault;
    use gandr_kernel_term::TheoryRuleRefusal;
    use gandr_kernel_term::TheoryRules;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    /// The declarations `fixture` exports, and the position of the one named
    /// `name`.
    ///
    /// # Specification
    /// trivial.
    fn exported(
        fixture: &Path,
        name: &StructuredName,
    ) -> (
        gandr_kernel_term::TermArena,
        alloc::vec::Vec<MarkedDeclaration>,
        ConstantIndex,
    )
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus")
            .join(fixture);
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("{} lowers", fixture.display());
        };
        let decoded = decode(exported.artifact.as_image()).expect("the export decodes");
        let declarations = decoded.declarations().to_vec();
        let position = declarations
            .iter()
            .position(|marked| marked.declaration().name() == name)
            .unwrap_or_else(|| panic!("`{name:?}` crossed"));
        (
            decoded.arena().clone(),
            declarations,
            ConstantIndex::from(position),
        )
    }

    /// The one-segment name `text`.
    ///
    /// # Specification
    /// trivial.
    fn named<T>(text: T) -> StructuredName
    where
        T: AsRef<str>,
    {
        let segment = NameSegment::from_text(text.as_ref().into()).expect("a name segment");
        StructuredName::from(vec![segment])
    }

    #[test]
    fn a_presentations_rules_are_decided_at_readmission_1059()
    {
        let (mut arena, declarations, unital) = exported(
            Path::new("model/desc/sealed-lawful-model.gandr"),
            &named("Unital"),
        );
        Environment::replay(arena.clone(), &declarations)
            .unwrap_or_else(|refusal| panic!("`Unital` readmits: {refusal:?}"));
        let marked = &declarations[usize::from(unital)];
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("`Unital` is a definition");
        };
        let Some(Value::Constructor {
            datatype,
            tag,
            fields,
        }) = arena.value(body).cloned()
        else {
            panic!("`Unital` is a presentation");
        };
        let &[sorts, operations, unit_law] = fields.as_slice()
        else {
            panic!("a presentation holds three chains");
        };
        let Some(Value::Constructor {
            tag: rule,
            fields: law,
            ..
        }) = arena.value(unit_law).cloned()
        else {
            panic!("the rule chain opens with `unitL`");
        };
        let &[name, left, right, rest] = law.as_slice()
        else {
            panic!("a rule holds its name, its sides and the rest");
        };
        let Some(Value::Constructor { fields: call, .. }) = arena.value(left).cloned()
        else {
            panic!("`unitL`'s left side is a call");
        };
        let Some(Value::Constructor {
            fields: arguments, ..
        }) = arena.value(call[1]).cloned()
        else {
            panic!("the call's arguments");
        };
        // The twin's second law rewrites `unitL`'s own call, `mul(e(), x)`, to
        // its first argument, `e()`, where `unitL` gives `x`.
        let unit = arguments[0];
        let twin_name = arena.value_literal(Literal::Text(StringLiteral::new("twin".into())));
        let parting = arena.value_constructor(datatype, rule, vec![twin_name, left, unit, rest]);
        let unit_law = arena.value_constructor(datatype, rule, vec![name, left, right, parting]);
        let forged = arena.value_constructor(datatype, tag, vec![sorts, operations, unit_law]);
        let twin_declaration = DeclarationBuilder::new(&mut arena)
            .def(marked.declaration().levels().clone(), declared, forged)
            .named(marked.declaration().name().clone());
        let mut twin = declarations.clone();
        twin[usize::from(unital)] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("the twin's laws rewrite `mul(e(), x)` two ways");
        assert_eq!(refusal.position(), unital);
        assert_eq!(
            *refusal.error(),
            KernelError::PresentationRulesRefused(TheoryRuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault: TheoryRuleFault::Diverges(RuleIndex::from(1_usize)),
            }),
            "the kernel names the pair that parts"
        );
    }

    #[test]
    fn a_completed_group_readmits_from_the_peaks_its_value_names_1059()
    {
        let (arena, declarations, group) = exported(
            Path::new("model/identity/group-laws.gandr"),
            &named("Group"),
        );
        let DeclarationContent::Def { body, .. } =
            *declarations[usize::from(group)].declaration().content()
        else {
            panic!("`Group` is a definition");
        };
        let rules = TheoryRules::read(&arena, body).expect("`Group`'s rule chain reads");
        assert!(
            !rules.peaks().is_empty(),
            "`Group` crosses with the rules its completion derived"
        );
        Environment::replay(arena, &declarations)
            .unwrap_or_else(|refusal| panic!("`Group` readmits: {refusal:?}"));
    }

    /// #1510: a completion over an indexed sort states its derived rule
    /// without the indices and names the peak among the rules read with
    /// them, which is where the kernel replays it.
    #[test]
    fn an_indexed_completion_readmits_from_the_peaks_its_value_names_1510()
    {
        let (arena, declarations, views) = exported(
            Path::new("ledger/features/nested-operation-laws.gandr"),
            &named("EditedViews"),
        );
        let DeclarationContent::Def { body, .. } =
            *declarations[usize::from(views)].declaration().content()
        else {
            panic!("`EditedViews` is a definition");
        };
        let rules = TheoryRules::read(&arena, body).expect("`EditedViews`'s rule chain reads");
        assert!(
            !rules.peaks().is_empty() && rules.decided() != rules.rules(),
            "`EditedViews` crosses with a derived rule, and the kernel reads its rules indexed"
        );
        Environment::replay(arena, &declarations)
            .unwrap_or_else(|refusal| panic!("`EditedViews` readmits: {refusal:?}"));
    }
}

/// Effects as data readmit whole, and a program's row is a claim the kernel
/// re-derives: a twin performing an operation outside its row is refused by
/// name.
mod kernel_effect_tree_readmission
{
    use alloc::vec;
    use std::path::PathBuf;

    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_program_over_its_row_readmits_and_one_performing_outside_it_is_refused_by_name()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/effects/tree-rows.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("tree-rows lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("tree-rows' export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations).unwrap_or_else(|refusal| {
            panic!("tree-rows readmits, its programs and handlers pure: {refusal:?}")
        });
        let definition = |name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            let named = StructuredName::from(vec![segment]);
            let position = declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{name}` crossed"));
            let DeclarationContent::Def { declared, body } =
                *declarations[position].declaration().content()
            else {
                panic!("`{name}` is a definition");
            };
            (position, declared, body)
        };
        let (_, _, failing) = definition("failing");
        let (quiet, declared, body) = definition("quiet");
        let Some(&Value::Constructor {
            fields: ref raised, ..
        }) = arena.value(failing)
        else {
            panic!("`failing` is `Op(Left(Raise(4)), k)`");
        };
        let raise = raised[0];
        let Some(Value::Constructor {
            datatype,
            tag,
            fields,
        }) = arena.value(body).cloned()
        else {
            panic!("`quiet` is `Op(Left(Get), k)`");
        };
        // The twin keeps `quiet`'s type, `Prog(Either(StateOp, Void),
        // Integer)`, and its continuation, and performs `Left(Raise(4))`:
        // the front of its row is `StateOp`, and `Raise(4)` is an `ExnOp`.
        let forged = arena.value_constructor(datatype, tag, vec![raise, fields[1]]);
        let marked = &declarations[quiet];
        let twin_declaration = DeclarationBuilder::new(&mut arena)
            .def(marked.declaration().levels().clone(), declared, forged)
            .named(marked.declaration().name().clone());
        let mut twin = declarations.clone();
        twin[quiet] = MarkedDeclaration::new(marked.mark(), twin_declaration);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("an operation outside the row has no injection into it");
        assert_eq!(usize::from(refusal.position()), quiet);
        assert!(
            matches!(*refusal.error(), KernelError::ValueTypeMismatch(_)),
            "the kernel names the operation's type against the row's: {:?}",
            refusal.error()
        );
    }
}

/// A deep handler readmits as the fold of its effect's free model, a data
/// declaration the kernel admits ahead of the first handler of the effect,
/// one constructor per operation, at the level of the universe the handled
/// subject's result inhabits; the kernel types the fold, so a twin whose
/// model replies another type than the clauses resume with is refused by
/// name.
mod kernel_effect_handler_readmission
{
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;

    use super::Root;
    use super::Swept;
    use super::export;

    #[test]
    fn a_handler_crosses_as_the_fold_of_its_free_model_1624()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/effects/exit.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("exit lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("exit's export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations)
            .unwrap_or_else(|refusal| panic!("exit readmits, each handler a fold: {refusal:?}"));
        let position = |segments: &[&str]| {
            let named = StructuredName::from(
                segments
                    .iter()
                    .map(|&segment| NameSegment::from_text(segment.into()).expect("a name segment"))
                    .collect::<Vec<_>>(),
            );
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{}` crossed", segments.join(".")))
        };
        for handler in ["resumed", "answered", "coded", "summed", "printed"] {
            assert!(
                matches!(
                    *declarations[position(&[handler])].declaration().content(),
                    DeclarationContent::Def { .. }
                ),
                "`{handler}` crosses as a definition"
            );
        }
        // `Proc`'s model crosses ahead of its first handler, `Console`'s
        // ahead of its own.
        let model = position(&["effect", "free", "0"]);
        assert!(model < position(&["resumed"]));
        assert!(position(&["summed"]) < position(&["effect", "free", "1"]));
        assert!(position(&["effect", "free", "1"]) < position(&["printed"]));
        let marked = &declarations[model];
        let DeclarationContent::Data {
            ref parameters,
            ref constructors,
            kind,
            ..
        } = *marked.declaration().content()
        else {
            panic!("`Proc`'s free model is a data declaration");
        };
        let (parameters, mut constructors) = (parameters.clone(), constructors.clone());
        // The twin's `exit` continues from an integer, where `Proc` replies
        // the unit every clause resumes with.
        let Some(&ValueType::Thunk(continuation)) = arena.value_type(constructors[1][1])
        else {
            panic!("`exit`'s continuation is a thunk");
        };
        let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(continuation)
        else {
            panic!("`exit`'s continuation is a function of the reply");
        };
        let integer = arena.value_type_base(BaseType::Integer);
        let forged = arena.comp_type_arrow(integer, codomain);
        constructors[1][1] = arena.value_type_thunk(forged);
        let twin_model = DeclarationBuilder::new(&mut arena)
            .data(
                marked.declaration().levels().clone(),
                parameters,
                constructors,
                kind,
            )
            .named(marked.declaration().name().clone());
        let mut twin = declarations.clone();
        twin[model] = MarkedDeclaration::new(marked.mark(), twin_model);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("a clause resuming with the unit has no integer to give");
        assert_eq!(usize::from(refusal.position()), position(&["resumed"]));
        assert!(
            matches!(*refusal.error(), KernelError::ValueTypeMismatch(_)),
            "the kernel names the reply's type against the resumption's: {:?}",
            refusal.error()
        );
    }

    #[test]
    fn a_handler_of_several_operations_crosses_as_one_fold_2750()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/effects/state-handler.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("state-handler lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("state-handler's export decodes");
        let declarations = decoded.declarations().to_vec();
        let mut arena = decoded.arena().clone();
        Environment::replay(arena.clone(), &declarations).unwrap_or_else(|refusal| {
            panic!("state-handler readmits, each handler a fold: {refusal:?}")
        });
        let named = |segments: &[&str]| {
            let named = StructuredName::from(
                segments
                    .iter()
                    .map(|&segment| NameSegment::from_text(segment.into()).expect("a name segment"))
                    .collect::<Vec<_>>(),
            );
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
        };
        let position = |segments: &[&str]| {
            named(segments).unwrap_or_else(|| panic!("`{}` crossed", segments.join(".")))
        };
        // `constant` writes its clauses, and `answeredByPassing` hands each
        // operation to `Passing`'s; both fold `State`'s one model.
        for handler in ["constant", "answeredByPassing", "answeredFromZero"] {
            assert!(
                matches!(
                    *declarations[position(&[handler])].declaration().content(),
                    DeclarationContent::Def { .. }
                ),
                "`{handler}` crosses as a definition"
            );
        }
        let model = position(&["effect", "free", "0"]);
        assert!(model < position(&["constant"]));
        assert_eq!(
            named(&["effect", "free", "1"]),
            None,
            "the second handler of `State` folds the first's model"
        );
        let marked = &declarations[model];
        let DeclarationContent::Data {
            ref parameters,
            ref constructors,
            kind,
            ..
        } = *marked.declaration().content()
        else {
            panic!("`State`'s free model is a data declaration");
        };
        assert_eq!(
            constructors.iter().map(Vec::len).collect::<Vec<_>>(),
            [1, 2, 2],
            "`Return(x)`, then `get(p, k)` and `put(p, k)`"
        );
        let (parameters, mut constructors) = (parameters.clone(), constructors.clone());
        // The twin's `get` continues from the unit, where `State` replies the
        // integer state `constant`'s clause resumes with.
        let Some(&ValueType::Thunk(continuation)) = arena.value_type(constructors[1][1])
        else {
            panic!("`get`'s continuation is a thunk");
        };
        let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(continuation)
        else {
            panic!("`get`'s continuation is a function of the reply");
        };
        let unit = arena.value_type_unit();
        let forged = arena.comp_type_arrow(unit, codomain);
        constructors[1][1] = arena.value_type_thunk(forged);
        let twin_model = DeclarationBuilder::new(&mut arena)
            .data(
                marked.declaration().levels().clone(),
                parameters,
                constructors,
                kind,
            )
            .named(marked.declaration().name().clone());
        let mut twin = declarations.clone();
        twin[model] = MarkedDeclaration::new(marked.mark(), twin_model);
        let refusal = Environment::replay(arena, &twin)
            .expect_err("a clause resuming with an integer has no unit to give");
        assert_eq!(usize::from(refusal.position()), position(&["constant"]));
        assert!(
            matches!(*refusal.error(), KernelError::ValueTypeMismatch(_)),
            "the kernel names the reply's type against the resumption's: {:?}",
            refusal.error()
        );
    }

    #[test]
    fn a_handler_into_predicate_transformers_crosses_through_a_larger_model_2750()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/specification/state-wp.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("state-wp lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("state-wp's export decodes");
        let declarations = decoded.declarations().to_vec();
        Environment::replay(decoded.arena().clone(), &declarations).unwrap_or_else(|refusal| {
            panic!("state-wp readmits, its observation a fold: {refusal:?}")
        });
        let position = |segments: &[&str]| {
            let named = StructuredName::from(
                segments
                    .iter()
                    .map(|&segment| NameSegment::from_text(segment.into()).expect("a name segment"))
                    .collect::<Vec<_>>(),
            );
            declarations
                .iter()
                .position(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{}` crossed", segments.join(".")))
        };
        assert!(
            matches!(
                *declarations[position(&["incrObserved"])]
                    .declaration()
                    .content(),
                DeclarationContent::Def { .. }
            ),
            "`incrObserved` crosses as a definition"
        );
        // Its subject returns a predicate transformer, a type of types, so
        // the model it folds stands above the smallest universe.
        let model = position(&["effect", "free", "0"]);
        assert!(model < position(&["incrObserved"]));
        let DeclarationContent::Data { kind, .. } = *declarations[model].declaration().content()
        else {
            panic!("`StateLaws`'s free model is a data declaration");
        };
        assert!(
            matches!(
                decoded.arena().value_type(kind),
                Some(ValueType::Universe { level, .. }) if !bool::from(level.is_zero())
            ),
            "the model stands above level zero: {:?}",
            decoded.arena().value_type(kind)
        );
    }

    /// A scope that names no model is answered by the one model of its
    /// theory in scope, its carrier among the components the checker fills:
    /// the scope crosses as the one naming that model does, and the program
    /// calling it crosses after it.
    #[test]
    fn a_scope_answered_by_the_model_in_scope_crosses_as_naming_it_2755()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let path = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/effects/state-handler.gandr"
        ));
        let Swept::Exported(exported) = export(&pbg, path, Root::Fixture)
        else {
            panic!("state-handler lowers");
        };
        let decoded = decode(exported.artifact.as_image()).expect("state-handler's export decodes");
        let declarations = decoded.declarations();
        Environment::replay(decoded.arena().clone(), declarations).unwrap_or_else(|refusal| {
            panic!("state-handler readmits, the scope in scope a fold: {refusal:?}")
        });
        let content = |name: &str| {
            let named = StructuredName::from(Vec::from([
                NameSegment::from_text(name.into()).expect("a name segment")
            ]));
            let marked = declarations
                .iter()
                .find(|marked| *marked.declaration().name() == named)
                .unwrap_or_else(|| panic!("`{name}` crossed"));
            marked.declaration().content().clone()
        };
        assert!(
            matches!(content("inScopeFromZero"), DeclarationContent::Def { .. }),
            "`inScopeFromZero` crosses as a definition"
        );
        // The decoder shares every repeated subterm, so two definitions whose
        // types and bodies are one term name the same roots.
        assert_eq!(
            content("answeredInScope"),
            content("answeredByPassing"),
            "the model in scope answers the scope as naming it does"
        );
    }
}
