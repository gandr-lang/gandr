use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use super::BackendArtifact;
use super::CheckpointAddress;
use super::CheckpointObserver;
use super::CheckpointStore as _;
use super::CheckpointStoreError;
use super::FileCheckpointStore;
use super::MemoryCheckpointStore;
use super::address_of;
use super::artifact_bytes;
use super::decode_checkpoints;
use super::encode_checkpoints;
use super::persist;
use super::restore;
use super::restored;
use super::stored;
use crate::boundary::NodeIndex;
use crate::boundary::Occurrence;
use crate::boundary::RecordCount;
use crate::checkpoint::Answer;
use crate::checkpoint::Checkpoints;
use crate::checkpoint::ItemCheckpoint;
use crate::codec::Bytes;
use crate::codec::CheckpointBytes;
use crate::codec::UnsupportedPersistence;
use crate::codec::reference_bytes;
use crate::content::ContentNode;
use crate::content::Sort;
use crate::fixture::Digits;
use crate::fixture::Key;
use crate::fixture::Label;
use crate::fixture::Noise;
use crate::fixture::Position;
use crate::fixture::Scratch;
use crate::fixture::checked;
use crate::fixture::declaration;
use crate::fixture::every_former;
use crate::fixture::integer;
use crate::fixture::integers;
use crate::fixture::noisy;
use crate::footprint::footprint_of;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;
use crate::region::Reference;
use crate::typing::Refusal;
use crate::typing::Typing;

/// An observer that records what it is told.
///
/// # Specification
/// - executable: none — the lists retain notifications, not the operations that
///   should have emitted them.
///
/// # Adequacy
/// - hypothesis: L3 — successful stores, absent restores and failed publication
///   are observed through the recording lists. Distinct missing addresses
///   retain notification order; the observer does not judge the persistence
///   operation.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
#[derive(Debug, Default)]
struct Recording
{
    /// The addresses stored.
    stored: Vec<CheckpointAddress>,
    /// The addresses whose restore returned nothing.
    invalidated: Vec<CheckpointAddress>,
}

impl CheckpointObserver for Recording
{
    /// Record the stored address.
    ///
    /// # Specification
    /// - ensures: append this stored address without invalidating an address.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successful memory and file persistence append
    ///   notifications; failed publication leaves the list empty. The predicate
    ///   observes length and last address, not a cloned history prefix.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    #[spec(
            captures: [
                before = self.stored.len(),
                invalidated = self.invalidated.len(),
            ],
            ensures: |ret| {
                before.checked_add(1) == Some(self.stored.len())
                    && self.stored.last() == Some(&address)
                    && self.invalidated.len() == invalidated
            },
        )]
    fn stored(
        &mut self,
        address: CheckpointAddress,
    )
    {
        self.stored.push(address);
    }

    /// Record the invalidated address.
    ///
    /// # Specification
    /// - ensures: append this invalidated address without recording a store.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct missing addresses preserve notification
    ///   order; other-backend and other-program restores are also observed. The
    ///   predicate checks append extent and the final address without cloning
    ///   earlier entries.
    /// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    #[spec(
            captures: [before = self.invalidated.len(), stored = self.stored.len()],
            ensures: |ret| {
                before.checked_add(1) == Some(self.invalidated.len())
                    && self.invalidated.last() == Some(&address)
                    && self.stored.len() == stored
            },
        )]
    fn invalidated(
        &mut self,
        address: CheckpointAddress,
    )
    {
        self.invalidated.push(address);
    }
}

/// The backend every fixture is judged by.
///
/// # Specification
/// trivial.
fn backend() -> BackendArtifact
{
    BackendArtifact::from(b"core-checker".as_slice())
}

/// The program `a = 1; b = 2`.
///
/// # Specification
/// trivial.
fn pair() -> Program
{
    integers(CoreArena::new(), &[
        (Key("a"), Digits("1")),
        (Key("b"), Digits("2")),
    ])
}

/// The canonical bytes of `checkpoints`.
///
/// # Specification
/// - requires: the checkpoint set is encodable.
/// - ensures: the canonical bytes of that set.
/// - panics: an unencodable fixture violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the finite semantic corpus and deliberately noncanonical
///   tables use encodable fixtures. The partial precondition checks unresolved
///   main-content nodes only, not support, typing planes or machine widths.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
#[spec(
        requires: checkpoints.items().iter().all(|checkpoint| {
            checkpoint
                .content()
                .nodes()
                .iter()
                .all(|node| !matches!(*node.former(), ContentNode::Unresolved(_)))
        }),
    )]
fn bytes_of(checkpoints: &Checkpoints) -> CheckpointBytes
{
    encode_checkpoints(checkpoints).expect("supported")
}

/// Decode `bytes`.
///
/// # Specification
/// trivial.
fn decoded(bytes: &CheckpointBytes) -> Result<Checkpoints, CheckpointStoreError>
{
    decode_checkpoints(bytes)
}

/// A one-item set whose content is the closed formers `nodes`, listed in the
/// given order under a body root of 0.
///
/// # Specification
/// - requires: `nodes` is closed and acyclic, every child in range and of its
///   sort, no two entries equal.
/// - ensures: one unsigned, owed item named hand, with body root zero and
///   exactly the supplied formers in the supplied order, every scope and edge
///   empty; discovery order and reachability are not required.
///
/// # Adequacy
/// - hypothesis: L3 — reversed discovery and unreachable entries reach the
///   decoder. The predicate checks node count and fixed metadata without
///   cloning the moved node vector or certifying its graph.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `persistence::tests::file_load_rejects_parseable_noncanonical_payload_after_integrity_checks`
#[spec(
        captures: [count = nodes.len()],
        ensures: |ret| {
            ret.budget() == CheckBudget::DEFAULT
                && ret.items().len() == 1
                && ret.items().first().is_some_and(|checkpoint| {
                    let content = checkpoint.content();
                    content.nodes().len() == count
                        && matches!(content.declaration(), crate::DeclarationRoots::Value {signature:Maybe::Absent(signature::Absent::Unsigned),body:Maybe::Present(root),laws} if *root == NodeIndex::from(0_usize) && laws.is_empty())
                        && checkpoint.support().is_empty()
                        && matches!(checkpoint.typing(), &Typing::Owed)
                        && match *content.reference() {
                            | Reference::Item {
                                ref key,
                                occurrence,
                            } => key.as_ref() == b"hand" && usize::from(occurrence) == 0,
                            | _ => false,
                        }
                })
        },
    )]
fn hand_made(nodes: Vec<ContentNode>) -> Checkpoints
{
    let parts = nodes
        .into_iter()
        .map(|former| {
            let edges = former.children().iter().count();
            crate::support::NodeParts {
                former,
                cover: vec![gandr_core_term::support::Thinning::empty(); edges],
                scope: gandr_core_term::support::Scope::default(),
            }
        })
        .collect();
    let nodes = crate::support::assemble(parts).expect("a closed acyclic table");
    let content = crate::content::ItemContent::from_parts(
        Reference::Item {
            key: ItemKey::from("hand"),
            occurrence: Occurrence::from(0_usize),
        },
        crate::content::DeclarationRoots::Value {
            signature: Maybe::Absent(signature::Absent::Unsigned),
            body: Maybe::Present(NodeIndex::from(0_usize)),
            laws: Vec::new(),
        },
        nodes,
        vec![gandr_core_term::support::Thinning::empty()],
    );
    let footprint = footprint_of(&content);
    Checkpoints::new(CheckBudget::DEFAULT, vec![ItemCheckpoint::new(
        content,
        footprint,
        Vec::new(),
        Typing::Owed,
    )])
}

/// `bytes` with the first occurrence of `from` replaced by `to`.
///
/// # Specification
/// - requires: from is nonempty and occurs in bytes.
/// - ensures: replace only its first occurrence, preserving the prefix and
///   suffix even when the replacement length differs.
/// - panics: a missing or empty pattern violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — growing and deleting the first of two occurrences
///   preserve the surrounding bytes. Canonicality mutations exercise
///   equal-width rewrites; the postcondition compares borrowed slices, not a
///   rebuilt output buffer.
/// - witness: `persistence::tests::rewriting_the_first_frame_preserves_unequal_length_neighbors`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
#[spec(
        requires: !from.as_ref().is_empty(),
        ensures: |ret| {
            bytes
                .as_ref()
                .windows(from.as_ref().len())
                .position(|window| window == from.as_ref())
                .is_some_and(|at| {
                    match (
                        at.checked_add(from.as_ref().len()),
                        at.checked_add(to.as_ref().len()),
                    ) {
                        | (Some(after), Some(end)) => {
                            ret.as_ref().get(.. at) == bytes.as_ref().get(.. at)
                                && ret.as_ref().get(at .. end) == Some(to.as_ref())
                                && ret.as_ref().get(end ..) == bytes.as_ref().get(after ..)
                        },
                        | _ => false,
                    }
                })
        },
    )]
fn rewritten(
    bytes: &CheckpointBytes,
    from: &CheckpointBytes,
    to: &CheckpointBytes,
) -> CheckpointBytes
{
    let (bytes, from, to) = (bytes.as_ref(), from.as_ref(), to.as_ref());
    let at = bytes
        .windows(from.len())
        .position(|window| window == from)
        .expect("the pattern occurs");
    let mut out = Vec::with_capacity(bytes.len());
    out.extend_from_slice(bytes.get(.. at).expect("in range"));
    out.extend_from_slice(to);
    out.extend_from_slice(
        bytes
            .get(at.saturating_add(from.len()) ..)
            .expect("in range"),
    );
    CheckpointBytes::from(out)
}

/// The program of one item `nested` with `signature` and `body`.
///
/// # Specification
/// - ensures: one item named nested at origin zero retains the supplied roots
///   and arena, including deliberately unresolved identifiers.
///
/// # Adequacy
/// - hypothesis: L3 — foreign and opaque children in all four sorts reach exact
///   persistence refusals. The predicate checks item identity and root slots;
///   it does not clone the moved arena or certify that those roots resolve.
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
        ensures: |ret| {
            ret.items().len() == 1
                && ret.items().first().is_some_and(|item| {
                    matches!(item.declaration().content(), gandr_core_checker::DeclarationContent::Value {signature:held_signature,body:held_body} if *held_signature == signature && *held_body == body)
                })
                && ret
                    .references()
                    .first()
                    .is_some_and(|reference| match *reference {
                        | Reference::Item {
                            ref key,
                            occurrence,
                        } => key.as_ref() == b"nested" && usize::from(occurrence) == 0,
                        | _ => false,
                    })
        },
    )]
fn nested(
    arena: CoreArena,
    signature: Maybe<gandr_core_term::ValueTypeId, signature::Absent>,
    body: Maybe<gandr_core_term::ValueId, body::Absent>,
) -> Program
{
    Program::new(arena, vec![Item::new(
        ItemKey::from("nested"),
        declaration(Position(0_usize), signature, body),
    )])
    .expect("one item ascends")
}

/// The kind of a typing, as a name.
///
/// # Specification
/// trivial.
fn kind(typing: &Typing) -> Key
{
    Key(match *typing {
        Typing::Data => "data",
        Typing::Refused(Refusal::NotADataType(_)) => "not-a-data-type",
        Typing::Refused(Refusal::Located { .. }) => "located",
        Typing::Refused(Refusal::DataKindNotUniverse(_)) => "data-kind-not-universe",
        Typing::Refused(Refusal::DataFieldLevel { .. }) => "data-field-level",
        Typing::Refused(Refusal::RuleNotPresentable { .. }) => "rule-not-presentable",
        Typing::Refused(Refusal::RuleNotRespected { .. }) => "rule-not-respected",
        Typing::Refused(Refusal::NotApart { .. }) => "not-apart",
        Typing::Refused(Refusal::LoopNotRespected { .. }) => "loop-not-respected",
        Typing::Refused(Refusal::LoopUndecided { .. }) => "loop-undecided",
        Typing::Refused(Refusal::DataArgumentArity(_)) => "data-argument-arity",
        Typing::Refused(Refusal::UnknownConstructor { .. }) => "unknown-constructor",
        Typing::Refused(Refusal::ConstructorArity(_)) => "constructor-arity",
        Typing::Refused(Refusal::NonExhaustiveDataCase(_)) => "non-exhaustive-data-case",
        Typing::Refused(Refusal::UndecidedCoverage(_)) => "undecided-coverage",
        Typing::Refused(Refusal::AbsentRecordField(_)) => "absent-record-field",
        Typing::Refused(Refusal::AbsentTupleComponent(_)) => "absent-tuple-component",
        Typing::Refused(Refusal::MissingRecordField { .. }) => "missing-record-field",
        Typing::Checked { .. } => "checked",
        Typing::Synthesised { .. } => "synthesised",
        Typing::Owed => "owed",
        Typing::Suspended => "suspended",
        Typing::Refused(Refusal::PathCode(_)) => "path-code",
        Typing::Refused(Refusal::EndpointMismatch { .. }) => "endpoint-mismatch",
        Typing::Refused(Refusal::CompoundEndpoint { .. }) => "compound-endpoint",
        Typing::Refused(Refusal::FunextUnsupported { .. }) => "funext-unsupported",
        Typing::Refused(Refusal::PointwiseDistinct(_)) => "pointwise-distinct",
        Typing::Refused(Refusal::EquivUnsupported { .. }) => "equiv-unsupported",
        Typing::Refused(Refusal::UncertifiedStratum { .. }) => "uncertified-stratum",
        Typing::Refused(Refusal::RoundTripDistinct(_)) => "round-trip-distinct",
        Typing::Refused(Refusal::NotOver { .. }) => "not-over",
        Typing::Refused(Refusal::UaUncertified { .. }) => "ua-uncertified",
        Typing::Refused(Refusal::UaInequivalent { .. }) => "ua-inequivalent",
        Typing::Refused(Refusal::SessionNotEquivalent(_)) => "session-not-equivalent",
        Typing::Refused(Refusal::SessionNotSubtype(_)) => "session-not-subtype",
        Typing::Refused(Refusal::SessionCodeExpected(_)) => "session-code-expected",
        Typing::Refused(Refusal::NonCovariantMotive(_)) => "non-covariant-motive",
        Typing::Refused(Refusal::RideUnsupported(_)) => "ride-unsupported",
        Typing::Refused(Refusal::RunNotAdmitted { .. }) => "run-not-admitted",
        Typing::Refused(Refusal::ForwardUnsupported(_)) => "forward-unsupported",
        Typing::Refused(Refusal::Boundary(_)) => "boundary",
        Typing::Refused(Refusal::Access { .. }) => "access",
        Typing::Refused(Refusal::EffectSignatureConflict { .. }) => "effect-signature-conflict",
        Typing::Refused(Refusal::UnknownOperation { .. }) => "unknown-operation",
        Typing::Refused(Refusal::HandlerCoverage { .. }) => "handler-coverage",
        Typing::Refused(Refusal::ShiftWithoutReset { .. }) => "shift-without-reset",
        Typing::Refused(Refusal::DependentStack { .. }) => "dependent-stack",
        Typing::Refused(Refusal::TypeMismatch { .. }) => "type-mismatch",
        Typing::Refused(Refusal::ShapeMismatch { .. }) => "shape-mismatch",
        Typing::Refused(Refusal::NotSynthesisable { .. }) => "not-synthesisable",
        Typing::Refused(Refusal::UnknownConstant { .. }) => "unknown-constant",
        Typing::Refused(Refusal::OutOfFragment { .. }) => "out-of-fragment",
        Typing::Refused(Refusal::UnboundIndex { .. }) => "unbound-index",
        Typing::Refused(Refusal::BudgetExceeded { .. }) => "budget-exceeded",
        Typing::Refused(Refusal::DanglingNode { .. }) => "dangling-node",
        Typing::Refused(Refusal::AdmissionOrder) => "admission-order",
        Typing::Refused(Refusal::MachineInvariant) => "machine-invariant",
        Typing::Refused(Refusal::SortMismatch { .. }) => "sort-mismatch",
        Typing::Refused(Refusal::LevelMismatch { .. }) => "level-mismatch",
        Typing::Refused(Refusal::DependentBind { .. }) => "dependent-bind",
        Typing::Refused(Refusal::Undecided { .. }) => "undecided",
        Typing::Refused(Refusal::FamilyArity { .. }) => "family-arity",
        Typing::Refused(Refusal::FamilyArgumentClassifier { .. }) => "family-argument-classifier",
        Typing::Refused(Refusal::StaticLambdaArgument { .. }) => "static-lambda-argument",
        Typing::Refused(Refusal::StaticClassifierExpected { .. }) => "static-classifier-expected",
        Typing::Refused(Refusal::NegativeOccurrence(_)) => "negative-occurrence",
        Typing::Refused(Refusal::NestedOccurrence(_)) => "nested-occurrence",
        Typing::Refused(Refusal::IndexOccurrence(_)) => "index-occurrence",
        Typing::Refused(Refusal::NonUniformOccurrence(_)) => "non-uniform-occurrence",
        Typing::Refused(Refusal::CrossBlockReference { .. }) => "cross-block-reference",
        Typing::Refused(Refusal::StageNotBelow { .. }) => "stage-not-below",
        Typing::Refused(Refusal::AbstractKindNotUniverse(_)) => "abstract-kind-not-universe",
        Typing::Refused(Refusal::RepresentationAboveKind { .. }) => "representation-above-kind",
        Typing::Refused(Refusal::NotAnAbstractType(_)) => "not-an-abstract-type",
        Typing::Refused(Refusal::SealSiteRepeated(_)) => "seal-site-repeated",
        Typing::Refused(Refusal::UnenclosedRun { .. }) => "unenclosed-run",
        Typing::Refused(Refusal::SessionMismatch { .. }) => "session-mismatch",
        Typing::Refused(Refusal::Linearity { .. }) => "linearity",
        Typing::Refused(Refusal::CapabilityForged { .. }) => "capability-forged",
        Typing::Refused(Refusal::CapabilityAmplified { .. }) => "capability-amplified",
        Typing::Refused(Refusal::CapabilityOutsideAuthority { .. }) => {
            "capability-outside-authority"
        },
        Typing::Refused(Refusal::CapabilityEscaped { .. }) => "capability-escaped",
        Typing::Refused(Refusal::CapabilityConsumable(_)) => "capability-consumable",
        Typing::Refused(Refusal::CapabilityUngranted(_)) => "capability-ungranted",
    })
}

#[test]
fn independently_built_programs_have_identical_bytes_and_addresses()
{
    let entries = [(Key("a"), Digits("1")), (Key("b"), Digits("2"))];
    let mut quiet = integers(CoreArena::new(), &entries);
    let mut loud = integers(noisy(Noise(4)), &entries);
    assert_eq!(
        address_of(&quiet),
        address_of(&loud),
        "the address reads content, never ids"
    );
    assert_eq!(
        bytes_of(&checked(&mut quiet)),
        bytes_of(&checked(&mut loud)),
        "so do the checkpoint bytes"
    );
}

#[test]
fn meaningful_program_changes_and_source_order_change_identity()
{
    let variants = [
        vec![(Key("a"), Digits("1")), (Key("b"), Digits("2"))],
        vec![(Key("a"), Digits("1")), (Key("b"), Digits("3"))],
        vec![(Key("b"), Digits("2")), (Key("a"), Digits("1"))],
        vec![(Key("a"), Digits("1")), (Key("c"), Digits("2"))],
        vec![(Key("a"), Digits("1"))],
        vec![(Key("a"), Digits("1")), (Key("a"), Digits("2"))],
    ];
    let addresses: BTreeSet<CheckpointAddress> = variants
        .iter()
        .map(|entries| address_of(&integers(CoreArena::new(), entries)).expect("resolved"))
        .collect();
    assert_eq!(
        addresses.len(),
        variants.len(),
        "a value, an order, a key, a deletion and an occurrence each change the address"
    );
}

#[test]
fn canonical_maps_and_supported_semantic_variants_round_trip()
{
    let checkpoints = checked(&mut every_former(Noise(0)));
    let kinds: BTreeSet<&str> = checkpoints
        .items()
        .iter()
        .map(|checkpoint| kind(checkpoint.typing()).0)
        .collect();
    let per_item: Vec<(&Reference, &str)> = checkpoints
        .items()
        .iter()
        .map(|checkpoint| {
            (
                checkpoint.content().reference(),
                kind(checkpoint.typing()).0,
            )
        })
        .collect();
    for expected in [
        "checked",
        "synthesised",
        "owed",
        "type-mismatch",
        "shape-mismatch",
        "not-synthesisable",
        "unknown-constant",
        "out-of-fragment",
        "unbound-index",
        "family-arity",
        "family-argument-classifier",
        "static-lambda-argument",
        "static-classifier-expected",
    ] {
        assert!(
            kinds.contains(expected),
            "the fixture reaches {expected}: {per_item:?}"
        );
    }
    assert!(
            checkpoints.items().iter().any(|checkpoint| checkpoint
                .support()
                .iter()
                .any(|answered| matches!(*answered.answer(), Answer::Typed(ref ty) if ty.nodes().len() > 1))),
            "some support holds a structured answer"
        );
    let bytes = bytes_of(&checkpoints);
    assert_eq!(
        bytes,
        bytes_of(&checked(&mut every_former(Noise(3)))),
        "built after unrelated nodes, the same program has the same bytes"
    );
    assert_eq!(
        decoded(&bytes),
        Ok(checkpoints),
        "and the bytes decode to the set"
    );
}

#[test]
fn sealed_content_and_its_refusals_round_trip()
{
    use gandr_core_checker::AbstractType;
    use gandr_core_checker::ComponentOrdinal;
    use gandr_core_checker::SealSite;
    use gandr_core_checker::SealingSite;
    use gandr_kernel_term::SealExtent;
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let stray = arena.value_type_abstract(ConstantIndex::from(4_usize));
    let sealed = |position: usize, kind, representation, component: usize| {
        Item::new(
            ItemKey::from(format!("abstract-{position}").as_str()),
            gandr_core_checker::Declaration::abstract_type(
                ConstantIndex::from(position),
                AbstractType::new(
                    kind,
                    representation,
                    SealExtent::from(1_usize),
                    SealSite::new(
                        SealingSite::from(0_usize),
                        ComponentOrdinal::from(component),
                    ),
                ),
                gandr_core_checker::OriginToken::from(position),
            ),
        )
    };
    let items = vec![
        sealed(0, small, integer, 0),
        Item::new(
            ItemKey::from("member"),
            declaration(
                Position(1),
                Maybe::Present(atom),
                Maybe::Absent(body::Absent::Hole),
            ),
        ),
        sealed(2, integer, integer, 1),
        sealed(3, small, small, 2),
        sealed(4, small, integer, 0),
        Item::new(
            ItemKey::from("stray"),
            declaration(
                Position(5),
                Maybe::Present(stray),
                Maybe::Absent(body::Absent::Hole),
            ),
        ),
    ];
    let checkpoints = checked(&mut Program::new(arena, items).expect("positions ascend"));
    let kinds: Vec<&str> = checkpoints
        .items()
        .iter()
        .map(|checkpoint| kind(checkpoint.typing()).0)
        .collect();
    assert_eq!(
        kinds,
        [
            "data",
            "owed",
            "abstract-kind-not-universe",
            "representation-above-kind",
            "seal-site-repeated",
            "not-an-abstract-type",
        ],
        "an atom, a member owed at it, and each refusal of sealing"
    );
    assert_eq!(
        decoded(&bytes_of(&checkpoints)),
        Ok(checkpoints),
        "abstract roots, their extent and site, and every refusal round trip"
    );
}

#[test]
fn universe_sorts_and_levels_round_trip()
{
    let level = Level::var(LevelVar::new(LevelVarIndex::from(37_u32)))
        .succ()
        .expect("far from the ceiling");
    let mut arena = CoreArena::new();
    let sorts = [
        gandr_core_term::Sort::Ground(GroundSort::Value),
        gandr_core_term::Sort::Ground(GroundSort::Computation),
        gandr_core_term::Sort::Parameter(gandr_core_term::SortParameter::from(2_u32)),
    ];
    let items = sorts
        .into_iter()
        .enumerate()
        .map(|(position, sort)| {
            let universe = arena.value_type_universe(sort, level.clone());
            Item::new(
                ItemKey::from(format!("universe-{position}").as_str()),
                declaration(
                    Position(position),
                    Maybe::Present(universe),
                    Maybe::Absent(body::Absent::Hole),
                ),
            )
        })
        .collect();
    let checkpoints = checked(&mut Program::new(arena, items).expect("positions ascend"));
    let tables: Vec<Vec<ContentNode>> = checkpoints
        .items()
        .iter()
        .map(|checkpoint| {
            checkpoint
                .content()
                .nodes()
                .iter()
                .map(crate::support::SupportedNode::former)
                .cloned()
                .collect()
        })
        .collect();
    let expected: Vec<Vec<ContentNode>> = sorts
        .into_iter()
        .map(|sort| {
            vec![ContentNode::Universe {
                sort,
                level: level.clone(),
            }]
        })
        .collect();
    assert_eq!(
        expected, tables,
        "each signature's content is its universe, sort and level both"
    );
    assert_eq!(
        decoded(&bytes_of(&checkpoints)),
        Ok(checkpoints),
        "and each sort and its level round trip"
    );
}

#[test]
fn a_suspended_typing_round_trips()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded_type = arena.value_type_element(code, Level::zero());
    let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::zero(),
        ),
    ));
    let items = vec![
        Item::new(
            ItemKey::from("code"),
            declaration(
                Position(0_usize),
                Maybe::Present(universe),
                Maybe::Absent(body::Absent::Hole),
            ),
        ),
        Item::new(
            ItemKey::from("zero"),
            declaration(
                Position(1_usize),
                Maybe::Present(decoded_type),
                Maybe::Present(zero),
            ),
        ),
    ];
    let checkpoints = checked(&mut Program::new(arena, items).expect("positions ascend"));
    let kinds: Vec<&str> = checkpoints
        .items()
        .iter()
        .map(|checkpoint| kind(checkpoint.typing()).0)
        .collect();
    assert_eq!(
        kinds,
        ["owed", "suspended"],
        "a value at an owed code's decode waits on it"
    );
    assert_eq!(
        decoded(&bytes_of(&checkpoints)),
        Ok(checkpoints),
        "and the suspension round trips"
    );
}

#[test]
fn oversized_level_offset_is_refused_with_exact_error()
{
    let at_offset = |offset: u64| {
        let mut level = Level::var(LevelVar::new(LevelVarIndex::from(0_u32)));
        for _ in 0 .. offset {
            level = level.succ().expect("far from the ceiling");
        }
        let mut arena = CoreArena::new();
        let universe =
            arena.value_type_universe(gandr_core_term::Sort::Ground(GroundSort::Value), level);
        let mut program = Program::new(arena, vec![Item::new(
            ItemKey::from("universe"),
            declaration(
                Position(0_usize),
                Maybe::Present(universe),
                Maybe::Absent(body::Absent::Hole),
            ),
        )])
        .expect("one item ascends");
        checked(&mut program)
    };
    let under = at_offset(4095_u64);
    assert_eq!(
        decoded(&bytes_of(&under)),
        Ok(under),
        "an offset under the cap round trips"
    );
    let capped = at_offset(4096_u64);
    let refusal = CheckpointStoreError::LevelOffsetTooLarge {
        offset: LevelOffset::from(4096_u64),
    };
    assert_eq!(encode_checkpoints(&capped), Err(refusal));
    let raw = crate::codec::checkpoint_frame(&capped).expect("raw capped frame");
    assert_eq!(decoded(&raw), Err(refusal));
}

#[test]
fn checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes()
{
    let bytes = Vec::from(bytes_of(&checked(&mut pair())));
    for length in 0 .. bytes.len() {
        let prefix = bytes.get(.. length).expect("in range").to_vec();
        assert_eq!(
            decoded(&CheckpointBytes::from(prefix)),
            Err(CheckpointStoreError::Corrupt),
            "a prefix of {length} bytes is corrupt"
        );
    }
    let mut corrupted = bytes.clone();
    if let Some(first) = corrupted.first_mut() {
        *first ^= 0xFF_u8;
    }
    assert_eq!(
        decoded(&CheckpointBytes::from(corrupted)),
        Err(CheckpointStoreError::Corrupt),
        "a broken magic"
    );
    let mut extended = bytes;
    extended.push(0_u8);
    assert_eq!(
        decoded(&CheckpointBytes::from(extended)),
        Err(CheckpointStoreError::Corrupt),
        "a trailing byte"
    );
}

#[test]
fn checkpoint_decoder_rejects_parseable_noncanonical_payload()
{
    // r = (a, b): the footprint lists a then b; swapped, the set parses
    // and sorts back, so the payload is not the spelling of its value.
    let mut arena = CoreArena::new();
    let a = arena.value_literal(integer(Digits("1")));
    let b = arena.value_literal(integer(Digits("2")));
    let first = arena.value_constant(ConstantIndex::from(0_usize));
    let second = arena.value_constant(ConstantIndex::from(1_usize));
    let pair = arena.value_tuple(&[first, second]);
    let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
    let mut program = Program::new(arena, vec![
        Item::new(
            ItemKey::from("a"),
            declaration(Position(0_usize), unsigned(), Maybe::Present(a)),
        ),
        Item::new(
            ItemKey::from("b"),
            declaration(Position(1_usize), unsigned(), Maybe::Present(b)),
        ),
        Item::new(
            ItemKey::from("r"),
            declaration(Position(2_usize), unsigned(), Maybe::Present(pair)),
        ),
    ])
    .expect("positions ascend");
    let bytes = bytes_of(&checked(&mut program));
    let reference = |key: &str| {
        Vec::from(reference_bytes(&Reference::Item {
            key: ItemKey::from(key),
            occurrence: Occurrence::from(0_usize),
        }))
    };
    let ordered = CheckpointBytes::from([reference("a"), reference("b")].concat());
    let swapped = CheckpointBytes::from([reference("b"), reference("a")].concat());
    assert_eq!(
        decoded(&rewritten(&bytes, &ordered, &swapped)),
        Err(CheckpointStoreError::NonCanonical),
        "a set out of order"
    );

    let literal = |digits: &'static str| ContentNode::Literal(integer(Digits(digits)));
    let out_of_discovery = hand_made(vec![
        ContentNode::Tuple(vec![NodeIndex::from(2_usize), NodeIndex::from(1_usize)]),
        literal("1"),
        literal("2"),
    ]);
    let raw = crate::codec::checkpoint_frame(&out_of_discovery).expect("raw reordered table");
    assert_eq!(decoded(&raw), Err(CheckpointStoreError::NonCanonical));
    let unreached = hand_made(vec![literal("1"), literal("2")]);
    let raw = crate::codec::checkpoint_frame(&unreached).expect("raw unreachable node");
    assert_eq!(decoded(&raw), Err(CheckpointStoreError::NonCanonical));
}

#[test]
fn file_load_rejects_parseable_noncanonical_payload_after_integrity_checks()
{
    let scratch = Scratch::new(Label("noncanonical-file"));
    let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
    let address = address_of(&pair()).expect("resolved");
    let payload = crate::codec::checkpoint_frame(&hand_made(vec![
        ContentNode::Literal(integer(Digits("1"))),
        ContentNode::Literal(integer(Digits("2"))),
    ]))
    .expect("raw noncanonical table");
    let artifact =
        artifact_bytes(address, backend(), Bytes(payload.as_ref())).expect("representable");
    std::fs::write(store.record_path(address), &artifact.0).expect("write");
    assert_eq!(
        store.load(
            address,
            BackendArtifact::from(b"another backend".as_slice())
        ),
        Err(CheckpointStoreError::NonCanonical),
        "integrity passes; decoding fails before the backend mismatch is considered"
    );
}

#[test]
fn a_failed_file_store_strands_no_temporary_in_the_record_directory()
{
    let scratch = Scratch::new(Label("failed-store"));
    let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
    let mut program = pair();
    let address = address_of(&program).expect("resolved");
    std::fs::create_dir_all(store.record_path(address)).expect("occupy the record path");
    let checkpoints = checked(&mut program);
    let mut observer = Recording::default();
    assert_eq!(
        persist(&mut store, &program, backend(), &checkpoints, &mut observer),
        Err(CheckpointStoreError::Io),
        "the rename onto a directory fails"
    );
    assert!(
        observer.stored.is_empty(),
        "a failed publication is not observed as stored"
    );
    assert!(
        observer.invalidated.is_empty(),
        "storage does not invalidate a restore"
    );
    assert_eq!(
        scratch.entries(),
        [address.to_hex()],
        "only the occupying directory remains"
    );
}

#[test]
fn a_store_never_writes_through_a_file_it_did_not_create()
{
    let scratch = Scratch::new(Label("squatter"));
    let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
    let mut program = pair();
    let address = address_of(&program).expect("resolved");
    let hex = address.to_hex();
    let squatters = [
        format!("{hex}.tmp"),
        format!("{hex}.tmp-{}", std::process::id()),
        format!("{hex}.tmp-{}-0000000000000000", std::process::id()),
    ];
    for name in &squatters {
        std::fs::write(scratch.path().join(name), b"squatter").expect("plant");
    }
    let checkpoints = checked(&mut program);
    store
        .store(address, backend(), &checkpoints)
        .expect("the store succeeds");
    for name in &squatters {
        assert_eq!(
            std::fs::read(scratch.path().join(name)).expect("still there"),
            b"squatter",
            "{name} is byte-identical"
        );
    }
    assert_eq!(
        store.load(address, backend()),
        Ok(Maybe::Present(checkpoints)),
        "the record was published beside them"
    );
    assert_eq!(
        scratch.entries().len(),
        squatters.len() + 1,
        "and nothing else"
    );
}

#[test]
fn concurrent_stores_of_one_address_leave_the_record_and_no_temporary()
{
    let scratch = Scratch::new(Label("concurrent"));
    let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
    let mut program = pair();
    let address = address_of(&program).expect("resolved");
    let checkpoints = checked(&mut program);
    std::thread::scope(|scope| {
        for _ in 0_usize .. 4_usize {
            let mut store = store.clone();
            let checkpoints = &checkpoints;
            let _handle = scope.spawn(move || {
                for _ in 0_usize .. 16_usize {
                    store
                        .store(address, backend(), checkpoints)
                        .expect("every store succeeds");
                }
            });
        }
    });
    assert_eq!(
        scratch.entries(),
        [address.to_hex()],
        "one record, no temporary"
    );
    assert_eq!(
        store.load(address, backend()),
        Ok(Maybe::Present(checkpoints)),
        "and it is whole"
    );
}

#[test]
fn supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file()
{
    let mut program = every_former(Noise(0));
    let checkpoints = checked(&mut program);
    let address = address_of(&program).expect("resolved");
    let other = BackendArtifact::from(b"another checker".as_slice());
    let mut observer = Recording::default();

    let mut memory = MemoryCheckpointStore::default();
    assert_eq!(
        persist(
            &mut memory,
            &program,
            backend(),
            &checkpoints,
            &mut observer
        ),
        Ok(address),
        "persisted at the program's address"
    );
    assert_eq!(observer.stored, [address], "and the observer told");
    assert_eq!(
        restore(&mut memory, &program, address, backend(), &mut observer),
        Ok(Maybe::Present(checkpoints.clone())),
        "memory round trip"
    );
    assert_eq!(
        memory.load(address, other),
        Ok(Maybe::Absent(stored::Absent::OtherBackend)),
        "another backend's record is not this one's"
    );

    let scratch = Scratch::new(Label("round-trip"));
    let mut file = FileCheckpointStore::open(scratch.path()).expect("open");
    let _address =
        persist(&mut file, &program, backend(), &checkpoints, &mut observer).expect("persisted");
    drop(file);
    let mut reopened = FileCheckpointStore::open(scratch.path()).expect("reopen");
    assert_eq!(
        restore(&mut reopened, &program, address, backend(), &mut observer),
        Ok(Maybe::Present(checkpoints)),
        "file round trip through a reopened store"
    );
    assert_eq!(
        restore(&mut reopened, &program, address, other, &mut observer),
        Ok(Maybe::Absent(restored::Absent::OtherBackend)),
        "the backend keys the record"
    );
    assert_eq!(
        restore(&mut reopened, &pair(), address, backend(), &mut observer),
        Ok(Maybe::Absent(restored::Absent::AddressMismatch)),
        "an address is restored only for its own program"
    );
    assert_eq!(
        observer.invalidated,
        [address, address],
        "each empty restore is observed"
    );
}

#[test]
fn nested_process_local_and_opaque_forms_report_exact_errors()
{
    // Ids past anything the fixture's arena, or the checker's atoms in it,
    // will hold: each resolves in this arena and in no program's.
    let mut foreign = noisy(Noise(64));
    let foreign_value = foreign.value_unit();
    let foreign_unit = foreign.value_unit();
    let foreign_computation = foreign.computation_return(foreign_unit);
    let foreign_value_type = foreign.value_type_unit();
    let foreign_comp_type = foreign.comp_type_returner(foreign_value_type);

    let mut programs: Vec<(Sort, Program)> = Vec::new();
    let mut arena = CoreArena::new();
    let literal = arena.value_literal(integer(Digits("1")));
    let pair = arena.value_tuple(&[literal, foreign_value]);
    programs.push((
        Sort::Value,
        nested(
            arena,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(pair),
        ),
    ));
    let mut arena = CoreArena::new();
    let thunk = arena.value_thunk(foreign_computation);
    programs.push((
        Sort::Computation,
        nested(
            arena,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(thunk),
        ),
    ));
    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[integer_type, foreign_value_type]);
    programs.push((
        Sort::ValueType,
        nested(
            arena,
            Maybe::Present(product),
            Maybe::Absent(body::Absent::Hole),
        ),
    ));
    let mut arena = CoreArena::new();
    let thunk_type = arena.value_type_thunk(foreign_comp_type);
    programs.push((
        Sort::CompType,
        nested(
            arena,
            Maybe::Present(thunk_type),
            Maybe::Absent(body::Absent::Hole),
        ),
    ));

    for (sort, mut program) in programs {
        let refused = Err(CheckpointStoreError::UnsupportedPersistence(
            UnsupportedPersistence::Dangling(sort),
        ));
        assert_eq!(
            address_of(&program),
            refused,
            "no address for a {sort:?} id of another arena"
        );
        let checkpoints = checked(&mut program);
        assert_eq!(
            encode_checkpoints(&checkpoints).map(|_bytes| ()),
            refused.map(|_address| ()),
            "no bytes either"
        );
        let mut memory = MemoryCheckpointStore::default();
        let mut observer = Recording::default();
        assert_eq!(
            persist(
                &mut memory,
                &program,
                backend(),
                &checkpoints,
                &mut observer
            ),
            refused,
            "persisting refuses with the same error"
        );
        assert_eq!(
            memory.record_count(),
            RecordCount::from(0_usize),
            "nothing is stored"
        );
        assert!(observer.stored.is_empty(), "and nothing is observed");
    }
}

#[test]
#[expect(
    clippy::std_instead_of_core,
    reason = "`core::io::ErrorKind` is not stable yet"
)]
fn file_load_distinguishes_not_found_from_other_read_errors()
{
    let scratch = Scratch::new(Label("not-found"));
    let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
    let address = address_of(&pair()).expect("resolved");
    assert_eq!(
        store.load(address, backend()),
        Ok(Maybe::Absent(stored::Absent::NotStored)),
        "a missing record is absent, not an error"
    );
    std::fs::create_dir_all(store.record_path(address)).expect("occupy the record path");
    assert_eq!(
        store.load(address, backend()),
        Err(CheckpointStoreError::Io),
        "a record path that cannot be read is an error"
    );
    for (kind, expected) in [
        (std::io::ErrorKind::NotFound, super::Failure::NotFound),
        (
            std::io::ErrorKind::AlreadyExists,
            super::Failure::AlreadyExists,
        ),
        (std::io::ErrorKind::PermissionDenied, super::Failure::Other),
    ] {
        assert_eq!(
            super::failure_of(&std::io::Error::from(kind)),
            expected,
            "{kind:?} is classified as itself"
        );
    }
}

#[test]
fn file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes()
{
    let scratch = Scratch::new(Label("integrity"));
    let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
    let mut program = pair();
    let address = address_of(&program).expect("resolved");
    store
        .store(address, backend(), &checked(&mut program))
        .expect("stored");
    let path = store.record_path(address);
    let record = std::fs::read(&path).expect("read");
    let elsewhere =
        address_of(&integers(CoreArena::new(), &[(Key("c"), Digits("3"))])).expect("resolved");
    std::fs::write(store.record_path(elsewhere), &record).expect("copy");
    assert_eq!(
        store.load(elsewhere, backend()),
        Err(CheckpointStoreError::Corrupt),
        "a record under another address's name"
    );
    let mut magic = record.clone();
    if let Some(first) = magic.first_mut() {
        *first ^= 0x01_u8;
    }
    let mut version = record.clone();
    if let Some(low) = version.get_mut(8) {
        *low ^= 0x01_u8;
    }
    let mut flipped = record.clone();
    if let Some(last) = flipped.last_mut() {
        *last ^= 0x01_u8;
    }
    let truncated = record.get(.. record.len() - 1).expect("in range").to_vec();
    let mut extended = record;
    extended.push(0_u8);
    for (damaged, what) in [
        (magic, "a broken magic alone"),
        (version, "another version alone"),
        (flipped, "a flipped payload byte"),
        (truncated, "a truncated record"),
        (extended, "a trailing byte"),
    ] {
        std::fs::write(&path, &damaged).expect("damage");
        assert_eq!(
            store.load(address, backend()),
            Err(CheckpointStoreError::Corrupt),
            "{what}"
        );
    }
}

#[test]
fn memory_records_separate_addresses_backends_and_replacements()
{
    let mut program = pair();
    let first = crate::checkpoint::check_program(&mut program, CheckBudget::from(1_usize))
        .expect("first budget checked")
        .checkpoints()
        .clone();
    let second = crate::checkpoint::check_program(&mut program, CheckBudget::from(2_usize))
        .expect("second budget checked")
        .checkpoints()
        .clone();
    let address = address_of(&program).expect("resolved");
    let lower = BackendArtifact([0; 32]);
    let upper = BackendArtifact([u8::MAX; 32]);
    let mut store = MemoryCheckpointStore::default();
    let mut observer = Recording::default();
    assert_eq!(
        restore(&mut store, &program, address, lower, &mut observer),
        Ok(Maybe::Absent(restored::Absent::NotStored))
    );
    assert_eq!(store.store(address, upper, &second), Ok(()));
    assert_eq!(
        store.load(address, lower),
        Ok(Maybe::Absent(stored::Absent::OtherBackend)),
        "the inclusive upper digest is in the address range"
    );
    assert_eq!(store.store(address, lower, &first), Ok(()));
    assert_eq!(
        store.record_count(),
        crate::boundary::RecordCount::from(2_usize)
    );
    assert_eq!(store.load(address, lower), Ok(Maybe::Present(first)));
    assert_eq!(
        store.load(address, upper),
        Ok(Maybe::Present(second.clone()))
    );
    assert_eq!(store.store(address, lower, &second), Ok(()));
    assert_eq!(
        store.record_count(),
        crate::boundary::RecordCount::from(2_usize)
    );
    assert_eq!(
        store.load(address, lower),
        Ok(Maybe::Present(second.clone()))
    );
    assert_eq!(store.load(address, upper), Ok(Maybe::Present(second)));

    let mut empty = integers(CoreArena::new(), &[]);
    let empty_address = address_of(&empty).expect("empty program resolves");
    assert_eq!(
        restore(&mut store, &empty, empty_address, lower, &mut observer),
        Ok(Maybe::Absent(restored::Absent::NotStored)),
        "records at another address do not occupy this range"
    );
    assert_eq!(observer.invalidated, [address, empty_address]);
    assert!(observer.stored.is_empty());
    let empty_set = checked(&mut empty);
    assert_eq!(store.store(empty_address, lower, &empty_set), Ok(()));
    assert_eq!(
        store.load(empty_address, upper),
        Ok(Maybe::Absent(stored::Absent::OtherBackend)),
        "the inclusive lower digest is in its own address range"
    );
    assert_eq!(
        store.load(empty_address, lower),
        Ok(Maybe::Present(empty_set))
    );
    assert_eq!(
        store.record_count(),
        crate::boundary::RecordCount::from(3_usize)
    );
}

#[test]
fn opening_an_existing_file_as_a_directory_fails_without_changing_it()
{
    let scratch = Scratch::new(Label("open-file"));
    std::fs::create_dir_all(scratch.path()).expect("fixture directory");
    let path = scratch.path().join("occupied");
    std::fs::write(&path, b"retained bytes").expect("create occupied file");
    assert_eq!(
        FileCheckpointStore::open(&path),
        Err(CheckpointStoreError::Io)
    );
    assert_eq!(
        std::fs::read(&path).expect("read occupied file"),
        b"retained bytes"
    );
}

#[test]
fn rewriting_the_first_frame_preserves_unequal_length_neighbors()
{
    let bytes = CheckpointBytes::from(vec![8, 1, 2, 3, 1, 2, 4]);
    let pattern = CheckpointBytes::from(vec![1, 2]);
    let grown = rewritten(&bytes, &pattern, &CheckpointBytes::from(vec![9, 10, 11]));
    assert_eq!(grown.as_ref(), &[8, 9, 10, 11, 3, 1, 2, 4]);
    let deleted = rewritten(&bytes, &pattern, &CheckpointBytes::from(Vec::new()));
    assert_eq!(deleted.as_ref(), &[8, 3, 1, 2, 4]);
}

#[test]
fn stores_refuse_capped_levels_without_replacing_records()
{
    let mut level = Level::var(LevelVar::new(LevelVarIndex::from(0_u32)));
    for _ in 0 .. crate::codec::MAX_DECODED_LEVEL_OFFSET {
        level = level.succ().expect("representable level");
    }
    let mut arena = CoreArena::new();
    let universe =
        arena.value_type_universe(gandr_core_term::Sort::Ground(GroundSort::Value), level);
    let mut capped_program = nested(
        arena,
        Maybe::Present(universe),
        Maybe::Absent(body::Absent::Hole),
    );
    let capped = checked(&mut capped_program);
    let mut program = pair();
    let valid = checked(&mut program);
    let address = address_of(&program).expect("resolved address");
    let refusal = CheckpointStoreError::LevelOffsetTooLarge {
        offset: LevelOffset::from(crate::codec::MAX_DECODED_LEVEL_OFFSET),
    };

    let mut memory = MemoryCheckpointStore::default();
    assert_eq!(memory.store(address, backend(), &valid), Ok(()));
    assert_eq!(memory.store(address, backend(), &capped), Err(refusal));
    assert_eq!(
        memory.record_count(),
        crate::boundary::RecordCount::from(1_usize)
    );
    let loaded = memory.load(address, backend()).expect("old memory record");
    assert!(matches!(loaded, Maybe::Present(ref checkpoints) if checkpoints == &valid));

    let scratch = Scratch::new(Label("capped-store"));
    let mut file = FileCheckpointStore::open(scratch.path()).expect("open");
    assert_eq!(file.store(address, backend(), &valid), Ok(()));
    let before = std::fs::read(file.record_path(address)).expect("old file record");
    assert_eq!(file.store(address, backend(), &capped), Err(refusal));
    assert_eq!(
        std::fs::read(file.record_path(address)).expect("retained file record"),
        before
    );
    assert_eq!(scratch.entries(), [address.to_hex()]);
    let loaded = file.load(address, backend()).expect("old file checkpoints");
    assert!(matches!(loaded, Maybe::Present(ref checkpoints) if checkpoints == &valid));
}
