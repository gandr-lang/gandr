//! The toy surface the differential runs over, and the gate every step of it
//! passes.
//!
//! A statement is `def name [: ascription] = body`. Lowering resolves a name
//! lexically — to the latest earlier definition of it — so shadowing is real
//! and a forward or unknown name lowers to a position no item holds. Every
//! statement allocates its own nodes, so equal statements have equal content
//! in any revision.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::Opacity;
use gandr_core_incremental::Program;
use gandr_core_incremental::Resume;
use gandr_core_incremental::Typing;
use gandr_core_incremental::check_program;
use gandr_core_incremental::decode_checkpoints;
use gandr_core_incremental::encode_checkpoints;
use gandr_core_incremental::footprint_of;
use gandr_core_incremental::project;
use gandr_core_incremental::resume;
use gandr_core_term::CoreArena;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use proptest::test_runner::TestCaseError;
use quenchant_shape::shape::Maybe;

/// A statement's body.
///
/// # Specification
/// - executable: none — this syntax declaration is not callable; lowering
///   relates its payloads to arena nodes.
///
/// # Adequacy
/// - hypothesis: L3 — fixed integer boundaries, Unicode text, references, a
///   thunk and a hole have distinct lowered stage representations.
/// - witness: `tests::common::lowering_handles_numeric_and_binding_boundaries`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body
{
    /// An integer literal.
    Int(u64),
    /// A string literal.
    Str(String),
    /// A name.
    Ref(String),
    /// `thunk (return n)`.
    Thunk(u64),
    /// A hole.
    Hole,
}

/// A statement's ascription.
///
/// # Specification
/// - executable: none — this syntax declaration has no invocation; its
///   interpretation is checked at lower.
///
/// # Adequacy
/// - hypothesis: L3 — integer, text, returner and code ascriptions are observed
///   as their exact core formers, including a shadowed code reference.
/// - witness: `tests::common::lowering_handles_numeric_and_binding_boundaries`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ascription
{
    /// `Integer`.
    Integer,
    /// `String`.
    Text,
    /// `U (F Integer)`.
    ReturnsInteger,
    /// `El 0 name`: a type position reading a definition.
    CodeOf(String),
}

/// `def name [: ascription] = body`.
///
/// # Specification
/// - executable: none — the data does not carry the preceding scope; binding
///   and position laws belong to lower.
///
/// # Adequacy
/// - hypothesis: L3 — an earlier shadow and a forward reference separate
///   preceding-scope resolution from final-scope lookup.
/// - witness: `tests::common::lowering_handles_numeric_and_binding_boundaries`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Stmt
{
    /// The definition's name.
    pub name: String,
    /// Its ascription, if any.
    pub ascription: Option<Ascription>,
    /// Its body.
    pub body: Body,
}

/// A fixture name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Name(pub &'static str);

/// `def name = body`.
///
/// # Specification
/// trivial.
pub fn def(
    name: Name,
    body: Body,
) -> Stmt
{
    Stmt {
        name: String::from(name.0),
        ascription: None,
        body,
    }
}

/// `def name : ascription = body`.
///
/// # Specification
/// trivial.
pub fn ascribed(
    name: Name,
    ascription: Ascription,
    body: Body,
) -> Stmt
{
    Stmt {
        name: String::from(name.0),
        ascription: Some(ascription),
        body,
    }
}

/// A reference to `name`.
///
/// # Specification
/// trivial.
pub fn read(name: Name) -> Body
{
    Body::Ref(String::from(name.0))
}

/// A string literal body.
///
/// # Specification
/// trivial.
pub fn text(content: Name) -> Body
{
    Body::Str(String::from(content.0))
}

/// A natural number of a fixture.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Natural(pub u64);

/// The integer literal `value`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the nonnegative integer whose magnitude is exactly `value`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero and the largest u64 lower to their fixed decimal
///   magnitudes. The predicate checks a numeric round trip without formatting a
///   second string.
/// - witness: `tests::common::lowering_handles_numeric_and_binding_boundaries`
#[spec(
    ensures: |ret| matches!(ret, Literal::Integer(ref literal) if literal.sign() == Sign::NonNegative && literal.magnitude().as_ref().parse::<u64>() == Ok(value.0)),
)]
pub fn integer(value: Natural) -> Literal
{
    Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(format!("{}", value.0)).expect("decimal digits"),
    ))
}

/// The program `statements` lower to.
///
/// # Specification
/// - ensures: one item per statement, keyed by its name, at dense positions; a
///   name resolves to the latest earlier statement of it, and an unbound one to
///   the first position past the program.
///
/// # Adequacy
/// - hypothesis: L3 — a fixed seven-statement stage artifact checks integer
///   boundaries, every toy former, forward lookup and shadowing. The predicate
///   covers arity, keys, dense metadata and resolved root presence; it does not
///   run a second lowering.
/// - witness: `tests::common::lowering_handles_numeric_and_binding_boundaries`
#[spec(
    ensures: |ret| {
        ret.items().len() == statements.len()
            && ret.items().iter().zip(statements).enumerate().all(
                |(position, (item, statement))| {
                    let declaration = item.declaration();
                    item.key().as_ref() == statement.name.as_bytes()
                        && usize::from(declaration.constant()) == position
                        && usize::from(declaration.origin()) == position
                        && match declaration.signature() {
                            | Maybe::Present(id) => {
                                statement.ascription.is_some()
                                    && ret.arena().value_type(id).is_some()
                            },
                            | Maybe::Absent(_) => statement.ascription.is_none(),
                        }
                        && match declaration.body() {
                            | Maybe::Present(id) => {
                                !matches!(&statement.body, Body::Hole)
                                    && ret.arena().value(id).is_some()
                            },
                            | Maybe::Absent(_) => matches!(&statement.body, Body::Hole),
                        }
                },
            )
    },
)]
pub fn lower(statements: &[Stmt]) -> Program
{
    let mut arena = CoreArena::new();
    let mut scope: BTreeMap<&str, usize> = BTreeMap::new();
    let unbound = ConstantIndex::from(statements.len());
    let mut items = Vec::with_capacity(statements.len());
    for (position, statement) in statements.iter().enumerate() {
        let resolve = |name: &str| {
            scope
                .get(name)
                .map_or(unbound, |&position| ConstantIndex::from(position))
        };
        let signature = match statement.ascription {
            | None => Maybe::Absent(signature::Absent::Unsigned),
            | Some(Ascription::Integer) => Maybe::Present(arena.value_type_base(BaseType::Integer)),
            | Some(Ascription::Text) => Maybe::Present(arena.value_type_base(BaseType::String)),
            | Some(Ascription::ReturnsInteger) => {
                let integer_type = arena.value_type_base(BaseType::Integer);
                let returner = arena.comp_type_returner(integer_type);
                Maybe::Present(arena.value_type_thunk(returner))
            },
            | Some(Ascription::CodeOf(ref name)) => {
                let code = arena.value_constant(resolve(name));
                Maybe::Present(arena.value_type_element(code, Level::zero()))
            },
        };
        let body = match statement.body {
            | Body::Int(value) => Maybe::Present(arena.value_literal(integer(Natural(value)))),
            | Body::Str(ref content) => Maybe::Present(
                arena.value_literal(Literal::Text(StringLiteral::new(content.clone()))),
            ),
            | Body::Ref(ref name) => Maybe::Present(arena.value_constant(resolve(name))),
            | Body::Thunk(value) => {
                let literal = arena.value_literal(integer(Natural(value)));
                let returned = arena.computation_return(literal);
                Maybe::Present(arena.value_thunk(returned))
            },
            | Body::Hole => Maybe::Absent(body::Absent::Hole),
        };
        items.push(Item::new(
            ItemKey::from(statement.name.as_str()),
            Declaration::new(
                ConstantIndex::from(position),
                signature,
                body,
                OriginToken::from(position),
            ),
        ));
        let _shadowed = scope.insert(&statement.name, position);
    }
    Program::new(arena, items).expect("dense positions ascend")
}

/// The typings the checker's own module entry gives `program` in a fresh
/// context over a copy of its arena, projected.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one projected module-entry typing per item, in source order, at
///   the default budget.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the module entry is the differential oracle for the
///   incremental entry, not an independent checker semantics. The predicate
///   checks arity; generated edits and deliberate stale typing exercise
///   agreement and disagreement.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
#[spec(
    ensures: |ret| ret.len() == program.items().len(),
)]
pub fn batch(program: &Program) -> Vec<Typing>
{
    let mut arena = program.arena().clone();
    let declarations = program.declarations();
    let report = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );
    report
        .judged()
        .iter()
        .enumerate()
        .map(|(index, judged)| {
            project(program, &arena, ItemOrdinal::from(index), &judged.verdict())
        })
        .collect()
}

/// The batch run of `statements` through this crate's own pass.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh default-budget pass with one judged checkpoint per
///   statement in order.
/// - panics: an internal order invariant fails.
///
/// # Adequacy
/// - hypothesis: L2 — generated edit chains begin at this fresh pass and
///   compare with the module entry. The predicate checks budget, source keys,
///   arity and fresh judgement marks.
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
#[spec(
    ensures: |ret| {
        ret.checkpoints().budget() == CheckBudget::DEFAULT
            && ret.checkpoints().items().len() == statements.len()
            && ret.adoptions().len() == statements.len()
            && ret.adoptions().iter().all(|mark| *mark == Adoption::Judged)
            && ret.checkpoints().items().iter().zip(statements).all(
                |(checkpoint, statement)| match *checkpoint.content().reference() {
                    | gandr_core_incremental::Reference::Item { ref key, .. } => {
                        key.as_ref() == statement.name.as_bytes()
                    },
                    | gandr_core_incremental::Reference::Unoccupied => false,
                },
            )
    },
)]
pub fn checked(statements: &[Stmt]) -> Resume
{
    check_program(&mut lower(statements), CheckBudget::DEFAULT).expect("the order builds")
}

/// What one differential step observed.
///
/// # Specification
/// - executable: none — this result declaration is not callable and retains
///   neither the base nor the independent module observation; step checks their
///   relation.
///
/// # Adequacy
/// - hypothesis: L2 — edit chains check the resumed typing. L3 — the precision
///   witness observes one probe for its one adopted reader; this is an
///   instrumentation count, not a timing claim.
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
/// - witness: `tests::incremental::the_precision_probe_examines_real_adoptions`
#[derive(Debug)]
pub struct Step
{
    /// The resume.
    pub resumed: Resume,
    /// How many adoptions the precision probe examined.
    pub probed: ItemCount,
}

/// A differential failure, as a proptest case failure.
///
/// # Specification
/// trivial.
pub fn failure(message: String) -> TestCaseError
{
    TestCaseError::fail(message)
}

/// One differential step: resume `base` onto `edited` and discharge every
/// obligation.
///
/// # Specification
/// - ensures: on success the batch pass equals the checker's module entry,
///   projected; the resume equals both; every adopted item is transparent,
///   carries the footprint of its content, and carries exactly the support a
///   fresh judgement of the edited program records for it — the adoption rule's
///   licence, re-derived outside the pass; and the resumed checkpoints survive
///   the persisted round trip unchanged.
/// - fails: naming the first obligation broken.
///
///
/// # Adequacy
/// - hypothesis: L2 — generated edits compare distinct module and incremental
///   entries while sharing checker semantics. L3 — a forged stale typing must
///   be a failing case, not a discarded case. The predicate checks retained
///   budget, target references, output arities and transparency without
///   repeating checking, footprint derivation or encoding.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
///
/// # Errors
/// A test-case failure naming the broken obligation.
#[spec(
    captures: [budget = base.checkpoints().budget()],
    ensures: |ret| match ret {
        | Ok(ref step) => {
            step.resumed.checkpoints().budget() == budget
                && step.resumed.checkpoints().items().len() == edited.items().len()
                && step.resumed.adoptions().len() == edited.items().len()
                && step.resumed.handles().len() == edited.items().len()
                && step
                    .resumed
                    .checkpoints()
                    .items()
                    .iter()
                    .zip(edited.references())
                    .all(|(checkpoint, reference)| {
                        checkpoint.content().reference() == reference
                    })
                && step
                    .resumed
                    .adoptions()
                    .iter()
                    .zip(step.resumed.checkpoints().items())
                    .all(|(mark, checkpoint)| {
                        *mark != Adoption::Adopted
                            || checkpoint.content().opacity() == Opacity::Transparent
                    })
        },
        | Err(TestCaseError::Fail(_)) => true,
        | Err(TestCaseError::Reject(_)) => false,
    },
)]
pub fn step(
    base: Resume,
    edited: &mut Program,
) -> Result<Step, TestCaseError>
{
    let expected = batch(edited);
    let fresh = check_program(&mut edited.clone(), base.checkpoints().budget())
        .map_err(|error| failure(format!("the batch pass failed: {error}")))?;
    let fresh_typings: Vec<Typing> = fresh.typings().cloned().collect();
    if fresh_typings != expected {
        return Err(failure(format!(
            "the batch pass must equal the checker's module entry\n  pass:   {fresh_typings:?}\n  module: {expected:?}"
        )));
    }
    let resumed =
        resume(base, edited).map_err(|error| failure(format!("the resume failed: {error}")))?;
    let actual: Vec<Typing> = resumed.typings().cloned().collect();
    if actual != expected {
        return Err(failure(format!(
            "incremental must equal batch\n  resumed: {actual:?}\n  batch:   {expected:?}"
        )));
    }
    if resumed.adoptions().len() != actual.len() || resumed.handles().len() != actual.len() {
        return Err(failure(String::from(
            "one adoption mark and one handle per item",
        )));
    }
    let mut probed = 0_usize;
    for (index, &adoption) in resumed.adoptions().iter().enumerate() {
        if adoption == Adoption::Judged {
            continue;
        }
        let (Some(checkpoint), Some(fresh)) = (
            resumed.checkpoints().items().get(index),
            fresh.checkpoints().items().get(index),
        )
        else {
            return Err(failure(format!(
                "the adoption at {index} has no checkpoint"
            )));
        };
        if checkpoint.content().opacity() == Opacity::Opaque {
            return Err(failure(format!("the opaque item at {index} was adopted")));
        }
        if *checkpoint.footprint() != footprint_of(checkpoint.content()) {
            return Err(failure(format!(
                "the adopted item at {index} carries a footprint its content does not have"
            )));
        }
        if checkpoint.support() != fresh.support() {
            return Err(failure(format!(
                "over-adoption at {index}: adopted on support {:?}, a fresh judgement reads {:?}",
                checkpoint.support(),
                fresh.support()
            )));
        }
        probed = probed.saturating_add(1);
    }
    let bytes = encode_checkpoints(resumed.checkpoints())
        .map_err(|error| failure(format!("every toy checkpoint encodes, but: {error}")))?;
    let decoded = decode_checkpoints(&bytes)
        .map_err(|error| failure(format!("canonical bytes decode, but: {error}")))?;
    if decoded != *resumed.checkpoints() {
        return Err(failure(String::from(
            "the persisted round trip must preserve the checkpoints exactly",
        )));
    }
    Ok(Step {
        resumed,
        probed: ItemCount::from(probed),
    })
}

/// The gate over one edit: batch `base`, then step onto `edited`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the successful differential step for `edited`, at the default
///   budget; the returned checkpoints retain its keys and order.
/// - panics: a differential obligation fails.
///
/// # Adequacy
/// - hypothesis: L2 — named edits and generated chains pass through the gate.
///   The predicate checks its output metadata; the stale-typing witness
///   exercises the underlying failure rather than pinning panic text.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
#[spec(
    ensures: |ret| {
        ret.resumed.checkpoints().budget() == CheckBudget::DEFAULT
            && ret.resumed.checkpoints().items().len() == edited.len()
            && ret.resumed.checkpoints().items().iter().zip(edited).all(
                |(checkpoint, statement)| match *checkpoint.content().reference() {
                    | gandr_core_incremental::Reference::Item { ref key, .. } => {
                        key.as_ref() == statement.name.as_bytes()
                    },
                    | gandr_core_incremental::Reference::Unoccupied => false,
                },
            )
    },
)]
pub fn gate(
    base: &[Stmt],
    edited: &[Stmt],
) -> Step
{
    match step(checked(base), &mut lower(edited)) {
        | Ok(step) => step,
        | Err(error) => panic!("the differential step must hold: {error}"),
    }
}

/// A scratch directory's label, unique among the tests.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Label(pub &'static str);

/// A labelled temporary path with best-effort removal on creation and drop.
///
/// # Specification
/// - executable: none — the declaration owns a path, not a file-system
///   snapshot; its constructor and snapshot operation carry the observable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a writable private directory retains two distinct file
///   payloads in its snapshot and is removed on ordinary drop. Cleanup refusal
///   is not injected.
/// - witness: `tests::common::directory_snapshots_order_names_and_retain_bytes`
#[repr(transparent)]
#[derive(Debug)]
pub struct Scratch(PathBuf);

impl Scratch
{
    /// The scratch directory of `label` for this process.
    ///
    /// # Specification
    /// - requires: the label is unique among concurrent fixtures.
    /// - ensures: the temporary path ends in the label; any old directory at
    ///   that path receives a best-effort removal attempt. No directory is
    ///   created.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the snapshot witness creates and uses the returned
    ///   path. The predicate checks the label without querying the file system
    ///   or repeating environment lookup.
    /// - witness: `tests::common::directory_snapshots_order_names_and_retain_bytes`
    #[spec(
        ensures: |ret| {
            ret.0
                .as_os_str()
                .as_encoded_bytes()
                .ends_with(label.0.as_bytes())
        },
    )]
    pub fn new(label: Label) -> Self
    {
        let path = std::env::temp_dir().join(format!(
            "gandr-core-incremental-tests-{}-{}",
            std::process::id(),
            label.0
        ));
        drop(std::fs::remove_dir_all(&path));
        Self(path)
    }

    /// The directory's path.
    ///
    /// # Specification
    /// trivial.
    pub fn path(&self) -> &Path
    {
        &self.0
    }

    /// Every entry's name and bytes, sorted by name.
    ///
    /// # Specification
    /// - requires: the directory and every yielded entry are readable files
    ///   throughout their respective reads.
    /// - ensures: the observed names and bytes, sorted by name; this is not an
    ///   atomic snapshot of concurrent file-system changes.
    /// - panics: a required read fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two deliberately reverse-created names retain their
    ///   exact distinct bytes in name order. The predicate checks ordering
    ///   without rereading external state.
    /// - witness: `tests::common::directory_snapshots_order_names_and_retain_bytes`
    #[spec(
        ensures: |ret| {
            ret.0
                .windows(2)
                .all(|pair| matches!(pair, [left, right] if left.0 <= right.0))
        },
    )]
    pub fn snapshot(&self) -> Snapshot
    {
        let mut entries: Vec<(String, Vec<u8>)> = std::fs::read_dir(&self.0)
            .expect("the scratch directory is readable")
            .map(|entry| {
                let entry = entry.expect("a readable entry");
                (
                    entry.file_name().to_string_lossy().into_owned(),
                    std::fs::read(entry.path()).expect("a readable file"),
                )
            })
            .collect();
        entries.sort();
        Snapshot(entries)
    }
}

/// A scratch directory's entries, name and bytes, sorted by name.
///
/// # Specification
/// - executable: none — this stored observation is not callable; snapshot
///   checks ordering when constructing it.
///
/// # Adequacy
/// - hypothesis: L3 — a two-file semantic golden observes exact names and
///   bytes, not merely entry count.
/// - witness: `tests::common::directory_snapshots_order_names_and_retain_bytes`
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
pub struct Snapshot(Vec<(String, Vec<u8>)>);

impl Drop for Scratch
{
    /// Attempt to remove the directory.
    ///
    /// # Specification
    /// - ensures: removal is attempted; failure is ignored.
    /// - executable: none — file-system removal is fallible and the value is
    ///   being destroyed; no post-drop object can observe the external result.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary drop removes the witness directory and its
    ///   files. Permission changes and concurrent interference are outside this
    ///   witness.
    /// - witness: `tests::common::directory_snapshots_order_names_and_retain_bytes`
    fn drop(&mut self)
    {
        drop(std::fs::remove_dir_all(&self.0));
    }
}

#[test]
fn lowering_handles_numeric_and_binding_boundaries()
{
    let source = [
        ascribed(Name("x"), Ascription::Integer, Body::Int(u64::MAX)),
        def(Name("reader"), read(Name("later"))),
        def(Name("x"), read(Name("x"))),
        def(Name("later"), Body::Int(0)),
        ascribed(
            Name("type-reader"),
            Ascription::CodeOf(String::from("x")),
            Body::Hole,
        ),
        ascribed(Name("text"), Ascription::Text, text(Name("λ\0"))),
        ascribed(Name("thunk"), Ascription::ReturnsInteger, Body::Thunk(7)),
    ];
    let resumed = checked(&source);
    let literal = |digits: &str| {
        gandr_core_incremental::ContentNode::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::from_decimal_text(String::from(digits)).expect("fixed decimal golden"),
        )))
    };
    let expected = [
        vec![
            gandr_core_incremental::ContentNode::Base(BaseType::Integer),
            literal("18446744073709551615"),
        ],
        vec![gandr_core_incremental::ContentNode::Constant(
            gandr_core_incremental::Reference::Unoccupied,
        )],
        vec![gandr_core_incremental::ContentNode::Constant(
            gandr_core_incremental::Reference::Item {
                key: ItemKey::from("x"),
                occurrence: gandr_core_incremental::Occurrence::from(0_usize),
            },
        )],
        vec![literal("0")],
        vec![
            gandr_core_incremental::ContentNode::Element {
                code: gandr_core_incremental::NodeIndex::from(1_usize),
                target: Level::zero(),
            },
            gandr_core_incremental::ContentNode::Constant(
                gandr_core_incremental::Reference::Item {
                    key: ItemKey::from("x"),
                    occurrence: gandr_core_incremental::Occurrence::from(1_usize),
                },
            ),
        ],
        vec![
            gandr_core_incremental::ContentNode::Base(BaseType::String),
            gandr_core_incremental::ContentNode::Literal(Literal::Text(StringLiteral::new(
                String::from("λ\0"),
            ))),
        ],
        vec![
            gandr_core_incremental::ContentNode::ThunkType(
                gandr_core_incremental::NodeIndex::from(2_usize),
            ),
            gandr_core_incremental::ContentNode::Thunk(gandr_core_incremental::NodeIndex::from(
                3_usize,
            )),
            gandr_core_incremental::ContentNode::Returner(gandr_core_incremental::NodeIndex::from(
                4_usize,
            )),
            gandr_core_incremental::ContentNode::Return(gandr_core_incremental::NodeIndex::from(
                5_usize,
            )),
            gandr_core_incremental::ContentNode::Base(BaseType::Integer),
            literal("7"),
        ],
    ];
    assert_eq!(resumed.checkpoints().items().len(), expected.len());
    for (checkpoint, expected) in resumed.checkpoints().items().iter().zip(expected) {
        assert_eq!(checkpoint.content().nodes(), expected.as_slice());
    }
}

#[test]
fn directory_snapshots_order_names_and_retain_bytes()
{
    let scratch = Scratch::new(Label("snapshot-order"));
    std::fs::create_dir_all(scratch.path()).expect("create fixture directory");
    std::fs::write(scratch.path().join("zeta"), b"second\0").expect("write zeta");
    std::fs::write(scratch.path().join("alpha"), b"\0first").expect("write alpha");
    assert_eq!(
        scratch.snapshot(),
        Snapshot(vec![
            (String::from("alpha"), b"\0first".to_vec()),
            (String::from("zeta"), b"second\0".to_vec()),
        ])
    );
    let path = scratch.path().to_path_buf();
    drop(scratch);
    assert!(
        !path.exists(),
        "ordinary drop removes the fixture directory"
    );
}
