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
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ascription
{
    /// `Integer`.
    Integer,
    /// `String`.
    Text,
    /// `U (F Integer)`.
    ReturnsInteger,
    /// `El 0 name`: a type position reading a definition, outside the
    /// checker's fragment today and inside the adoption rule's reach.
    CodeOf(String),
}

/// `def name [: ascription] = body`.
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
/// trivial.
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
/// trivial.
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
/// trivial.
pub fn checked(statements: &[Stmt]) -> Resume
{
    check_program(&mut lower(statements), CheckBudget::DEFAULT).expect("the order builds")
}

/// What one differential step observed.
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
/// # Errors
/// A test-case failure naming the broken obligation.
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
/// trivial.
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

/// A directory under the system temporary directory, emptied on creation and
/// removed on drop.
#[repr(transparent)]
#[derive(Debug)]
pub struct Scratch(PathBuf);

impl Scratch
{
    /// The scratch directory of `label` for this process.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
pub struct Snapshot(Vec<(String, Vec<u8>)>);

impl Drop for Scratch
{
    /// Remove the directory.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        drop(std::fs::remove_dir_all(&self.0));
    }
}
