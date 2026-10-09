//! Test fixtures: synthetic modules, parsed, lowered and checked from source
//! text.
//!
//! A fixture runs the composition a driver runs — parse, lower, adapt the
//! lowering's declarations to the checker's input, check — so a witness
//! settles exactly what a real run hands this crate.

use alloc::format;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::AttributeRegistry;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::RegisteredAttribute;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::report::SettleReport;
use crate::root::CorpusRoot;
use crate::run::RunSpelling;
use crate::settle::settle;

/// A module lowered and checked, beside the arena both wrote into.
pub struct Checked<'source>
{
    /// The arena the lowering minted into and the checker read.
    pub arena: CoreArena,
    /// The lowered module.
    pub module: LoweredModule<'source>,
    /// The checker's report for the module.
    pub verdicts: ModuleReport,
}

/// Parse, lower and check `source`, which the parser must accept cleanly and
/// the lowering must not refuse as a whole.
///
/// # Specification
/// trivial.
pub fn checked(source: SourceText<'_>) -> Checked<'_>
{
    let pbg = built_in().expect("the built-in grammar builds");
    let parsed = parse(&pbg, source).expect("the parser reads the source");
    assert!(
        bool::from(parsed.is_clean()),
        "the fixture source is one the parser accepts without repair"
    );
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(
        &pbg,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .expect("the lowering reads the module");
    let declarations = declarations(&module);
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );

    Checked {
        arena,
        module,
        verdicts,
    }
}

/// The checker's input for `module`: every declaration the lowering did not
/// refuse, in admission order, its origin carried through.
///
/// # Specification
/// trivial.
pub fn declarations(module: &LoweredModule<'_>) -> Vec<Declaration>
{
    module
        .declarations()
        .iter()
        .filter_map(|lowered| {
            let (declared, defined) = match lowered.outcome() {
                | DeclarationOutcome::Completed {
                    declared_type,
                    body: value,
                } => (Maybe::Present(declared_type), Maybe::Present(value)),
                | DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                | DeclarationOutcome::Bodied { body: value } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(value),
                ),
                | DeclarationOutcome::Refused(_) => return None,
            };
            let origin = OriginToken::from(usize::from(lowered.origin()));
            Some(Declaration::new(
                lowered.constant(),
                declared,
                defined,
                origin,
            ))
        })
        .collect()
}

/// The settle report for `source` under `root`, over its own verdicts, each
/// run outcome asked for spelled by [`ran_at`].
///
/// # Specification
/// trivial.
pub fn settled(
    root: CorpusRoot,
    source: SourceText<'_>,
) -> SettleReport<'_>
{
    let checked = checked(source);
    settle(
        root,
        &checked.arena,
        &checked.module,
        &checked.verdicts,
        &mut ran_at,
    )
    .expect("the verdicts are the module's own")
}

/// The outcome the test runner spells for the declaration at `constant`:
/// `ran at n`, so a comparison shows which declaration was run.
///
/// # Specification
/// trivial.
pub fn ran_at(constant: ConstantIndex) -> RunSpelling
{
    RunSpelling::from(format!("ran at {}", usize::from(constant)))
}

/// The span from `start` to `end`.
///
/// # Specification
/// trivial.
pub fn span(
    start: ByteOffset,
    end: ByteOffset,
) -> ByteSpan
{
    ByteSpan::new(start, end).expect("the fixture span is ordered")
}

/// The empty span at the start of a source.
///
/// # Specification
/// trivial.
pub fn empty_span() -> ByteSpan
{
    span(ByteOffset::from(0_usize), ByteOffset::from(0_usize))
}

/// The registry entry `name` spells, which must be registered.
///
/// # Specification
/// trivial.
pub fn registered(name: SurfaceName<'_>) -> RegisteredAttribute
{
    let Maybe::Present((entry, _schema)) = AttributeRegistry::lookup(name)
    else {
        panic!("the fixture names a registered attribute");
    };

    entry
}
