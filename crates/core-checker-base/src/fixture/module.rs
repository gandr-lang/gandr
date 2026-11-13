//! The declarations, calls, literals and answers that the module checker's
//! witnesses build. Its unit tests and the tests that readmit through the
//! bridge read them both.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::fixture::text_literal;
use crate::module::check_module;
use crate::report::ModuleReport;

/// An admission position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct At(pub usize);

/// The declaration at `position`, its origin `position + 100`.
///
/// # Specification
/// - requires: adding the origin offset one hundred does not overflow.
/// - ensures: the fixture position and the distinct origin are retained
///   alongside the supplied signature and body.
/// - panics: the position lies outside the offset domain.
///
/// # Adequacy
/// - hypothesis: L3 — a module with all four declaration shapes observes
///   verdicts and displaced origins, separating a lost half or confusion
///   between admission position and diagnostic origin.
/// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
/// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
#[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| usize::from(ret.constant()) == position.0
            && Some(usize::from(ret.origin())) == position.0.checked_add(100)
            && matches!(ret.content(),&crate::DeclarationContent::Value {signature,body} if signature == declared && body == defined),
    )]
pub fn declaration(
    position: At,
    declared: Maybe<ValueTypeId, signature::Absent>,
    defined: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position.0),
        declared,
        defined,
        OriginToken::from(position.0.checked_add(100).unwrap()),
    )
}

/// No declared type.
pub const UNSIGNED: Maybe<ValueTypeId, signature::Absent> =
    Maybe::Absent(signature::Absent::Unsigned);

/// No body.
pub const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

/// `U (Integer -> F Integer)`, and the identity function of that type.
///
/// # Specification
/// trivial.
pub fn integer_function(arena: &mut CoreArena) -> (ValueTypeId, ValueId)
{
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let argument = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let returned = arena.computation_return(argument);
    let lambda = arena.computation_lambda(returned);
    (function, arena.value_thunk(lambda))
}

/// A call of the constant `callee`, forced, at `argument`.
///
/// # Specification
/// trivial.
pub fn call(
    arena: &mut CoreArena,
    callee: ConstantIndex,
    argument: ValueId,
) -> gandr_core_term::ComputationId
{
    let callee = arena.value_constant(callee);
    let forced = arena.computation_force(callee);
    arena.computation_application(forced, argument)
}

/// The fixture of the literal readers: `word : U(Integer → F String)` reads
/// every natural as the same string, `flag` and `bit : U(Integer → F
/// Character)` are owed, `taker : U(String → F Integer)` and `chooser :
/// U(Character → F Integer)` are owed, and the declaration at 5 is
/// `thunk(callee(n))` at `U(F Integer)`, `n` the literal `written`. The checker
/// keeps `kept` as its readers.
///
/// # Specification
/// trivial.
pub fn read_literal(
    kept: &[gandr_core_term::LiteralReader],
    callee: ConstantIndex,
    written: gandr_kernel_term::Literal,
) -> (CoreArena, ModuleReport, ValueId)
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let boolean = arena.value_type_base(BaseType::Character);
    let thunk_of = |arena: &mut CoreArena, domain, result| {
        let returns = arena.comp_type_returner(result);
        let arrow = arena.comp_type_arrow(domain, returns);
        arena.value_type_thunk(arrow)
    };
    let word_type = thunk_of(&mut arena, integer, text);
    let word = {
        let read = arena.value_literal(text_literal());
        let returned = arena.computation_return(read);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let flag_type = thunk_of(&mut arena, integer, boolean);
    let taker_type = thunk_of(&mut arena, text, integer);
    let chooser_type = thunk_of(&mut arena, boolean, integer);
    let user_type = {
        let returns = arena.comp_type_returner(integer);
        arena.value_type_thunk(returns)
    };
    let literal = arena.value_literal(written);
    let user = {
        let called = call(&mut arena, callee, literal);
        arena.value_thunk(called)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_readers(kept);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(word_type), Maybe::Present(word)),
            declaration(At(1), Maybe::Present(flag_type), HOLE),
            declaration(At(2), Maybe::Present(flag_type), HOLE),
            declaration(At(3), Maybe::Present(taker_type), HOLE),
            declaration(At(4), Maybe::Present(chooser_type), HOLE),
            declaration(At(5), Maybe::Present(user_type), Maybe::Present(user)),
        ])
    };
    (arena, report, literal)
}

/// The natural-literal readers at the positions `at`.
///
/// # Specification
/// trivial.
pub fn naturals(at: &[ConstantIndex]) -> Vec<gandr_core_term::LiteralReader>
{
    at.iter()
        .map(|&by| gandr_core_term::LiteralReader {
            by,
            reads: gandr_core_term::LiteralKind::Natural,
        })
        .collect()
}

/// The answers of `supported`, positions and type ids, in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one position and underlying type-id answer per consultation, in
///   the same order and retaining absence reasons.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — repeated, absent and interrupted consultation reads are
///   compared with exact position/type pairs; the observer exposes wrong order,
///   missing answers or loss of an absence.
/// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
/// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
#[spec(ensures: |ret| ret.iter().copied().eq(supported.support().consulted().iter()
        .map(|entry| (entry.constant(), entry.answer().map(crate::formation::FormedValueType::id)))))]
pub fn answers(
    supported: &crate::support::Supported
) -> Vec<(
    ConstantIndex,
    Maybe<ValueTypeId, crate::context::signature_table::Absent>,
)>
{
    supported
        .support()
        .consulted()
        .iter()
        .map(|consulted| {
            (
                consulted.constant(),
                consulted
                    .answer()
                    .map(crate::formation::FormedValueType::id),
            )
        })
        .collect()
}
