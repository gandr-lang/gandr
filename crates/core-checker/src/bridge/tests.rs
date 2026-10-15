#[test]
fn native_operations_cross_as_audited_assumptions()
{
    use gandr_core_term::primitive::Arguments;
    use gandr_core_term::primitive::PRELUDE;
    let mut arena = CoreArena::new();
    let sub = PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "sub")
        .unwrap();
    let function = sub.thunk(&mut arena);
    let function_type = sub.declared_type(&mut arena);
    let function_type = arena.value_type_thunk(function_type);
    let zero = arena.value_literal(integer_literal());
    let saturated = arena.computation_primitive(sub, Arguments::Binary([zero, zero]));
    let result = arena.value_thunk(saturated);
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let result_type = arena.value_type_thunk(returns);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(function_type),
            Maybe::Present(function),
        ),
        declaration(At(1), Maybe::Present(result_type), Maybe::Present(result)),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. }))
    );
    assert_eq!(readmission.audit().axioms(), &[ConstantIndex::from(
        0_usize
    )]);
    assert!(readmission.audit().unchecked_admissions().is_empty());
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let native = artifact.declarations().first().unwrap().declaration();
    assert!(matches!(native.content(), DeclarationContent::Axiom { .. }));
    assert_eq!(
        native
            .name()
            .segments()
            .iter()
            .map(AsRef::as_ref)
            .collect::<Vec<&str>>(),
        ["sub"]
    );
    assert_eq!(
        crossed_at(&readmission, At(0)),
        ConstantIndex::from(1_usize)
    );
    assert_eq!(
        crossed_at(&readmission, At(1)),
        ConstantIndex::from(2_usize)
    );
}

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::TraceNode;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::Sort;
use gandr_core_term::SortParameter;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayRefusal;
use gandr_kernel_core::TracePosition;
use gandr_kernel_core::content_digest;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::NameSegment;
use gandr_kernel_term::Side;
use gandr_kernel_term::StructuredName;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value as KernelValue;
use gandr_kernel_term::ValueType as KernelValueType;
use gandr_kernel_term::decode;
use proptest::prelude::ProptestConfig;
use proptest::prelude::prop_assert;
use proptest::prelude::prop_assert_eq;
use proptest::prelude::proptest;
use proptest::test_runner::TestCaseError;
use quenchant_shape::shape::Maybe;

use super::Erasure;
use super::Frame;
use super::Mode as Reading;
use super::Outcome;
use super::Positions;
use super::Readmission;
use super::Readmitted;
use super::Refusal;
use super::Replayed;
use super::Source;
use super::fault;
use super::readmit;
use super::readmit_with;
use crate::code::Lift;
use crate::code::Unfolded;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::fixture::Mode;
use crate::fixture::Typing;
use crate::fixture::dangling_value;
use crate::fixture::dangling_value_type;
use crate::fixture::function_recipe;
use crate::fixture::integer_literal;
use crate::fixture::numeric_literal;
use crate::fixture::seed;
use crate::fixture::term_recipe;
use crate::fixture::text_literal;
use crate::fixture::typed_recipe;
use crate::judgement::synthesise_comp;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::StaticArity;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;

/// A module position in a fixture.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// The origin a fixture gives the declaration at `position`: the position
/// plus one hundred, so an origin is never mistaken for a position.
///
/// # Specification
/// - requires: the position plus one hundred fits in `usize`.
/// - ensures: that sum, preserving the distinction from a module position.
/// - panics: the sum overflows.
///
/// # Adequacy
/// - hypothesis: L1 over bounded generated modules observes each exact
///   declaration origin after readmission; replacing the offset with a module
///   position or dropping the origin changes the per-declaration comparison.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
#[spec(requires: position.0.checked_add(100).is_some(), ensures: |ret| position.0.checked_add(100) == Some(usize::from(ret)))]
fn origin(position: At) -> OriginToken
{
    OriginToken::from(position.0.checked_add(100).unwrap())
}

/// The declaration at `position` with these halves.
///
/// # Specification
/// - requires: the position plus one hundred fits in `usize`.
/// - ensures: the supplied halves, position and offset origin.
/// - panics: the origin offset overflows.
///
/// # Adequacy
/// - hypothesis: L1 over bounded generated typed and free terms observes each
///   declaration outcome, hole and origin; dropping a half or confusing source
///   and kernel positions changes the independent admission checks.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
#[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| ret.constant() == ConstantIndex::from(position.0)
            && matches!(ret.content(), &crate::DeclarationContent::Value {signature,body} if signature == declared && body == defined)
            && position.0.checked_add(100) == Some(usize::from(ret.origin())),
    )]
fn declaration(
    position: At,
    declared: Maybe<ValueTypeId, signature::Absent>,
    defined: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position.0),
        declared,
        defined,
        origin(position),
    )
}

/// No declared type.
const UNSIGNED: Maybe<ValueTypeId, signature::Absent> = Maybe::Absent(signature::Absent::Unsigned);

/// No body.
const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

/// Judge `module` over `arena`, then readmit what the judgement accepted.
///
/// # Specification
/// - requires: the module's ids belong to the supplied arena.
/// - ensures: one judgement and one located readmission per declaration.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 over bounded typed and free-term modules compares judgement
///   and readmission outcomes, origins and owed axioms; losing or reordering
///   declarations changes the per-entry oracle.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
#[spec(ensures: |ret| ret.0.judged().len() == module.len() && ret.1.readmitted().len() == module.len()
        && ret.1.readmitted().iter().zip(module).all(|(entry,source)| entry.constant() == source.constant() && entry.origin() == source.origin()))]
fn judge_and_readmit(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> (ModuleReport, Readmission)
{
    let report = {
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        check_module(&mut context, module)
    };
    let readmission = readmit(arena, &report);
    (report, readmission)
}

/// Erase `root` from `arena` into a fresh kernel arena, with no module
/// declaration crossed.
///
/// # Specification
/// - requires: nothing; absent or cyclic nodes are refused.
/// - ensures: a successful image belongs to the returned fresh arena and to the
///   root's family; no constant has a crossed declaration.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite former tables, missing ids and back-edges observe
///   exact target nodes and refusals; dropping the arena or selecting a
///   different node family changes these observations.
/// - witness: `bridge::tests::returning_a_literal_lowers`
/// - witness: `bridge::tests::returner_type_lowers`
/// - witness: `bridge::tests::every_recursive_node_family_refuses_a_back_edge`
#[spec(ensures: |ret| match ret.1 {
        | Ok(AnyNode::Value(at)) => matches!(root, CoreNode::Term(TermNode::Value(_))) && ret.0.value(at).is_some(),
        | Ok(AnyNode::Computation(at)) => matches!(root, CoreNode::Term(TermNode::Computation(_))) && ret.0.computation(at).is_some(),
        | Ok(AnyNode::ValueType(at)) => matches!(root, CoreNode::Type(TypeNode::Value(_))) && ret.0.value_type(at).is_some(),
        | Ok(AnyNode::CompType(at)) => matches!(root, CoreNode::Type(TypeNode::Computation(_))) && ret.0.comp_type(at).is_some(),
        | Err(_) => true,
    })]
fn erase(
    arena: &mut CoreArena,
    root: CoreNode,
) -> (TermArena, Result<AnyNode, Refusal>)
{
    let positions = Positions::default();
    let lifts = alloc::collections::BTreeMap::new();
    let definitions = alloc::collections::BTreeMap::new();
    let mut target = TermArena::new();
    let source = Source {
        lifts: &lifts,
        funexts: &BTreeMap::new(),
        equivalences: &BTreeMap::new(),
        flows: &BTreeMap::new(),
        directed: &BTreeMap::new(),
        reflexivities: &BTreeMap::new(),
        relations: &BTreeMap::new(),
        laws: &BTreeMap::new(),
        natives: &BTreeMap::new(),
        definitions: &definitions,
    };
    let image = Erasure::new(arena, source, &positions, ConstantIndex::from(0_usize))
        .erase(&mut target, root);
    (target, image)
}

/// What each certificate `entry` replayed unfolded, beside its verdict.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every recorded unfolding and verdict, in certificate order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — defined codes and two instances of one static definition
///   expose exact replay sequences; omission, reversal or verdict substitution
///   changes those certificate observations.
/// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
/// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
#[spec(ensures: |ret| ret.len() == entry.certificates().len() && ret.iter().zip(entry.certificates()).all(|(pair,replay)| *pair == (replay.unfolded(),replay.verdict())))]
fn steps(entry: &Readmitted) -> Vec<(Unfolded, KernelVerdict)>
{
    entry
        .certificates()
        .iter()
        .map(|replayed| (replayed.unfolded(), replayed.verdict()))
        .collect()
}

/// A convertible replay of the definition at `position`.
///
/// # Specification
/// trivial.
fn convertible(position: At) -> (Unfolded, KernelVerdict)
{
    (
        Unfolded::Definition(ConstantIndex::from(position.0)),
        KernelVerdict::Convertible,
    )
}

/// The kernel position the entry at `position` crossed at.
///
/// # Specification
/// - requires: the indexed entry exists and crossed as a definition or axiom.
/// - ensures: its admitted kernel position, not its module position.
/// - panics: the entry is absent or did not cross.
///
/// # Adequacy
/// - hypothesis: L3 — marked entries before crossed ones separate module from
///   kernel positions; exact references in the decoded artifact expose using
///   the wrong coordinate or choosing another receipt.
/// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
/// - witness: `bridge::tests::an_export_names_each_crossed_declaration_at_its_position`
#[spec(
        requires: readmission.readmitted().get(position.0).is_some_and(|entry| matches!(entry.outcome(), Outcome::Defined { .. } | Outcome::Assumed { .. } | Outcome::Data { .. })),
        ensures: |ret| readmission.readmitted().get(position.0).is_some_and(|entry| match *entry.outcome() {
            | Outcome::Defined { admitted, .. } | Outcome::Assumed { admitted, .. } | Outcome::Data { admitted, .. } => ret == admitted.position(),
            | _ => false,
        }),
    )]
fn crossed_at(
    readmission: &Readmission,
    position: At,
) -> ConstantIndex
{
    match *readmission.readmitted()[position.0].outcome() {
        Outcome::Defined { admitted, .. }
        | Outcome::Assumed { admitted, .. }
        | Outcome::Data { admitted, .. } => admitted.position(),
        Outcome::Marked(_) | Outcome::Static | Outcome::Refused(_) | Outcome::Rejected(_) => {
            panic!("the declaration at this position crosses")
        },
    }
}

/// Every declaration `report` accepted crossed and every refused one is
/// marked with its refusal, each at its declaration's origin; every owed
/// hole, and nothing else, crossed as an axiom; and the artifact rests on
/// exactly those axioms, so its audit is empty exactly when the ledger is.
///
/// # Specification
/// - requires: the report and readmission concern the same module.
/// - ensures: success only when every acceptance, refusal, origin and owed
///   axiom agrees, with no unchecked admission.
/// - fails: an assertion reports the first differing observation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 over bounded typed, free, function and universe modules
///   compares all located outcomes and axioms against judgement; missing,
///   reordered or misclassified readmissions differ. Static-only declarations
///   are outside this helper's accepted-module domain.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `bridge::tests::every_checked_function_definition_is_readmitted`
/// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
#[spec(ensures: |ret| ret.is_err() || (readmission.readmitted().len() == report.judged().len()
        && readmission.readmitted().iter().zip(report.judged()).all(|(entry,judged)| entry.constant() == judged.constant() && entry.origin() == judged.origin())
        && readmission.audit().unchecked_admissions().is_empty()
        && readmission.audit().axioms().is_empty() == report.ledger().entries().is_empty()))]
fn assert_crossed(
    report: &ModuleReport,
    readmission: &Readmission,
) -> Result<(), TestCaseError>
{
    prop_assert_eq!(
        readmission.readmitted().len(),
        report.judged().len(),
        "one outcome per judged declaration"
    );
    for (judged, readmitted) in report.judged().iter().zip(readmission.readmitted()) {
        prop_assert_eq!(
            (readmitted.constant(), readmitted.origin()),
            (judged.constant(), judged.origin()),
            "each outcome is located at its declaration"
        );
        prop_assert!(
            matches!(
                (judged.verdict(), readmitted.outcome()),
                (
                    Verdict::Checked { .. } | Verdict::Synthesised { .. },
                    &Outcome::Defined { .. }
                ) | (Verdict::Owed(_), &Outcome::Assumed { .. })
                    | (Verdict::Refused(_), &Outcome::Marked(_))
            ),
            "{:?} crossed as {:?}",
            judged.verdict(),
            readmitted.outcome()
        );
        if let (Verdict::Refused(refusal), &Outcome::Marked(mark)) =
            (judged.verdict(), readmitted.outcome())
        {
            prop_assert_eq!(mark, refusal, "the mark is the judgement's refusal");
        }
    }
    let owed: Vec<_> = report
        .ledger()
        .entries()
        .iter()
        .map(|entry| entry.absence().constant())
        .collect();
    let mut assumed = Vec::new();
    let mut axioms = Vec::new();
    for entry in readmission.readmitted() {
        if let Outcome::Assumed { admitted, .. } = *entry.outcome() {
            assumed.push(entry.constant());
            axioms.push(admitted.position());
        }
    }
    prop_assert_eq!(
        &assumed,
        &owed,
        "every owed hole crossed as an axiom, in ledger order, and nothing else did"
    );
    prop_assert_eq!(
        readmission.audit().axioms(),
        axioms.as_slice(),
        "the artifact rests on exactly the axioms the owed holes became"
    );
    prop_assert_eq!(
        readmission.audit().axioms().is_empty(),
        report.ledger().entries().is_empty(),
        "the artifact's audit is empty exactly when the ledger is"
    );
    prop_assert!(
        readmission.audit().unchecked_admissions().is_empty(),
        "the bridge admits nothing unchecked"
    );
    Ok(())
}

#[test]
fn returning_a_literal_lowers()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let (target, image) = erase(&mut arena, CoreNode::Term(TermNode::Computation(returned)));
    let Ok(AnyNode::Computation(image)) = image
    else {
        panic!("a returned literal erases to a computation");
    };
    let Some(&gandr_kernel_term::Computation::Return(value)) = target.computation(image)
    else {
        panic!("the image is a return");
    };
    assert_eq!(
        target.value(value),
        Some(&gandr_kernel_term::Value::Literal(integer_literal())),
        "the literal carries over unchanged"
    );
}

#[test]
fn returner_type_lowers()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer);
    let (target, image) = erase(&mut arena, CoreNode::Type(TypeNode::Computation(returner)));
    let Ok(AnyNode::CompType(image)) = image
    else {
        panic!("a returner erases to a computation type");
    };
    let Some(&gandr_kernel_term::CompType::Returner(result)) = target.comp_type(image)
    else {
        panic!("the image is a returner");
    };
    assert_eq!(
        target.value_type(result),
        Some(&gandr_kernel_term::ValueType::Base(BaseType::Integer)),
        "F Integer erases to the kernel's F Integer"
    );
}

#[test]
fn a_bound_variable_resolves_to_a_de_bruijn_index()
{
    let mut arena = CoreArena::new();
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let (target, image) = erase(&mut arena, CoreNode::Term(TermNode::Computation(lambda)));
    let Ok(AnyNode::Computation(image)) = image
    else {
        panic!("a lambda erases to a computation");
    };
    let Some(&gandr_kernel_term::Computation::Lambda(body)) = target.computation(image)
    else {
        panic!("the image is a lambda");
    };
    let Some(&gandr_kernel_term::Computation::Return(value)) = target.computation(body)
    else {
        panic!("the lambda's body is a return");
    };
    assert_eq!(
        target.value(value),
        Some(&gandr_kernel_term::Value::Variable(DeBruijnIndex::from(
            0_u32
        ))),
        "the bound variable keeps its de Bruijn index"
    );
}

#[test]
fn a_lowered_value_definition_admits()
{
    // def answer : Integer = 0 ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(
        At(0),
        Maybe::Present(integer),
        Maybe::Present(zero),
    )]);
    let [ref answer] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    let Outcome::Defined {
        admitted,
        ref audit,
    } = *answer.outcome()
    else {
        panic!("the definition crosses");
    };
    assert_eq!(
        admitted.position(),
        ConstantIndex::from(0_usize),
        "the first crossing takes the first kernel position"
    );
    assert!(
        audit.axioms().is_empty() && audit.unchecked_admissions().is_empty(),
        "a closed definition rests on nothing"
    );
}

#[test]
fn a_lowered_computation_definition_admits()
{
    // def greet : U (F String) = thunk { return "" } ;
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let returns_string = arena.comp_type_returner(string);
    let suspended = arena.value_type_thunk(returns_string);
    let text = arena.value_literal(text_literal());
    let returned = arena.computation_return(text);
    let thunk = arena.value_thunk(returned);
    let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(
        At(0),
        Maybe::Present(suspended),
        Maybe::Present(thunk),
    )]);
    assert!(
        matches!(
            *readmission.readmitted()[0].outcome(),
            Outcome::Defined { .. }
        ),
        "a computation declared as a thunk crosses as a value definition"
    );
}

#[test]
fn a_constant_reference_across_declarations_admits()
{
    // def first : Unit = () ; def second : Unit = first ;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let first = arena.value_constant(ConstantIndex::from(0_usize));
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(unit_type), Maybe::Present(unit)),
        declaration(At(1), Maybe::Present(unit_type), Maybe::Present(first)),
    ]);
    let Outcome::Defined {
        admitted,
        ref audit,
    } = *readmission.readmitted()[1].outcome()
    else {
        panic!("the referring definition crosses");
    };
    assert_eq!(
        admitted.position(),
        ConstantIndex::from(1_usize),
        "the second declaration takes the second kernel position"
    );
    assert!(
        audit.axioms().is_empty(),
        "resting on a definition rests on no axiom"
    );
}

#[test]
fn hole_unknown_class_rejects_exactly()
{
    // def hole ;
    //
    // A declaration hole with no signature has no type to assume; a term
    // hole written as a body is the other member of the class.
    let mut arena = CoreArena::new();
    let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(At(0), UNSIGNED, HOLE)]);
    let [ref hole] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert_eq!(
        (hole.origin(), hole.outcome()),
        (
            origin(At(0)),
            &Outcome::Marked(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Hole(ConstantIndex::from(0_usize)),
            })
        ),
        "a hole with no type to owe is refused naming the hole, at its origin"
    );
    assert!(
        readmission.environment().entries().is_empty(),
        "no axiom stands in for a hole with no type"
    );
}

#[test]
fn a_sorted_universe_readmits_at_its_level()
{
    // def small : Type[+, 1] = Type ;
    // def number : Type = Integer ;
    // def action : Type[-, 0] = F Integer ;
    let mut arena = CoreArena::new();
    let one = Level::constant(LevelConstant::from(1_u64));
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let negative = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let small_code = arena.value_quote(small);
    let number_code = arena.value_quote(integer);
    let action_code = arena.value_quote_computation(returns_integer);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(large), Maybe::Present(small_code)),
        declaration(At(1), Maybe::Present(small), Maybe::Present(number_code)),
        declaration(At(2), Maybe::Present(negative), Maybe::Present(action_code)),
    ]);
    let expected = [
        (GroundSort::Value, one),
        (GroundSort::Value, Level::zero()),
        (GroundSort::Computation, Level::zero()),
    ];
    for (position, (sort, level)) in expected.into_iter().enumerate() {
        let admitted = crossed_at(&readmission, At(position));
        let entry = &readmission.environment().entries()[usize::from(admitted)];
        assert_eq!(
            readmission
                .environment()
                .arena()
                .value_type(entry.declared_id()),
            Some(&KernelValueType::Universe { sort, level }),
            "each code is admitted at the universe of its sort and level"
        );
    }
}

#[test]
fn a_smaller_type_at_a_larger_universe_readmits_with_a_lift()
{
    // def big : Type[+, 1] = Integer ;
    // def give : U (F Type[+, 1]) = thunk { return Integer } ;
    //
    // The kernel has no cumulativity, so each crossing admits only with the
    // lift the judgement recorded written where it stands.
    let mut arena = CoreArena::new();
    let one = Level::constant(LevelConstant::from(1_u64));
    let integer = arena.value_type_base(BaseType::Integer);
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let returns_large = arena.comp_type_returner(large);
    let suspended = arena.value_type_thunk(returns_large);
    let code = arena.value_quote(integer);
    let returned_code = arena.value_quote(integer);
    let returned = arena.computation_return(returned_code);
    let thunk = arena.value_thunk(returned);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(large), Maybe::Present(code)),
        declaration(At(1), Maybe::Present(suspended), Maybe::Present(thunk)),
    ]);
    let lift = Lift::new(Level::zero(), one);
    assert_eq!(
        (
            report.lifts().get(&code),
            report.lifts().get(&returned_code)
        ),
        (Some(&lift), Some(&lift)),
        "the judgement records the lift at both crossings"
    );
    for entry in readmission.readmitted() {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "{:?} is admitted with its lift",
            entry.outcome()
        );
    }
}

#[test]
fn a_code_constant_unfolds_in_conversion_and_its_trace_replays()
{
    // def Num : Type = Integer ; def Alias : Type = Num ;
    // def n : Num = 0 ; def m : Alias = 0 ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_quote(integer);
    let num = arena.value_constant(ConstantIndex::from(0_usize));
    let alias = arena.value_constant(ConstantIndex::from(1_usize));
    let decoded_num = arena.value_type_element(num, Level::zero());
    let decoded_alias = arena.value_type_element(alias, Level::zero());
    let zero = arena.value_literal(integer_literal());
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(small), Maybe::Present(code)),
        declaration(At(1), Maybe::Present(small), Maybe::Present(num)),
        declaration(At(2), Maybe::Present(decoded_num), Maybe::Present(zero)),
        declaration(At(3), Maybe::Present(decoded_alias), Maybe::Present(zero)),
    ]);
    for judged in report.judged() {
        assert!(
            matches!(judged.verdict(), Verdict::Checked { .. }),
            "the decode converts with the integer atom by unfolding: {:?}",
            judged.verdict()
        );
    }
    assert_eq!(
        steps(&readmission.readmitted()[2]),
        [convertible(At(0))],
        "the kernel replays the one unfolding the erasure of `Num` took"
    );
    assert_eq!(
        steps(&readmission.readmitted()[3]),
        [convertible(At(1)), convertible(At(0))],
        "a chain unfolds one certificate per constant, outermost first"
    );
    for entry in readmission.readmitted() {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "{:?} is admitted",
            entry.outcome()
        );
    }
}

/// A run's certificate keeps a code constant it is handed as the constant:
/// the trace unfolds `Num` inside the call, so the redex crosses with `Num`
/// as written and the kernel replays the unfolding there.
#[test]
fn a_code_constant_argument_crosses_as_written_in_a_run()
{
    // def Num : Type = Integer ; def id : U (Type -> F Type) = λx. return x ;
    // def n : El(id(Num)) = 0 ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_quote(integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = arena.computation_return(bound);
    let body = arena.computation_lambda(body);
    let identity = arena.value_thunk(body);
    let returns = arena.comp_type_returner(small);
    let arrow = arena.comp_type_arrow(small, returns);
    let arrow = arena.value_type_thunk(arrow);
    let num = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(head);
    let applied = arena.computation_application(forced, num);
    let call = arena.value_returned(applied);
    let decoded = arena.value_type_element(call, Level::zero());
    let zero = arena.value_literal(integer_literal());
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(small), Maybe::Present(code)),
        declaration(At(1), Maybe::Present(arrow), Maybe::Present(identity)),
        declaration(At(2), Maybe::Present(decoded), Maybe::Present(zero)),
    ]);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "`id(Num)` runs to the integer quote: {:?}",
        report.judged()[2].verdict()
    );
    let entry = &readmission.readmitted()[2];
    assert!(
        matches!(entry.outcome(), Outcome::Defined { .. }),
        "the kernel replays the run with `Num` where the trace unfolds it: {:?}",
        entry.outcome()
    );
    assert_eq!(steps(entry), [(
        Unfolded::Returned(call),
        KernelVerdict::Convertible
    )]);
}

/// Products, sums, tuples, injections and cases of any arity cross into
/// the kernel as the one n-ary former each is, and the kernel admits
/// them: a triple, an injection into the last of three summands, a case
/// of three branches and the empty sum's case of none.
#[test]
fn n_ary_formers_cross_the_kernel_at_their_arity()
{
    // def t : Integer * String * Unit = (0, "a", unit) ;
    // def i : Integer + String + Unit = Inj2(unit) ;
    // def p : U (Integer + String + Unit -> F Integer) =
    //     thunk λ. case x { y => return y ; _ => return 0 ; _ => return 0 } ;
    // def v : U (Void -> F Integer) = thunk λ. case x {} ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit_type = arena.value_type_unit();
    let triple_type = arena.value_type_product(&[integer, string, unit_type]);
    let three = arena.value_type_sum(&[integer, string, unit_type]);
    let void = arena.value_type_sum(&[]);
    let returns_integer = arena.comp_type_returner(integer);
    let picks = arena.comp_type_arrow(three, returns_integer);
    let picks = arena.value_type_thunk(picks);
    let absurd_type = arena.comp_type_arrow(void, returns_integer);
    let absurd_type = arena.value_type_thunk(absurd_type);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let unit = arena.value_unit();
    let triple = arena.value_tuple(&[zero, text, unit]);
    let injected = arena.value_injection(gandr_core_term::Summand::from(2_usize), unit);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let payload = arena.computation_return(bound);
    let constant = arena.computation_return(zero);
    let case = arena.computation_case(bound, &[payload, constant, constant]);
    let pick = arena.computation_lambda(case);
    let pick = arena.value_thunk(pick);
    let absurd = arena.computation_case(bound, &[]);
    let absurd = arena.computation_lambda(absurd);
    let absurd = arena.value_thunk(absurd);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(triple_type), Maybe::Present(triple)),
        declaration(At(1), Maybe::Present(three), Maybe::Present(injected)),
        declaration(At(2), Maybe::Present(picks), Maybe::Present(pick)),
        declaration(At(3), Maybe::Present(absurd_type), Maybe::Present(absurd)),
    ]);
    for judged in report.judged() {
        assert!(
            matches!(judged.verdict(), Verdict::Checked { .. }),
            "the n-ary former checks in the core: {:?}",
            judged.verdict()
        );
    }
    assert_eq!(readmission.readmitted().len(), 4);
    for entry in readmission.readmitted() {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "the kernel admits the n-ary former: {:?}",
            entry.outcome()
        );
    }
}

#[test]
fn a_code_constant_argument_unfolds_at_export()
{
    // def Num : Type = Integer ; def n : Num = 0 ;
    // def id : U ((a : Type) -> El a -> F (El a)) = thunk λ λ. return x ;
    // def k : U (F Num) = thunk ((force id) Num) n ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_quote(integer);
    let num = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded_num = arena.value_type_element(num, Level::zero());
    let zero = arena.value_literal(integer_literal());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let returns_element = arena.comp_type_returner(element);
    let arrow = arena.comp_type_arrow(element, returns_element);
    let polymorphic = arena.comp_type_pi(small, arrow);
    let identity_type = arena.value_type_thunk(polymorphic);
    let returned = arena.computation_return(bound);
    let inner = arena.computation_lambda(returned);
    let outer = arena.computation_lambda(inner);
    let identity = arena.value_thunk(outer);
    let returns_num = arena.comp_type_returner(decoded_num);
    let suspended = arena.value_type_thunk(returns_num);
    let id = arena.value_constant(ConstantIndex::from(2_usize));
    let n = arena.value_constant(ConstantIndex::from(1_usize));
    let head = arena.computation_force(id);
    let instantiated = arena.computation_application(head, num);
    let applied = arena.computation_application(instantiated, n);
    let thunk = arena.value_thunk(applied);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(small), Maybe::Present(code)),
        declaration(At(1), Maybe::Present(decoded_num), Maybe::Present(zero)),
        declaration(
            At(2),
            Maybe::Present(identity_type),
            Maybe::Present(identity),
        ),
        declaration(At(3), Maybe::Present(suspended), Maybe::Present(thunk)),
    ]);
    for judged in report.judged() {
        assert!(
            matches!(judged.verdict(), Verdict::Checked { .. }),
            "the identity instantiates at the code constant: {:?}",
            judged.verdict()
        );
    }
    for entry in readmission.readmitted() {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "{:?} is admitted",
            entry.outcome()
        );
    }
    assert_eq!(
        steps(&readmission.readmitted()[3]),
        [convertible(At(0))],
        "the argument unfolds in term position and the declared type at its decode: \
             one instance, certified once"
    );
}

/// `El` as unquote: a function to a universe, called where a type is read,
/// stands for the type its call returns the quote of. The checker runs
/// the closed call under a certificate that holds each δ-step, the kernel
/// replays it reading the returned code as its computation, a call that
/// returns another quote is refused at the type it does return, a call on
/// a binder stays a decode that converts with another node of the same
/// call, and a trace stripped of its steps is declined.
#[test]
fn an_unquoted_function_call_crosses_with_its_run_certified()
{
    // def pick : U (Integer + Unit -> F Type) =
    //     thunk λ. case x { _ => return ⌜Integer⌝ ; _ => return ⌜Unit⌝ } ;
    // def n : El (returned ((force pick) (Inj0 0))) = 0 ;
    // def m : El (returned ((force pick) (Inj1 unit))) = 0 ;
    // def keep : U ((t : Integer + Unit) -> El (returned ((force pick) t))
    //     -> F El (returned ((force pick) t))) = thunk λ λ. return x ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let unit_type = arena.value_type_unit();
    let tagged = arena.value_type_sum(&[integer, unit_type]);
    let returns_code = arena.comp_type_returner(small);
    let picking = arena.comp_type_arrow(tagged, returns_code);
    let picking = arena.value_type_thunk(picking);
    let integer_code = arena.value_quote(integer);
    let unit_code = arena.value_quote(unit_type);
    let to_integer = arena.computation_return(integer_code);
    let to_unit = arena.computation_return(unit_code);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_case(bound, &[to_integer, to_unit]);
    let pick = arena.computation_lambda(case);
    let pick = arena.value_thunk(pick);
    let zero = arena.value_literal(integer_literal());
    let unit = arena.value_unit();
    let call = |arena: &mut CoreArena, argument: ValueId| {
        let head = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(head);
        let applied = arena.computation_application(forced, argument);
        arena.value_returned(applied)
    };
    let first = arena.value_injection(gandr_core_term::Summand::from(0_usize), zero);
    let integer_call = call(&mut arena, first);
    let picked_integer = arena.value_type_element(integer_call, Level::zero());
    let second = arena.value_injection(gandr_core_term::Summand::from(1_usize), unit);
    let unit_call = call(&mut arena, second);
    let picked_unit = arena.value_type_element(unit_call, Level::zero());
    let held_call = call(&mut arena, bound);
    let held = arena.value_type_element(held_call, Level::zero());
    let returned_call = call(&mut arena, bound);
    let returned = arena.value_type_element(returned_call, Level::zero());
    let returns_held = arena.comp_type_returner(returned);
    let keeping = arena.comp_type_arrow(held, returns_held);
    let keeping = arena.comp_type_pi(tagged, keeping);
    let keeping = arena.value_type_thunk(keeping);
    let kept = arena.computation_return(bound);
    let kept = arena.computation_lambda(kept);
    let kept = arena.computation_lambda(kept);
    let kept = arena.value_thunk(kept);
    assert_ne!(held_call, returned_call, "the two calls are two nodes");
    let module = [
        declaration(At(0), Maybe::Present(picking), Maybe::Present(pick)),
        declaration(At(1), Maybe::Present(picked_integer), Maybe::Present(zero)),
        declaration(At(2), Maybe::Present(picked_unit), Maybe::Present(zero)),
        declaration(At(3), Maybe::Present(keeping), Maybe::Present(kept)),
    ];
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    let [ref function, ref selected, ref other, ref keep] = *report.judged()
    else {
        panic!("one verdict per declaration");
    };
    assert!(matches!(function.verdict(), Verdict::Checked { .. }));
    assert!(
        matches!(selected.verdict(), Verdict::Checked { .. }),
        "the call runs to the integer quote and `0` checks at it: {:?}",
        selected.verdict()
    );
    assert!(
        matches!(other.verdict(), Verdict::Refused(_)),
        "the other call runs to the unit quote, where `0` does not check: {:?}",
        other.verdict()
    );
    assert!(
        matches!(keep.verdict(), Verdict::Checked { .. }),
        "a call on a binder is rigid, and two nodes of it convert: {:?}",
        keep.verdict()
    );
    let readmission = readmit_with(&mut arena, &report, |certificate| certificate);
    let [ref function_entry, ref selected_entry, _, ref keep_entry] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert!(matches!(*function_entry.outcome(), Outcome::Defined { .. }));
    assert!(
        matches!(*selected_entry.outcome(), Outcome::Defined { .. }),
        "the kernel admits the declaration at the type the call returns: {:?}",
        selected_entry.outcome()
    );
    assert_eq!(
        steps(selected_entry),
        [(Unfolded::Returned(integer_call), KernelVerdict::Convertible)],
        "one run, certified once, replayed convertible"
    );
    assert!(
        matches!(*keep_entry.outcome(), Outcome::Defined { .. }),
        "the kernel admits the decode of the held call: {:?}",
        keep_entry.outcome()
    );
    let stripped = readmit_with(&mut arena, &report, |certificate| {
        certificate.with_decisions(Vec::new())
    });
    assert!(
        matches!(
            stripped.readmitted()[1].outcome(),
            Outcome::Refused(Refusal::CertificateDeclined {
                unfolded: Unfolded::Returned(at),
                ..
            }) if *at == integer_call
        ),
        "the replay needs the held unfolding the trace records: {:?}",
        stripped.readmitted()[1].outcome()
    );
}

/// An open decode steps by the kernel's own reading: `arrow(a)` on the
/// binder `a` runs to the quote of a function type over `a`, so a value
/// at that decode applies. The checker certifies the open step as a
/// reading and the closed one by the machine's dialogue; the kernel
/// re-derives each, and a forged reduct of either is refused by name.
#[test]
fn an_open_decode_crosses_read_and_a_forged_one_is_refused()
{
    // def arrow : U (Type -> F Type) = thunk λa. return ⌜U (El(a) -> F El(a))⌝ ;
    // def apply : U ((a : Type) -> El(⟨arrow a⟩) -> El(a) -> F El(a)) =
    //     thunk λ λ λ. force f v ;
    // def same : El(⟨arrow ⌜Integer⌝⟩) = thunk λ. return x ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let returns_code = arena.comp_type_returner(small);
    let coding = arena.comp_type_arrow(small, returns_code);
    let coding = arena.value_type_thunk(coding);
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(code, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let function = arena.comp_type_arrow(decoded, returns_decoded);
    let function = arena.value_type_thunk(function);
    let quoted = arena.value_quote(function);
    let returned = arena.computation_return(quoted);
    let arrow = arena.computation_lambda(returned);
    let arrow = arena.value_thunk(arrow);
    let call = |arena: &mut CoreArena, argument: ValueId| {
        let head = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(head);
        let applied = arena.computation_application(forced, argument);
        arena.value_returned(applied)
    };
    let open_call = call(&mut arena, code);
    let at_arrow = arena.value_type_element(open_call, Level::zero());
    let returning = arena.comp_type_arrow(decoded, returns_decoded);
    let applying = arena.comp_type_arrow(at_arrow, returning);
    let applying = arena.comp_type_pi(small, applying);
    let applying = arena.value_type_thunk(applying);
    let f = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let forced = arena.computation_force(f);
    let applied = arena.computation_application(forced, code);
    let apply = arena.computation_lambda(applied);
    let apply = arena.computation_lambda(apply);
    let apply = arena.computation_lambda(apply);
    let apply = arena.value_thunk(apply);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_code = arena.value_quote(integer);
    let closed_call = call(&mut arena, integer_code);
    let at_integer = arena.value_type_element(closed_call, Level::zero());
    let kept = arena.computation_return(code);
    let same = arena.computation_lambda(kept);
    let same = arena.value_thunk(same);
    let unit_type = arena.value_type_unit();
    let forged = arena.value_quote(unit_type);
    let module = [
        declaration(At(0), Maybe::Present(coding), Maybe::Present(arrow)),
        declaration(At(1), Maybe::Present(applying), Maybe::Present(apply)),
        declaration(At(2), Maybe::Present(at_integer), Maybe::Present(same)),
    ];
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    for judged in report.judged() {
        assert!(
            matches!(judged.verdict(), Verdict::Checked { .. }),
            "{:?}",
            judged.verdict()
        );
    }
    let readmission = readmit_with(&mut arena, &report, |certificate| certificate);
    let [_, ref apply_entry, ref same_entry] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert!(
        matches!(*apply_entry.outcome(), Outcome::Defined { .. }),
        "the kernel reads the open decode to the function type: {:?}",
        apply_entry.outcome()
    );
    assert_eq!(
        steps(apply_entry),
        [(Unfolded::Returned(open_call), KernelVerdict::Convertible)],
        "one open run, read once"
    );
    assert!(
        matches!(*same_entry.outcome(), Outcome::Defined { .. }),
        "{:?}",
        same_entry.outcome()
    );

    let forging = |derivation: crate::code::Derivation| {
        move |certificate: crate::code::Certificate| {
            if certificate.derivation() == derivation {
                certificate.with_reduct(forged)
            }
            else {
                certificate
            }
        }
    };
    for (derivation, at, redex) in [
        (crate::code::Derivation::Reading, 1_usize, open_call),
        (crate::code::Derivation::Dialogue, 2_usize, closed_call),
    ] {
        let forgery = readmit_with(&mut arena, &report, forging(derivation));
        assert!(
            matches!(
                forgery.readmitted()[at].outcome(),
                Outcome::Refused(Refusal::CertificateDeclined {
                    unfolded: Unfolded::Returned(stepped),
                    ..
                }) if *stepped == redex
            ),
            "{derivation:?}: a decode forged to the unit quote is refused: {:?}",
            forgery.readmitted()[at].outcome()
        );
    }
}

#[test]
fn a_declining_certificate_faults_the_declaration()
{
    // def Pair : Type -> Type = \X. El X * El X ;
    // def instance : Type = Pair Integer ;
    //
    // Missing dialogue and a foreign answer retain different reasons.
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let operator_type = arena.value_type_static_pi(small, small);
    let operator = pair_operator(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_code = arena.value_quote(integer);
    let pair = arena.value_constant(ConstantIndex::from(0_usize));
    let instance = arena.value_static_application(pair, integer_code);
    let module = [
        declaration(
            At(0),
            Maybe::Present(operator_type),
            Maybe::Present(operator),
        ),
        declaration(At(1), Maybe::Present(small), Maybe::Present(instance)),
    ];
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    let foreign = [ConversionDecision::Force {
        thunk: TraceNode::Constant(ConstantIndex::from(0_usize)),
    }];
    for (decisions, reason) in [
        (&[][..], ReplayRefusal::Exhausted),
        (foreign.as_slice(), ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        }),
    ] {
        let readmission = readmit_with(&mut arena, &report, |certificate| {
            certificate.with_decisions(decisions.to_vec())
        });
        let [ref operator_entry, ref faulted] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert_eq!(
            operator_entry.outcome(),
            &Outcome::Static,
            "the operator itself replays nothing"
        );
        let reason = ReplayDecline::Refused(reason);
        let refusal = Refusal::CertificateDeclined {
            unfolded: Unfolded::Definition(ConstantIndex::from(0_usize)),
            reason,
        };
        assert_eq!(faulted.outcome(), &Outcome::Refused(refusal));
        assert!(
            matches!(faulted.certificates(), [Replayed {
                    verdict: KernelVerdict::Declined(recorded),
                    ..
                }] if *recorded == reason),
            "the refusal and replay record preserve the same reason"
        );
        assert_eq!(refusal.classify(), FailureClass::EngineFault);
        assert!(
            readmission.environment().entries().is_empty(),
            "the refused declaration left the environment as it was"
        );
    }
}

#[test]
fn an_unbound_sealed_atom_is_refused()
{
    let mut arena = CoreArena::new();
    let atom = arena.value_type_abstract(ConstantIndex::from(3_usize));
    let at = CoreNode::Type(TypeNode::Value(atom));
    let (target, image) = erase(&mut arena, at);
    assert_eq!(
        image,
        Err(Refusal::OutOfFragment {
            at,
            former: UnadmittedFormer::Abstract,
        }),
        "an abstract atom is refused by name"
    );
    assert_eq!(
        target.watermark(),
        TermArena::new().watermark(),
        "nothing is minted at a guessed position"
    );
}

#[test]
fn a_bound_sealed_atom_lowers_to_the_kernel_atom()
{
    // module Counter :> #{ type T, seed : T } { type T = Integer ;
    //                                           def seed = 7 ; }
    // def client : Counter.T = Counter.seed ;
    //
    // The atom crosses first, at kernel position 0; the member checks at
    // the representation and the witness exports it at the atom, both
    // inside the seal; the client reads the atom past it.
    use gandr_kernel_core::Environment;
    use gandr_kernel_term::SealExtent;
    use gandr_kernel_term::SealScope;

    use crate::declaration::AbstractType;
    use crate::seal::ComponentOrdinal;
    use crate::seal::SealSite;
    use crate::seal::SealingSite;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let seven = arena.value_literal(integer_literal());
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let seed = arena.value_constant(ConstantIndex::from(1_usize));
    let exported = arena.value_constant(ConstantIndex::from(2_usize));
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        Declaration::abstract_type(
            ConstantIndex::from(0_usize),
            AbstractType::new(
                small,
                integer,
                SealExtent::from(2_usize),
                SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize)),
            ),
            origin(At(0)),
        ),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(seven)),
        declaration(At(2), Maybe::Present(atom), Maybe::Present(seed)),
        declaration(At(3), Maybe::Present(atom), Maybe::Present(exported)),
    ]);
    let positions: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| match *entry.outcome() {
            Outcome::Data { admitted, .. } => Ok(("data", usize::from(admitted.position()))),
            Outcome::Defined { admitted, .. } => Ok(("defined", usize::from(admitted.position()))),
            ref other @ (Outcome::Assumed { .. }
            | Outcome::Marked(_)
            | Outcome::Static
            | Outcome::Refused(_)
            | Outcome::Rejected(_)) => Err(other.clone()),
        })
        .collect();
    assert_eq!(
        positions,
        [
            Ok(("data", 0)),
            Ok(("defined", 1)),
            Ok(("defined", 2)),
            Ok(("defined", 3))
        ],
        "the atom crosses as a nominal declaration and every member and client is admitted"
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let contents: Vec<_> = artifact
        .declarations()
        .iter()
        .map(|marked| marked.declaration().content().clone())
        .collect();
    let DeclarationContent::AbstractType { kind, scope, .. } = contents[0]
    else {
        panic!("the atom exports as an abstract type");
    };
    assert_eq!(
        (artifact.arena().value_type(kind), scope),
        (
            Some(&KernelValueType::Universe {
                sort: GroundSort::Value,
                level: Level::zero(),
            }),
            SealScope::Closed(SealExtent::from(2_usize))
        ),
        "at its kind, its seal closed over the member and the witness and not the client"
    );
    for declared in contents.iter().skip(2) {
        let &DeclarationContent::Def { declared, .. } = declared
        else {
            panic!("the witness and the client export as definitions");
        };
        assert_eq!(
            artifact.arena().value_type(declared),
            Some(&KernelValueType::Abstract(ConstantIndex::from(0_usize))),
            "each reads the kernel atom at the position its abstract type took"
        );
    }
    assert!(
        Environment::replay(artifact.arena().clone(), artifact.declarations()).is_ok(),
        "the export replays, the seal where the producer drew it"
    );
}

#[test]
fn a_body_naming_a_withheld_declaration_is_refused()
{
    // def bad : Integer = "" ; def uses : Integer = bad ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(text_literal());
    let bad = arena.value_constant(ConstantIndex::from(0_usize));
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(bad)),
    ]);
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the judgement reads the reference through the declared type"
    );
    let uses = &readmission.readmitted()[1];
    let withheld = Refusal::Withheld {
        at: bad,
        constant: ConstantIndex::from(0_usize),
    };
    assert_eq!(
        (uses.origin(), uses.outcome()),
        (origin(At(1)), &Outcome::Refused(withheld)),
        "the reference is refused at the referring declaration's origin, naming its node"
    );
    assert_eq!(
        withheld.classify(),
        FailureClass::MalformedSource,
        "a withheld reference is the source's"
    );
    assert!(
        readmission.environment().entries().is_empty(),
        "nothing entered the kernel"
    );
}

#[test]
fn a_constant_resolves_to_its_readmitted_position()
{
    // def bad : Integer = "" ; def number : Integer = 0 ;
    // def word : String = "" ; def copy : String = word ;
    //
    // `word` is module position 2 and kernel position 1. The reference
    // crosses only under that map: kernel position 2 is `copy` itself, and
    // kernel position 0 is an integer.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let word = arena.value_constant(ConstantIndex::from(2_usize));
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(2), Maybe::Present(string), Maybe::Present(text)),
        declaration(At(3), Maybe::Present(string), Maybe::Present(word)),
    ]);
    assert!(
        matches!(*readmission.readmitted()[0].outcome(), Outcome::Marked(_)),
        "the first declaration does not cross"
    );
    assert_eq!(
        [
            crossed_at(&readmission, At(1)),
            crossed_at(&readmission, At(2)),
            crossed_at(&readmission, At(3)),
        ],
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(2_usize),
        ],
        "each crossing takes the next kernel position, and the reference crosses"
    );
}

#[test]
fn native_lists_check_and_round_trip()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let list_type = arena.value_type_list(unit_type);
    let unit = arena.value_unit();
    let nil = arena.value_list_nil();
    let cons = arena.value_list_cons(unit, nil);
    let bad_tail = arena.value_list_cons(unit, unit);
    let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let tail = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let cell = arena.value_list_cons(head, tail);
    let on_nil = arena.computation_return(nil);
    let on_cons = arena.computation_return(cell);
    let folded = arena.computation_list_fold(unit_type, list_type, cons, on_nil, on_cons);
    let folded = arena.value_thunk(folded);
    let result = arena.comp_type_returner(list_type);
    let fold_type = arena.value_type_thunk(result);
    let swapped = arena.value_list_cons(tail, head);
    let swapped = arena.computation_return(swapped);
    let swapped = arena.computation_list_fold(unit_type, list_type, cons, on_nil, swapped);
    let swapped = arena.value_thunk(swapped);
    let sum_nil = arena.value_injection(Side::Left.into(), unit);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(list_type), Maybe::Present(nil)),
        declaration(At(1), Maybe::Present(list_type), Maybe::Present(cons)),
        declaration(At(2), Maybe::Present(list_type), Maybe::Present(bad_tail)),
        declaration(At(3), Maybe::Present(fold_type), Maybe::Present(folded)),
        declaration(At(4), Maybe::Present(fold_type), Maybe::Present(swapped)),
        declaration(At(5), Maybe::Present(list_type), Maybe::Present(sum_nil)),
    ]);
    for admitted in &readmission.readmitted()[.. 2] {
        assert!(
            matches!(admitted.outcome(), Outcome::Defined { .. }),
            "{:?}",
            admitted.outcome()
        );
    }
    assert!(matches!(
        readmission.readmitted()[2].outcome(),
        Outcome::Marked(_)
    ));
    assert!(
        matches!(
            readmission.readmitted()[3].outcome(),
            Outcome::Defined { .. }
        ),
        "{:?}",
        readmission.readmitted()[3].outcome()
    );
    assert!(matches!(
        readmission.readmitted()[4].outcome(),
        Outcome::Marked(_)
    ));
    assert!(matches!(
        readmission.readmitted()[5].outcome(),
        Outcome::Marked(_)
    ));
    let image = readmission.export(BTreeMap::new());
    let imported = decode(image.as_image()).expect("lists decode");
    assert_eq!(
        gandr_kernel_term::encode(imported.arena(), imported.declarations()).as_image(),
        image.as_image()
    );
}

#[test]
fn effectful_declarations_are_refused_by_name_at_the_pure_boundary()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let interface = EffectSig::new(EffectName::from("IO"), [EffectOp {
        name: OperationName::from("emit"),
        payload: unit_type,
        reply: unit_type,
    }])
    .expect("one operation");
    let effectful =
        arena.comp_type_returner_with_effects(unit_type, EffectRow::singleton(interface.clone()));
    let effectful_type = arena.value_type_thunk(effectful);
    let pure = arena.comp_type_returner(unit_type);
    let pure_type = arena.value_type_thunk(pure);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let body = arena.value_thunk(returned);
    let requested = arena.computation_perform(interface.clone(), "emit".into(), unit);
    let requested_body = arena.value_thunk(requested);
    let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let resumed = arena.computation_resume(continuation, returned);
    let handled = arena.computation_handle(
        interface,
        requested,
        returned,
        [gandr_core_term::control::EffectClause {
            operation: "emit".into(),
            body: resumed,
        }]
        .into(),
    );
    let handled_body = arena.value_thunk(handled);
    let shifted = arena.computation_shift(resumed);
    let reset = arena.computation_reset(shifted);
    let reset_body = arena.value_thunk(reset);
    let stack_type = arena.value_type_stack(pure, pure);
    let stack = arena.value_reify([].into());
    let stack_constant = arena.value_constant(ConstantIndex::from(5_usize));
    let resumed = arena.computation_resume(stack_constant, returned);
    let resumed_body = arena.value_thunk(resumed);
    let quoted = arena.value_quote_computation(effectful);
    let quote_type = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        crate::synthesise_value(&mut context, quoted)
            .expect("a well-formed runtime computation code")
            .produced()
            .id()
    };
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(effectful_type),
            Maybe::Present(requested_body),
        ),
        declaration(At(1), Maybe::Present(effectful_type), HOLE),
        declaration(At(2), Maybe::Present(pure_type), Maybe::Present(body)),
        declaration(
            At(3),
            Maybe::Present(pure_type),
            Maybe::Present(handled_body),
        ),
        declaration(At(4), Maybe::Present(pure_type), Maybe::Present(reset_body)),
        declaration(At(5), Maybe::Present(stack_type), Maybe::Present(stack)),
        declaration(
            At(6),
            Maybe::Present(pure_type),
            Maybe::Present(resumed_body),
        ),
        declaration(At(7), Maybe::Present(quote_type), Maybe::Present(quoted)),
    ]);
    for (position, entry) in readmission.readmitted().iter().take(2).enumerate() {
        assert_eq!(entry.constant(), ConstantIndex::from(position));
        assert_eq!(
            entry.outcome(),
            &Outcome::Refused(Refusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Computation(effectful)),
                former: UnadmittedFormer::EffectRow
            })
        );
    }
    assert!(matches!(
        readmission.readmitted()[2].outcome(),
        Outcome::Defined { .. }
    ));
    for (position, at, former) in [
        (
            3_usize,
            CoreNode::Term(TermNode::Computation(handled)),
            UnadmittedFormer::Handle,
        ),
        (
            4,
            CoreNode::Term(TermNode::Computation(reset)),
            UnadmittedFormer::Reset,
        ),
        (
            5,
            CoreNode::Type(TypeNode::Value(stack_type)),
            UnadmittedFormer::Stack,
        ),
        (
            6,
            CoreNode::Term(TermNode::Computation(resumed)),
            UnadmittedFormer::Resume,
        ),
        (
            7,
            CoreNode::Type(TypeNode::Computation(effectful)),
            UnadmittedFormer::EffectRow,
        ),
    ] {
        let entry = &readmission.readmitted()[position];
        assert_eq!(entry.constant(), ConstantIndex::from(position));
        assert_eq!(
            entry.outcome(),
            &Outcome::Refused(Refusal::OutOfFragment { at, former })
        );
    }
    assert!(readmission.audit().axioms().is_empty());
    let artifact = readmission.export(BTreeMap::new());
    let decoded = decode(artifact.as_image()).expect("the remaining pure definition exports");
    assert_eq!(decoded.declarations().len(), 1);
}

#[test]
fn a_lazy_product_crosses_as_its_kernel_nodes()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_unit = arena.comp_type_returner(unit_type);
    let returns_integer = arena.comp_type_returner(integer);
    let pair_type = arena.comp_type_with(returns_unit, returns_integer);
    let suspended_pair = arena.value_type_thunk(pair_type);
    let unit = arena.value_unit();
    let zero = arena.value_literal(integer_literal());
    let first = arena.computation_return(unit);
    let second = arena.computation_return(zero);
    let pair = arena.computation_with(first, second);
    let pair_body = arena.value_thunk(pair);
    let pair_constant = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(pair_constant);
    let projected = arena.computation_project(Side::Right, forced);
    let projected_body = arena.value_thunk(projected);
    let projected_type = arena.value_type_thunk(returns_integer);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(suspended_pair),
            Maybe::Present(pair_body),
        ),
        declaration(
            At(1),
            Maybe::Present(projected_type),
            Maybe::Present(projected_body),
        ),
    ]);
    for entry in readmission.readmitted() {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "the kernel re-derives the pairing at its unequal sides and the right \
                 projection at the right side's type: {:?}",
            entry.outcome()
        );
    }
    let artifact = readmission.export(BTreeMap::new());
    let decoded = decode(artifact.as_image()).expect("the lazy product exports");
    assert_eq!(decoded.declarations().len(), 2);
}

#[test]
fn an_ascription_crosses_as_a_typed_position_the_kernel_replays()
{
    // def given : U (F Integer) =
    //     thunk { f ← (return thunk { \x. return x }
    //                  : F (U (Integer -> F Integer))) ;
    //             (force f)(0) } ;
    // def same : U (F Integer) =
    //     thunk { (\x. return x : Integer -> F Integer)(0) } ;
    // Each ascribed body only checks and stands where the kernel
    // synthesises, so an image that erased the ascription is refused.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let given_type = arena.value_type_thunk(returns_integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let suspended_arrow = arena.value_type_thunk(arrow);
    let returns_suspended = arena.comp_type_returner(suspended_arrow);
    let zero = arena.value_literal(integer_literal());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = arena.computation_return(bound);
    let lambda = arena.computation_lambda(identity);
    let suspended = arena.value_thunk(lambda);
    let returns_thunk = arena.computation_return(suspended);
    let ascribed = arena.computation_ascribe(returns_thunk, returns_suspended);
    let forced = arena.computation_force(bound);
    let called = arena.computation_application(forced, zero);
    let bind = arena.computation_bind(ascribed, called);
    let given_body = arena.value_thunk(bind);
    let ascribed_lambda = arena.computation_ascribe(lambda, arrow);
    let applied = arena.computation_application(ascribed_lambda, zero);
    let same_body = arena.value_thunk(applied);
    let same_type = given_type;
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(given_type),
            Maybe::Present(given_body),
        ),
        declaration(At(1), Maybe::Present(same_type), Maybe::Present(same_body)),
    ]);
    assert_eq!(readmission.readmitted().len(), 2);
    for entry in readmission.readmitted() {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "the kernel checks each ascribed body, a return and a lambda that only \
                 check, at the stated type: {:?}",
            entry.outcome()
        );
    }
}

#[test]
fn native_path_module_round_trips()
{
    use alloc::sync::Arc;

    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_core::path_universe::Dialogue;
    use gandr_kernel_core::path_universe::Transport;
    use gandr_kernel_core::path_universe::replay_transport;
    use gandr_kernel_core::replay::EngineClaim;
    use gandr_kernel_core::replay::ReplayBudget;
    use gandr_kernel_term::PathEvidence;

    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit_type, unit_type]);
    let code = arena.value_quote(boolean);
    let path_type = arena.value_type_path_universe(code, code);
    let unit = arena.value_unit();
    let truth = arena.value_injection(Side::Left.into(), unit);
    let falsity = arena.value_injection(Side::Right.into(), unit);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let left = arena.value_injection(Side::Right.into(), variable);
    let right = arena.value_injection(Side::Left.into(), variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let not = arena.computation_case(variable, &[left, right]);
    let not = arena.computation_lambda(not);
    let not = arena.value_thunk(not);
    // These are untrusted candidate dialogues, not acceptance marks. The
    // native admission below derives and replays all four round trips.
    let evidence = Arc::new(PathEvidence {
        source: vec![vec![ConversionDecision::Decompose], Vec::new()],
        target: vec![Vec::new(), vec![ConversionDecision::Decompose]],
    });
    let path = arena.value_path_equiv(path_type, not, not, evidence);
    let refl = arena.value_path_refl(code);
    let product_type = arena.value_type_product(&[boolean, boolean]);
    let product_code = arena.value_quote(product_type);
    let product_path_type = arena.value_type_path_universe(product_code, product_code);
    let product_path = arena.value_path_product(path, refl);
    let input = arena.value_tuple(&[falsity, truth]);
    let transport = arena.computation_transport(product_path, input);
    let body = arena.value_thunk(transport);
    let result = arena.comp_type_returner(product_type);
    let declared = arena.value_type_thunk(result);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(path_type), Maybe::Present(path)),
        declaration(At(1), Maybe::Present(path_type), Maybe::Present(refl)),
        declaration(
            At(2),
            Maybe::Present(product_path_type),
            Maybe::Present(product_path),
        ),
        declaration(At(3), Maybe::Present(declared), Maybe::Present(body)),
    ]);
    let image = readmission.export(BTreeMap::new());
    let imported = decode(image.as_image()).expect("native module decodes");
    assert_eq!(
        gandr_kernel_term::encode(imported.arena(), imported.declarations()).as_image(),
        image.as_image()
    );
    let declarations = imported.declarations();
    let [_, _, _, ref transported] = *declarations
    else {
        panic!(
            "every native declaration must cross: {:?}",
            readmission.readmitted()
        );
    };
    let DeclarationContent::Def { body, .. } = *transported.declaration().content()
    else {
        panic!("transport is a definition");
    };
    let Some(&KernelValue::Thunk(computation)) = imported.arena().value(body)
    else {
        panic!("transport is suspended");
    };
    let Some(&gandr_kernel_term::Computation::Transport(path, value)) =
        imported.arena().computation(computation)
    else {
        panic!("transport remains native on import");
    };
    let mut kernel = imported.arena().clone();
    let unit = kernel.value_unit();
    let truth = kernel.value_injection(Side::Left.into(), unit);
    let output = kernel.value_tuple(&[truth, truth]);
    let expected = kernel.computation_return(output);
    assert_eq!(
        replay_transport(
            &mut kernel,
            Transport { path, value },
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        )
        .expect("imported certificate is rechecked"),
        KernelVerdict::Convertible
    );
}

#[test]
fn an_export_names_each_crossed_declaration_at_its_position()
{
    // module M { def bad : Integer = "" ; def first : Integer = 0 ;
    //            def second : Integer = first ; }
    // def top : Integer = M.second ;
    //
    // `bad` is marked and leaves the artifact. `first` crosses at kernel
    // position 0, so `second` reads 0 and `top` reads 1 whatever they are
    // named, and `top` is given no name at all.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(text_literal());
    let zero = arena.value_literal(integer_literal());
    let first = arena.value_constant(ConstantIndex::from(1_usize));
    let second = arena.value_constant(ConstantIndex::from(2_usize));
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(2), Maybe::Present(integer), Maybe::Present(first)),
        declaration(At(3), Maybe::Present(integer), Maybe::Present(second)),
    ]);
    let named = |segments: [&str; 2]| {
        StructuredName::from(
            segments
                .into_iter()
                .map(|segment| NameSegment::from_text(String::from(segment)).unwrap())
                .collect::<Vec<NameSegment>>(),
        )
    };
    let names = BTreeMap::from([
        (ConstantIndex::from(0_usize), named(["M", "bad"])),
        (ConstantIndex::from(1_usize), named(["M", "first"])),
        (ConstantIndex::from(2_usize), named(["M", "second"])),
    ]);
    let artifact = decode(readmission.export(names).as_image()).unwrap();

    let exported: Vec<(Vec<&str>, AdmissionMark, Option<&KernelValue>)> = artifact
        .declarations()
        .iter()
        .map(|marked| {
            let body = match *marked.declaration().content() {
                DeclarationContent::Def { body, .. } => artifact.arena().value(body),
                DeclarationContent::Axiom { .. }
                | DeclarationContent::Data { .. }
                | DeclarationContent::AbstractType { .. } => None,
            };
            let name = marked
                .declaration()
                .name()
                .segments()
                .iter()
                .map(AsRef::as_ref)
                .collect();
            (name, marked.mark(), body)
        })
        .collect();
    let at = |position: usize| Some(KernelValue::Constant(ConstantIndex::from(position)));
    assert_eq!(
        exported
            .iter()
            .map(|&(ref name, mark, _)| (name.clone(), mark))
            .collect::<Vec<_>>(),
        [
            (vec!["M", "first"], AdmissionMark::Checked),
            (vec!["M", "second"], AdmissionMark::Checked),
            (vec![], AdmissionMark::Checked),
        ],
        "each crossed declaration carries its own name, the marked one is absent, and \
             an unnamed one carries none"
    );
    assert_eq!(
        exported
            .iter()
            .skip(1)
            .map(|&(_, _, body)| body.cloned())
            .collect::<Vec<_>>(),
        [at(0), at(1)],
        "each reference reads the kernel position its target took"
    );
}

#[test]
fn every_former_outside_the_fragment_is_refused_by_name()
{
    // The abstract atom is witnessed by its own test.
    let mut arena = CoreArena::new();
    let unit = arena.value_unit();

    let rows = [
        (
            CoreNode::Term(TermNode::Value(arena.value_lift(Level::zero(), unit))),
            UnadmittedFormer::ValueLift,
        ),
        (
            CoreNode::Term(TermNode::Value(arena.value_literal(numeric_literal()))),
            UnadmittedFormer::NumericLiteral,
        ),
        (
            CoreNode::Type(TypeNode::Value(arena.value_type_base(BaseType::Numeric))),
            UnadmittedFormer::NumericAtom,
        ),
        (
            CoreNode::Type(TypeNode::Value(arena.value_type_universe(
                Sort::Parameter(SortParameter::from(0_u32)),
                Level::zero(),
            ))),
            UnadmittedFormer::SortParameter,
        ),
    ];
    for (at, former) in rows {
        assert_eq!(
            erase(&mut arena, at).1,
            Err(Refusal::OutOfFragment { at, former }),
            "{former:?} is refused by name, at its node"
        );
    }
}

#[test]
fn element_identity_and_a_compound_endpoint_are_readmitted()
{
    // def id        : U (Integer -> F Integer) = thunk { \x. return x } ;
    // def same      : Path(Integer, 0, 0) = here(0) ;
    // def moved     : U (F Path(Integer, 0, 0))
    //               = thunk { tr(y. Path(Integer, 0, y), here(0), here(0)) } ;
    // def compound  : Path(Integer, (id 0), 0) = here(0) ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let suspended_arrow = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returns_bound = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returns_bound);
    let identity = arena.value_thunk(lambda);
    let zero = arena.value_literal(integer_literal());
    let here = arena.value_here(zero);
    let path = arena.value_type_path(integer, zero, zero);
    let motive = arena.value_type_path(integer, zero, bound);
    let transport = arena.computation_path_transport(motive, here, here);
    let moved = arena.value_thunk(transport);
    let returns_path = arena.comp_type_returner(path);
    let suspended_path = arena.value_type_thunk(returns_path);
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(named);
    let applied = arena.computation_application(forced, zero);
    let compound = arena.value_returned(applied);
    let compound_path = arena.value_type_path(integer, compound, zero);
    let module = [
        declaration(
            At(0),
            Maybe::Present(suspended_arrow),
            Maybe::Present(identity),
        ),
        declaration(At(1), Maybe::Present(path), Maybe::Present(here)),
        declaration(At(2), Maybe::Present(suspended_path), Maybe::Present(moved)),
        declaration(At(3), Maybe::Present(compound_path), Maybe::Present(here)),
    ];
    let (report, readmission) = judge_and_readmit(&mut arena, &module);
    let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
    assert!(
        verdicts
            .iter()
            .all(|verdict| matches!(verdict, Verdict::Checked { .. })),
        "the judgement accepts all four: {verdicts:?}"
    );
    let [_, ref same, ref transported, ref compounded] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert!(
        matches!(*same.outcome(), Outcome::Defined { .. }),
        "a path type and its reflexivity cross, and the kernel re-derives them: {:?}",
        same.outcome()
    );
    assert!(
        matches!(*transported.outcome(), Outcome::Defined { .. }),
        "a transport in a motive under its binder crosses, and the kernel re-derives it: \
             {:?}",
        transported.outcome()
    );
    assert!(
        matches!(*compounded.outcome(), Outcome::Defined { .. }),
        "a compound endpoint crosses, and the kernel replays its dialogue through `id`: {:?}",
        compounded.outcome()
    );
    assert_eq!(
        [
            crossed_at(&readmission, At(0)),
            crossed_at(&readmission, At(1)),
            crossed_at(&readmission, At(2)),
            crossed_at(&readmission, At(3)),
        ],
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(2_usize),
            ConstantIndex::from(3_usize),
        ],
        "the definition and the three identity declarations enter in declaration order"
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let declared = artifact
        .declarations()
        .last()
        .map(|marked| marked.declaration().declared_id())
        .unwrap();
    let Some(&KernelValueType::Path { left, .. }) = artifact.arena().value_type(declared)
    else {
        panic!("the compound declaration crosses at a path type");
    };
    let Some(&KernelValue::Returned(applied)) = artifact.arena().value(left)
    else {
        panic!("its source endpoint crosses as the kernel's returned endpoint");
    };
    assert!(
        matches!(
            artifact.arena().computation(applied),
            Some(&gandr_kernel_term::Computation::Application(..))
        ),
        "over the application it erases, not the value it returns"
    );
}

#[test]
fn a_reflexive_transport_at_a_path_motive_is_readmitted()
{
    // def moved_end : Path(Path(Integer, 0, 0),
    //                      ⟨tr(x. Path(Integer, x, x), here(0), here(0))⟩, here(0))
    //               = here(here(0)) ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let here = arena.value_here(zero);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_path(integer, bound, bound);
    let transport = arena.computation_path_transport(motive, here, here);
    let moved = arena.value_returned(transport);
    let looped = arena.value_type_path(integer, zero, zero);
    let declared = arena.value_type_path(looped, moved, here);
    let here_here = arena.value_here(here);
    let (report, readmission) = judge_and_readmit(&mut arena, &[declaration(
        At(0),
        Maybe::Present(declared),
        Maybe::Present(here_here),
    )]);
    let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
    assert!(
        matches!(*verdicts, [Verdict::Checked { .. }]),
        "the checker reduces the reflexive transport: {verdicts:?}"
    );
    let [ref entry] = *readmission.readmitted()
    else {
        panic!("one outcome");
    };
    assert!(
        matches!(*entry.outcome(), Outcome::Defined { .. }),
        "and the kernel re-derives it: {:?}",
        entry.outcome()
    );
}

#[test]
fn a_dependent_pair_and_its_identity_are_readmitted()
{
    // def ring   : Σ (n : Integer). Path(Integer, n, n) = #{0, here(0)} ;
    // def lap    : U (Π (p : Σ…). F Path(Integer, ⟨p.0⟩, ⟨p.0⟩))
    //            = thunk { \p. split p under F Path(…) as (m, w). return w } ;
    // def second : U (Π (p : Σ…). F Path(Integer, ⟨p.0⟩, ⟨p.0⟩))
    //            = thunk { \p. p.1 } ;
    // def both   : Path(Σ…, #{0, here(0)}, #{0, here(0)})
    //            = #{here(0), here(here(0))} ;
    // def moved  : U (F Integer) = thunk { tr(s. Integer, both, 0) } ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let looped = arena.value_type_path(integer, bound, bound);
    let sigma = arena.value_type_sigma(integer, looped);
    let zero = arena.value_literal(integer_literal());
    let here = arena.value_here(zero);
    let pair = arena.value_tuple(&[zero, here]);
    let projected =
        arena.computation_tuple_projection(bound, gandr_kernel_term::Component::from(0_usize));
    let projected = arena.value_returned(projected);
    let at_first = arena.value_type_path(integer, projected, projected);
    let answer = arena.comp_type_returner(at_first);
    let dependent = arena.comp_type_pi(sigma, answer);
    let suspended = arena.value_type_thunk(dependent);
    let returns_second = arena.computation_return(bound);
    let split = arena.computation_dependent_split(
        bound,
        gandr_core_term::ComponentCount::from(2_usize),
        answer,
        returns_second,
    );
    let split = arena.computation_lambda(split);
    let split = arena.value_thunk(split);
    let second =
        arena.computation_tuple_projection(bound, gandr_kernel_term::Component::from(1_usize));
    let second = arena.computation_lambda(second);
    let second = arena.value_thunk(second);
    let identity = arena.value_type_path(sigma, pair, pair);
    let here_here = arena.value_here(here);
    let paths = arena.value_tuple(&[here, here_here]);
    let both = arena.value_constant(ConstantIndex::from(3_usize));
    let constant = arena.value_type_base(BaseType::Integer);
    let transport = arena.computation_path_transport(constant, both, zero);
    let moved = arena.value_thunk(transport);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended_integer = arena.value_type_thunk(returns_integer);
    let module = [
        declaration(At(0), Maybe::Present(sigma), Maybe::Present(pair)),
        declaration(At(1), Maybe::Present(suspended), Maybe::Present(split)),
        declaration(At(2), Maybe::Present(suspended), Maybe::Present(second)),
        declaration(At(3), Maybe::Present(identity), Maybe::Present(paths)),
        declaration(
            At(4),
            Maybe::Present(suspended_integer),
            Maybe::Present(moved),
        ),
    ];
    let (report, readmission) = judge_and_readmit(&mut arena, &module);
    let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
    assert!(
        verdicts
            .iter()
            .all(|verdict| matches!(verdict, Verdict::Checked { .. })),
        "the judgement accepts the pair, the split, the projection, the path and the \
             transport: {verdicts:?}"
    );
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        outcomes
            .iter()
            .all(|outcome| matches!(*outcome, Outcome::Defined { .. })),
        "each crosses and the kernel re-derives it: {outcomes:?}"
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let declared = artifact
        .declarations()
        .first()
        .map(|marked| marked.declaration().declared_id())
        .unwrap();
    assert!(
        matches!(
            artifact.arena().value_type(declared),
            Some(&KernelValueType::Sigma { .. })
        ),
        "the dependent pair crosses as the kernel's own former"
    );
}

#[test]
fn a_funext_crosses_as_a_higher_evaluation()
{
    // def not, not_not, same : U (+{(), ()} -> F +{(), ()}) ;
    // def twice : Path(U (…), not_not, same) = funext(not_not, same) ;
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let [not_not, same] =
        [1_usize, 2_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let path = arena.value_type_path(functions.function, not_not, same);
    let funext = arena.value_funext(not_not, same);
    let declared = Maybe::Present(functions.function);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), declared, Maybe::Present(functions.not)),
        declaration(At(1), declared, Maybe::Present(functions.not_not)),
        declaration(At(2), declared, Maybe::Present(functions.same)),
        declaration(At(3), Maybe::Present(path), Maybe::Present(funext)),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays both functions' evaluations at every input: {:?}",
        readmission.readmitted()
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let Some(&DeclarationContent::Def { body, .. }) = artifact
        .declarations()
        .last()
        .map(|marked| marked.declaration().content())
    else {
        panic!("the extensionality is the last definition");
    };
    let Some(KernelValue::HigherEvaluation {
        dialogues,
        components,
    }) = artifact.arena().value(body).cloned()
    else {
        panic!("a funext crosses as the kernel's higher evaluation");
    };
    assert_eq!((dialogues.len(), components.len()), (2, 2));
    assert!(
        dialogues
            .iter()
            .all(|component| !component.left.is_empty() && !component.right.is_empty()),
        "every component carries both functions' traces"
    );
    let arena = artifact.arena();
    let digest = |value| content_digest(arena, AnyNode::Value(value));
    assert!(
        components.iter().enumerate().all(|(summand, component)| {
            digest(component.left) == digest(component.right)
                && arena
                    .value(component.evidence)
                    .and_then(KernelValue::components)
                    == Some(&[])
                && matches!(
                    arena.value(component.left),
                    Some(&KernelValue::Injection(found, _)) if usize::from(found) == summand
                )
        }),
        "each input returns itself on both sides, with the unit as its identity"
    );
}

/// A funext between functions that return a literal crosses with the literal
/// as both sides of its one component: an integer and a string alike.
#[test]
fn a_funext_returning_a_literal_crosses_with_the_literal()
{
    // def f, g : U (() -> F T) = λ_. return c ;
    // def same : Path(U (…), f, g) = funext(f, g) ;
    for (atom, literal) in [
        (BaseType::Integer, integer_literal()),
        (BaseType::String, text_literal()),
    ] {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let atom = arena.value_type_base(atom);
        let returns = arena.comp_type_returner(atom);
        let arrow = arena.comp_type_arrow(unit_type, returns);
        let function = arena.value_type_thunk(arrow);
        let [left, right] = [(), ()].map(|()| {
            let constant = arena.value_literal(literal.clone());
            let body = arena.computation_return(constant);
            let lambda = arena.computation_lambda(body);
            arena.value_thunk(lambda)
        });
        let [left_constant, right_constant] =
            [0_usize, 1_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let path = arena.value_type_path(function, left_constant, right_constant);
        let funext = arena.value_funext(left_constant, right_constant);
        let declared = Maybe::Present(function);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), declared, Maybe::Present(left)),
            declaration(At(1), declared, Maybe::Present(right)),
            declaration(At(2), Maybe::Present(path), Maybe::Present(funext)),
        ]);
        assert!(
            matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
            "both functions return the same literal: {:?}",
            report.judged()[2].verdict()
        );
        assert!(
            matches!(
                readmission.readmitted()[2].outcome(),
                Outcome::Defined { .. }
            ),
            "the literal crosses as itself on either side: {:?}",
            readmission.readmitted()[2].outcome()
        );
    }
}

#[test]
fn a_quantified_funext_crosses_as_a_quantified_evaluation()
{
    // def at_truth : U ((Bool -> F Bool) -> F Bool) = λh. h(true) ;
    // def bound = λh. x ← h(true); return x ;
    // def twice = λh. x ← h(true); h(x) ;
    // def twice_bound = λh. x ← h(true); y ← h(x); return y ;
    // def eta : Path(U (…), at_truth, bound) = funext(at_truth, bound) ;
    // def nested : Path(U (…), twice, twice_bound) = funext(twice, twice_bound) ;
    /// How one extensionality crossed.
    #[derive(Debug, Eq, PartialEq)]
    enum Crossed
    {
        /// A higher evaluation with this many components.
        Higher(usize),
        /// A quantified evaluation: its children, and per step whether it
        /// applies the premise at index zero.
        Quantified(usize, Vec<bool>),
    }
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let returns = arena.comp_type_returner(functions.ty);
    let arrow = arena.comp_type_arrow(functions.function, returns);
    let higher = arena.value_type_thunk(arrow);
    let unit = arena.value_unit();
    let truth = arena.value_injection(0_usize.into(), unit);
    // Beneath `λh`, `h` is index zero; beneath `λh. x ← …`, `x` is zero and
    // `h` one.
    let [innermost, outer] = [0_u32, 1_u32]
        .map(|index| arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
    let forced = arena.computation_force(innermost);
    let tail = arena.computation_application(forced, truth);
    let lambda = arena.computation_lambda(tail);
    let at_truth = arena.value_thunk(lambda);
    let returned = arena.computation_return(innermost);
    let forced_again = arena.computation_force(outer);
    let again = arena.computation_application(forced_again, innermost);
    let again_bound = arena.computation_bind(again, returned);
    let [bound, twice, twice_bound] = [returned, again, again_bound].map(|rest| {
        let first = arena.computation_bind(tail, rest);
        let lambda = arena.computation_lambda(first);
        arena.value_thunk(lambda)
    });
    let constant_body = arena.computation_return(truth);
    let constant_lambda = arena.computation_lambda(constant_body);
    let constant = arena.value_thunk(constant_lambda);
    let [
        at_truth_constant,
        bound_constant,
        twice_constant,
        twice_bound_constant,
        constant_constant,
    ] = [3_usize, 4, 5, 6, 7].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let eta_path = arena.value_type_path(higher, at_truth_constant, bound_constant);
    let eta = arena.value_funext(at_truth_constant, bound_constant);
    let nested_path = arena.value_type_path(higher, twice_constant, twice_bound_constant);
    let nested = arena.value_funext(twice_constant, twice_bound_constant);
    let unapplied_path = arena.value_type_path(higher, constant_constant, constant_constant);
    let unapplied = arena.value_funext(constant_constant, constant_constant);
    let declared = Maybe::Present(functions.function);
    let applying = Maybe::Present(higher);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), declared, Maybe::Present(functions.not)),
        declaration(At(1), declared, Maybe::Present(functions.not_not)),
        declaration(At(2), declared, Maybe::Present(functions.same)),
        declaration(At(3), applying, Maybe::Present(at_truth)),
        declaration(At(4), applying, Maybe::Present(bound)),
        declaration(At(5), applying, Maybe::Present(twice)),
        declaration(At(6), applying, Maybe::Present(twice_bound)),
        declaration(At(7), applying, Maybe::Present(constant)),
        declaration(At(8), Maybe::Present(eta_path), Maybe::Present(eta)),
        declaration(At(9), Maybe::Present(nested_path), Maybe::Present(nested)),
        declaration(
            At(10),
            Maybe::Present(unapplied_path),
            Maybe::Present(unapplied),
        ),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays every step under the quantifier: {:?}",
        readmission.readmitted()
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let crossed: Vec<Crossed> = artifact
            .declarations()
            .iter()
            .skip(8)
            .map(|marked| {
                let DeclarationContent::Def { body, .. } = *marked.declaration().content()
                else {
                    panic!("every extensionality is a definition");
                };
                match artifact.arena().value(body).cloned() {
                    | Some(KernelValue::HigherEvaluation { components, .. }) => {
                        Crossed::Higher(components.len())
                    },
                    | Some(KernelValue::QuantifiedEvaluation { steps, children }) => {
                        Crossed::Quantified(
                            children.len(),
                            steps
                                .iter()
                                .map(|step| matches!(step, gandr_kernel_term::QuantifiedStep::Apply { fibre, .. } if u32::from(*fibre) == 0))
                                .collect(),
                        )
                    },
                    | other => panic!("a funext crosses as an evaluation: {other:?}"),
                }
            })
            .collect();
    assert_eq!(
        crossed,
        Vec::from([
            Crossed::Quantified(8, Vec::from([true, false, false])),
            Crossed::Quantified(
                18,
                Vec::from([true, true, false, false, true, false, false])
            ),
            Crossed::Higher(1),
        ]),
        "pre-order steps, two children per application and three per return; a \
             body that never applies its argument crosses as a higher evaluation over \
             the single generic input"
    );
}

#[test]
fn a_reflexivity_crosses_with_the_dialogues_relating_its_endpoints()
{
    // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
    // def j : U (Integer -> F Integer) = k ;
    // def law : Path(U (…), thunk { force j }, k) = here(k) ;
    // Relating `k` to `thunk { force j }` unfolds `j` under the thunk, a
    // step only the recorded dialogue names.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let [k, j] = [0_usize, 1_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let forced = arena.computation_force(j);
    let delayed = arena.value_thunk(forced);
    let path = arena.value_type_path(function, delayed, k);
    let here = arena.value_here(k);
    let declared = Maybe::Present(function);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), declared, Maybe::Present(identity)),
        declaration(At(1), declared, Maybe::Present(k)),
        declaration(At(2), Maybe::Present(path), Maybe::Present(here)),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays the dialogue unfolding `j` under the thunk: {:?}",
        readmission.readmitted()
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let Some(&DeclarationContent::Def { body, .. }) = artifact
        .declarations()
        .last()
        .map(|marked| marked.declaration().content())
    else {
        panic!("the law is the last definition");
    };
    let Some(KernelValue::Here { dialogues, .. }) = artifact.arena().value(body).cloned()
    else {
        panic!("the law crosses as the kernel's reflexivity");
    };
    assert!(
        !dialogues.left.is_empty() && dialogues.right.is_empty(),
        "the delayed endpoint carries its dialogue and the point's own syntax none: \
             {dialogues:?}"
    );
    assert!(
        dialogues
            .left
            .iter()
            .any(|decision| matches!(decision, ConversionDecision::Unfold { .. })),
        "the dialogue names the unfoldings the kernel replays"
    );
}

/// The mirror of
/// `a_reflexivity_crosses_with_the_dialogues_relating_its_endpoints`:
/// with the delayed endpoint on the right, the right dialogue carries the
/// unfolding and the left none.
#[test]
fn a_reflexivity_carries_its_right_endpoint_s_dialogue()
{
    // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
    // def j : U (Integer -> F Integer) = k ;
    // def law : Path(U (…), k, thunk { force j }) = here(k) ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let [k, j] = [0_usize, 1_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let forced = arena.computation_force(j);
    let delayed = arena.value_thunk(forced);
    let path = arena.value_type_path(function, k, delayed);
    let here = arena.value_here(k);
    let declared = Maybe::Present(function);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), declared, Maybe::Present(identity)),
        declaration(At(1), declared, Maybe::Present(k)),
        declaration(At(2), Maybe::Present(path), Maybe::Present(here)),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays the right dialogue unfolding `j` under the thunk: {:?}",
        readmission.readmitted()
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let Some(&DeclarationContent::Def { body, .. }) = artifact
        .declarations()
        .last()
        .map(|marked| marked.declaration().content())
    else {
        panic!("the law is the last definition");
    };
    let Some(KernelValue::Here { dialogues, .. }) = artifact.arena().value(body).cloned()
    else {
        panic!("the law crosses as the kernel's reflexivity");
    };
    assert!(
        dialogues.left.is_empty() && !dialogues.right.is_empty(),
        "the delayed right endpoint carries its dialogue: {dialogues:?}"
    );
}

#[test]
fn an_ascription_crosses_with_the_endpoints_it_related()
{
    // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
    // def j : U (Integer -> F Integer) = k ;
    // def given : Path(U (…), thunk { force j }, k) = here(k) ;
    // def law : Path(U (…), k, k) = given ;
    // The ascription converts the two path types only through `j`'s body
    // under the thunk, which the kernel's forced reading does not unfold.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let [k, j, given] = [0_usize, 1, 2].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let forced = arena.computation_force(j);
    let delayed = arena.value_thunk(forced);
    let stated = arena.value_type_path(function, delayed, k);
    let diagonal = arena.value_type_path(function, k, k);
    let here = arena.value_here(k);
    let declared = Maybe::Present(function);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), declared, Maybe::Present(identity)),
        declaration(At(1), declared, Maybe::Present(k)),
        declaration(At(2), Maybe::Present(stated), Maybe::Present(here)),
        declaration(At(3), Maybe::Present(diagonal), Maybe::Present(given)),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays the ascription's dialogue: {:?}",
        readmission.readmitted()
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let related: Vec<usize> = artifact
        .declarations()
        .iter()
        .map(|marked| marked.declaration().related().len())
        .collect();
    assert_eq!(related, [0, 0, 0, 1], "the law alone carries a pair");
    let mut stripped = artifact.declarations().to_vec();
    if let Some(law) = stripped.last_mut() {
        *law = gandr_kernel_term::MarkedDeclaration::new(
            law.mark(),
            law.declaration().clone().relating(Vec::new()),
        );
    }
    let refusal = gandr_kernel_core::Environment::replay(artifact.arena().clone(), &stripped)
        .expect_err("without its pair the law is the refusal the ascription met before");
    assert_eq!(refusal.position(), ConstantIndex::from(3_usize));
    assert!(matches!(
        refusal.error(),
        &gandr_kernel_core::KernelError::ValueTypeMismatch(_)
    ));
}

/// `Flow(Type, ⌜Bool⌝, ⌜Bool⌝)`, `El(x)` and Bool's two constructors, over
/// [`crate::fixture::booleans`].
///
/// # Specification
/// trivial.
fn flows_of_booleans(
    arena: &mut CoreArena,
    boolean: ValueTypeId,
) -> (ValueTypeId, ValueTypeId, [ValueId; 2])
{
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_quote(boolean);
    let flow_type = arena.value_type_flow(universe, code, code);
    let decoded = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(decoded, Level::zero());
    let unit = arena.value_unit();
    let constructors = [0_usize, 1].map(|summand| arena.value_injection(summand.into(), unit));
    (flow_type, element, constructors)
}

/// Assert that every declaration of `report` checks and the kernel
/// readmits every one of them as a definition.
///
/// # Specification
/// trivial.
fn checks_and_readmits(
    report: &ModuleReport,
    readmission: &Readmission,
)
{
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "every declaration checks: {report:?}"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays every dialogue the checker recorded: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn a_ride_along_a_named_flow_crosses_with_the_flows_unfolding()
{
    // def not : U (Bool -> F Bool) = \b. case b of { .0 -> .1 ; .1 -> .0 } ;
    // def flip : Flow(Type, Bool, Bool) = forward(not) ;
    // def flipped : Path(Bool, ride(\X. X, flip, .0), .1) = here(.1) ;
    // The ride is stuck on `flip` until `flip` unfolds: a step only the
    // recorded dialogue names.
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let (flow_type, element, [truth, falsity]) = flows_of_booleans(&mut arena, functions.ty);
    let [not, flip] = [0_usize, 1].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let forward = arena.value_forward(not);
    let ride = arena.computation_ride(element, flip, truth);
    let ridden = arena.value_returned(ride);
    let path = arena.value_type_path(functions.ty, ridden, falsity);
    let here = arena.value_here(falsity);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(functions.function),
            Maybe::Present(functions.not),
        ),
        declaration(At(1), Maybe::Present(flow_type), Maybe::Present(forward)),
        declaration(At(2), Maybe::Present(path), Maybe::Present(here)),
    ]);
    // The checker relates the ride by unfolding `flip`, and the kernel
    // replays that unfolding at the ride's flow.
    checks_and_readmits(&report, &readmission);
}

#[test]
fn a_ride_through_named_translators_crosses_with_their_unfoldings()
{
    // def not : U (Bool -> F Bool) = \b. case b of { .0 -> .1 ; .1 -> .0 } ;
    // def both : Path(#{Bool, Bool},
    //   ride(\X. X, flowProduct(forward(not), forward(not)), #{.0, .1}),
    //   #{.1, .0}) = here(#{.1, .0}) ;
    // def each : Path(#{Bool, Bool},
    //   ride(\X. #{X, X}, forward(not), #{.0, .1}), #{.1, .0})
    //   = here(#{.1, .0}) ;
    // Each component's translator is the definition `not`, which unfolds
    // only once the components before it have returned.
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let (_, element, [truth, falsity]) = flows_of_booleans(&mut arena, functions.ty);
    let not = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(not);
    let paired = arena.value_flow_product(forward, forward);
    let pair = arena.value_type_product(&[functions.ty, functions.ty]);
    let doubled = arena.value_type_product(&[element, element]);
    let source = arena.value_tuple(&[truth, falsity]);
    let target = arena.value_tuple(&[falsity, truth]);
    let [both, each] = [(element, paired), (doubled, forward)].map(|(motive, flow)| {
        let ride = arena.computation_ride(motive, flow, source);
        let ridden = arena.value_returned(ride);
        arena.value_type_path(pair, ridden, target)
    });
    let here = arena.value_here(target);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(functions.function),
            Maybe::Present(functions.not),
        ),
        declaration(At(1), Maybe::Present(both), Maybe::Present(here)),
        declaration(At(2), Maybe::Present(each), Maybe::Present(here)),
    ]);
    // The checker unfolds `not` under each component's bind, in the order
    // the kernel's reduct binds them.
    checks_and_readmits(&report, &readmission);
}

#[test]
fn an_equiv_crosses_as_a_universe_path()
{
    // def not : U (+{(), ()} -> F +{(), ()}) ;
    // def negation : Path(Type, +{(), ()}, +{(), ()}) = equiv(not, not) ;
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let not = arena.value_constant(ConstantIndex::from(0_usize));
    let universe = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    let code = arena.value_quote(functions.ty);
    let path = arena.value_type_path(universe, code, code);
    let equiv = arena.value_equiv(not, not);
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(functions.function),
            Maybe::Present(functions.not),
        ),
        declaration(At(1), Maybe::Present(path), Maybe::Present(equiv)),
    ]);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays both round trips under the admitted negation: {:?}",
        readmission.readmitted()
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let Some(&DeclarationContent::Def { body, .. }) = artifact
        .declarations()
        .last()
        .map(|marked| marked.declaration().content())
    else {
        panic!("the equivalence is the last definition");
    };
    let arena = artifact.arena();
    let Some(KernelValue::PathEquiv {
        path_type,
        ref evidence,
        ..
    }) = arena.value(body).cloned()
    else {
        panic!("an equiv crosses as the kernel's native universe path");
    };
    assert!(
        matches!(
            arena.value_type(path_type),
            Some(&KernelValueType::PathUniverse(source, target))
                if content_digest(arena, AnyNode::Value(source)) == content_digest(arena, AnyNode::Value(target))
        ),
        "its classifier relates the quote of Bool to itself"
    );
    assert_eq!(
        (evidence.source.len(), evidence.target.len()),
        (2, 2),
        "one round trip per injection of each side's coverage"
    );
    assert!(
        evidence
            .source
            .iter()
            .chain(&evidence.target)
            .all(|dialogue| dialogue
                .iter()
                .any(|decision| matches!(decision, ConversionDecision::Unfold { .. }))),
        "every round trip unfolds the admitted negation"
    );
}

#[test]
fn marks_and_holes_are_refused_beside_their_positive_controls()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let sum = arena.value_type_sum(&[integer, integer]);
    let zero = arena.value_literal(integer_literal());
    let injection = arena.value_injection(Side::Left.into(), zero);
    let text = arena.value_literal(text_literal());
    let mismatched = arena.value_constant(ConstantIndex::from(5_usize));
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(sum), Maybe::Present(injection)),
        declaration(At(2), Maybe::Present(integer), HOLE),
        declaration(At(3), Maybe::Present(sum), HOLE),
        declaration(At(4), UNSIGNED, HOLE),
        declaration(At(5), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(6), Maybe::Present(integer), Maybe::Present(mismatched)),
    ];
    let (report, readmission) = judge_and_readmit(&mut arena, &module);
    let [
        ref control,
        ref sum_body,
        ref owed,
        ref sum_hole,
        ref hole,
        ref mismatched_entry,
        ref dependent,
    ] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert!(matches!(*control.outcome(), Outcome::Defined { .. }));
    assert!(
        matches!(*sum_body.outcome(), Outcome::Defined { .. }),
        "a checked sum injection crosses as a definition"
    );
    assert!(matches!(*owed.outcome(), Outcome::Assumed { .. }));
    assert!(
        matches!(*sum_hole.outcome(), Outcome::Assumed { .. }),
        "a hole with a formed sum signature crosses as an axiom"
    );
    assert_eq!(
        hole.outcome(),
        &Outcome::Marked(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(ConstantIndex::from(4_usize)),
        }),
        "an unsigned hole remains refused"
    );
    assert!(
        matches!(
            *mismatched_entry.outcome(),
            Outcome::Marked(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
        ),
        "an ill-typed body remains marked"
    );
    assert!(matches!(
        report.judged()[6].verdict(),
        Verdict::Checked { .. }
    ));
    assert_eq!(
        dependent.outcome(),
        &Outcome::Refused(Refusal::Withheld {
            at: mismatched,
            constant: ConstantIndex::from(5_usize),
        }),
        "a checked reference to a marked declaration is withheld"
    );
    assert_eq!(
        [
            crossed_at(&readmission, At(0)),
            crossed_at(&readmission, At(1)),
            crossed_at(&readmission, At(2)),
            crossed_at(&readmission, At(3)),
        ],
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(2_usize),
            ConstantIndex::from(3_usize),
        ],
        "both checked definitions and both formed holes enter in declaration order"
    );
    assert_eq!(
        readmission.audit().axioms(),
        [ConstantIndex::from(2_usize), ConstantIndex::from(3_usize)],
        "only the two signed holes are axioms"
    );
}

#[test]
fn a_hole_is_refused_where_it_stands_and_its_filling_is_admitted()
{
    use gandr_core_term::fill_hole;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::MarkIndex;
    use gandr_core_term::hole::TermId;

    // def holed  : Integer × Integer = (?h, 0) ;
    // def filled : Integer × Integer = (0, 0) ;   the same, ?h := 0
    // def kept   : Integer = mark 0 ;            a mark around a good body
    // def hidden : Integer = mark "" ;           a mark around a bad body
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[integer, integer]);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let hole = HoleId::from(0_u32);
    let standing = arena.value_hole(hole);
    let holed = arena.value_tuple(&[standing, zero]);
    let TermId::Value(filled) =
        fill_hole(&mut arena, TermId::Value(holed), hole, TermId::Value(zero))
    else {
        panic!("a value fills to a value");
    };
    let kept = arena.value_mark(MarkIndex::from(0_u32), zero);
    let hidden = arena.value_mark(MarkIndex::from(1_u32), text);
    let module = [
        declaration(At(0), Maybe::Present(product), Maybe::Present(holed)),
        declaration(At(1), Maybe::Present(product), Maybe::Present(filled)),
        declaration(At(2), Maybe::Present(integer), Maybe::Present(kept)),
        declaration(At(3), Maybe::Present(integer), Maybe::Present(hidden)),
    ];
    let (report, readmission) = judge_and_readmit(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the judgement accepts all four: a hole and a mark check against any type"
    );
    let [
        ref holed_entry,
        ref filled_entry,
        ref kept_entry,
        ref hidden_entry,
    ] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    let refusal = Refusal::Hole {
        at: CoreNode::Term(TermNode::Value(standing)),
        hole,
    };
    assert_eq!(
        holed_entry.outcome(),
        &Outcome::Refused(refusal),
        "the kernel is never offered a hole; the refusal names it where it stands"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::UserAbsence,
        "an unfilled hole is the author's absence"
    );
    assert!(
        matches!(*filled_entry.outcome(), Outcome::Defined { .. }),
        "the same declaration with the hole filled is admitted"
    );
    assert!(
        matches!(*kept_entry.outcome(), Outcome::Defined { .. }),
        "a mark is erased to its body, which the kernel re-derives"
    );
    assert!(
        matches!(*hidden_entry.outcome(), Outcome::Rejected(_)),
        "a mark never makes the kernel accept the body it wraps"
    );
    assert_eq!(
        readmission.audit().axioms(),
        [],
        "a refused hole is no axiom"
    );
}

#[test]
fn an_empty_ledger_readmits_an_artifact_resting_on_no_axiom()
{
    // An unsupported signed hole is marked, never entered as an axiom.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unformed = arena.value_type_base(BaseType::Numeric);
    let zero = arena.value_literal(integer_literal());
    let answer = arena.value_constant(ConstantIndex::from(0_usize));
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(1), UNSIGNED, Maybe::Present(answer)),
        declaration(At(2), Maybe::Present(unformed), HOLE),
    ]);
    assert!(
        report.ledger().entries().is_empty(),
        "the module owes nothing"
    );
    assert!(
        readmission.audit().axioms().is_empty()
            && readmission.audit().unchecked_admissions().is_empty(),
        "an artifact owing nothing rests on no axiom"
    );
    assert_eq!(
        (
            crossed_at(&readmission, At(0)),
            crossed_at(&readmission, At(1))
        ),
        (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)),
        "the definitions crossed, the signed one and the synthesised one"
    );
}

#[test]
fn each_owed_hole_is_an_axiom_of_the_artifact()
{
    // def first : Integer ; def uses : Integer = first ; def second : String ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let first = arena.value_constant(ConstantIndex::from(0_usize));
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(integer), HOLE),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(first)),
        declaration(At(2), Maybe::Present(string), HOLE),
    ]);
    let owed: Vec<_> = report
        .ledger()
        .entries()
        .iter()
        .map(|entry| entry.absence().origin())
        .collect();
    assert_eq!(
        owed,
        [origin(At(0)), origin(At(2))],
        "the module owes two holes"
    );
    let audits: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| match *entry.outcome() {
            Outcome::Defined { ref audit, .. }
            | Outcome::Assumed { ref audit, .. }
            | Outcome::Data { ref audit, .. } => audit.axioms().to_vec(),
            Outcome::Marked(_) | Outcome::Static | Outcome::Refused(_) | Outcome::Rejected(_) => {
                panic!("every declaration crosses")
            },
        })
        .collect();
    assert_eq!(
        audits,
        [
            Vec::from([ConstantIndex::from(0_usize)]),
            Vec::from([ConstantIndex::from(0_usize)]),
            Vec::from([ConstantIndex::from(2_usize)]),
        ],
        "an axiom's audit names itself, and a definition's names the axiom it reads"
    );
    assert!(
        matches!(
            (
                readmission.readmitted()[0].outcome(),
                readmission.readmitted()[2].outcome()
            ),
            (&Outcome::Assumed { .. }, &Outcome::Assumed { .. })
        ),
        "each owed hole crossed as an axiom"
    );
    assert_eq!(
        readmission.audit().axioms(),
        [ConstantIndex::from(0_usize), ConstantIndex::from(2_usize)],
        "the artifact rests on one axiom per ledger entry, in ledger order"
    );
}

#[test]
fn a_refused_declaration_leaves_the_environment_unchanged()
{
    // def id : U (Integer → F Integer) = thunk { λx. return x } ;
    // def bad : Integer = "" ;
    // def applied : U (F Integer) = thunk { (force id) bad } ;
    // def last : Integer = 0 ;
    //
    // `applied` erases its type and the head of its application before it
    // meets the withheld reference.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let function = arena.value_type_thunk(arrow);
    let suspended = arena.value_type_thunk(returns_integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let text = arena.value_literal(text_literal());
    let zero = arena.value_literal(integer_literal());
    let id = arena.value_constant(ConstantIndex::from(0_usize));
    let bad = arena.value_constant(ConstantIndex::from(1_usize));
    let head = arena.computation_force(id);
    let application = arena.computation_application(head, bad);
    let applied = arena.value_thunk(application);
    let crossing = [
        declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
        declaration(At(3), Maybe::Present(integer), Maybe::Present(zero)),
    ];
    let (_, control) = judge_and_readmit(&mut arena, &crossing);
    let [first, last] = crossing;
    let (_, readmission) = judge_and_readmit(&mut arena, &[
        first,
        declaration(At(1), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(2), Maybe::Present(suspended), Maybe::Present(applied)),
        last,
    ]);
    assert_eq!(
        readmission.readmitted()[2].outcome(),
        &Outcome::Refused(Refusal::Withheld {
            at: bad,
            constant: ConstantIndex::from(1_usize),
        }),
        "the application's argument is withheld"
    );
    assert_eq!(
        readmission.environment().arena().watermark(),
        control.environment().arena().watermark(),
        "the refused declaration left no node in the kernel arena"
    );
    assert_eq!(
        crossed_at(&readmission, At(3)),
        ConstantIndex::from(1_usize),
        "the next declaration takes the next kernel position"
    );
}

#[test]
fn a_shared_subterm_is_erased_once()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let inner = arena.computation_lambda(returned);
    let head = arena.computation_lambda(inner);
    let first = arena.computation_application(head, zero);
    let second = arena.computation_application(first, zero);
    let (target, image) = erase(&mut arena, CoreNode::Term(TermNode::Computation(second)));
    let Ok(AnyNode::Computation(image)) = image
    else {
        panic!("an application erases to a computation");
    };
    let Some(&gandr_kernel_term::Computation::Application(first, outer_argument)) =
        target.computation(image)
    else {
        panic!("the image is an application");
    };
    let Some(&gandr_kernel_term::Computation::Application(_, inner_argument)) =
        target.computation(first)
    else {
        panic!("its head is an application");
    };
    assert_eq!(
        outer_argument, inner_argument,
        "the literal both applications share is one kernel node"
    );
}

#[test]
fn the_machine_faults_are_refused_exactly()
{
    let mut arena = CoreArena::new();
    let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    assert_eq!(
        erase(&mut arena, CoreNode::Term(TermNode::Value(linear))).1,
        Err(Refusal::Session {
            at: CoreNode::Term(TermNode::Value(linear)),
        }),
        "a linear variable has no kernel zone to count in"
    );
    let dangling = CoreNode::Term(TermNode::Value(dangling_value()));
    assert_eq!(
        erase(&mut arena, dangling).1,
        Err(Refusal::DanglingNode { node: dangling }),
        "a dangling term is refused, not read"
    );
    let dangling = CoreNode::Type(TypeNode::Value(dangling_value_type()));
    assert_eq!(
        erase(&mut arena, dangling).1,
        Err(Refusal::DanglingNode { node: dangling }),
        "a dangling type is refused through the view"
    );
    // A thunk of a computation id this arena has not minted yet, then that
    // computation as the force of the thunk: each is the other's child.
    let mut cyclic = CoreArena::new();
    let mut scratch = CoreArena::new();
    let scratch_unit = scratch.value_unit();
    let ahead = scratch.computation_return(scratch_unit);
    let thunk = cyclic.value_thunk(ahead);
    let force = cyclic.computation_force(thunk);
    assert_eq!(force, ahead, "the force takes the id the thunk names");
    let node = CoreNode::Term(TermNode::Value(thunk));
    assert_eq!(
        erase(&mut cyclic, node).1,
        Err(Refusal::Cyclic { node }),
        "a node that is its own descendant is refused, not erased forever"
    );
    let positions = Positions::default();
    let lifts = alloc::collections::BTreeMap::new();
    let definitions = alloc::collections::BTreeMap::new();
    let mut target = TermArena::new();
    let unit = target.value_unit();
    let returned = arena.computation_return(linear);
    let source = Source {
        lifts: &lifts,
        funexts: &BTreeMap::new(),
        equivalences: &BTreeMap::new(),
        flows: &BTreeMap::new(),
        directed: &BTreeMap::new(),
        reflexivities: &BTreeMap::new(),
        relations: &BTreeMap::new(),
        laws: &BTreeMap::new(),
        natives: &BTreeMap::new(),
        definitions: &definitions,
    };
    assert_eq!(
        Erasure::new(&mut arena, source, &positions, ConstantIndex::from(0_usize)).resume(
            &mut target,
            Frame::Lambda { at: returned },
            AnyNode::Value(unit),
        ),
        Err(Refusal::MachineInvariant),
        "a frame handed an image of another family reports the miscount"
    );
}

#[test]
fn replay_decisions_preserve_shape_and_position_precedence()
{
    use gandr_core_nbe::TraceNode;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    use gandr_kernel_conversion_trace::SubgoalPosition;
    use gandr_kernel_core::ReplayNode;

    let crossed = ConstantIndex::from(0_usize);
    let static_only = ConstantIndex::from(1_usize);
    let missing = ConstantIndex::from(2_usize);
    let admitted = ConstantIndex::from(7_usize);
    let operator = ConstantIndex::from(9_usize);
    let mut positions = Positions::default();
    positions.admitted.insert(crossed, admitted);
    let operators = BTreeMap::from([
        (Unfolded::Definition(crossed), ConstantIndex::from(11_usize)),
        (Unfolded::Definition(static_only), operator),
    ]);
    assert_eq!(
        positions.kernel_decision(&operators, ConversionDecision::Decompose),
        ConversionDecision::Decompose
    );
    let mut arena = gandr_core_nbe::DomainArena::new();
    let unit = arena.value_unit(gandr_core_nbe::TermFace::Reduced);
    let returned = arena.comp_return(unit, gandr_core_nbe::CompTermFace::Reduced);
    let nodes = [
        (TraceNode::Constant(crossed), ReplayNode::Constant(admitted)),
        (
            TraceNode::Constant(static_only),
            ReplayNode::Constant(operator),
        ),
        (TraceNode::Constant(missing), ReplayNode::Other),
        (TraceNode::Value(unit), ReplayNode::Other),
        (TraceNode::Computation(returned), ReplayNode::Other),
    ];
    for (source, image) in nodes {
        let decisions = [
            (
                ConversionDecision::ReduceLeft { redex: source },
                ConversionDecision::ReduceLeft { redex: image },
            ),
            (
                ConversionDecision::ReduceRight { redex: source },
                ConversionDecision::ReduceRight { redex: image },
            ),
            (
                ConversionDecision::ConstShortcut { constant: source },
                ConversionDecision::ConstShortcut { constant: image },
            ),
            (
                ConversionDecision::Unfold { constant: source },
                ConversionDecision::Unfold { constant: image },
            ),
            (
                ConversionDecision::Postpone { constant: source },
                ConversionDecision::Postpone { constant: image },
            ),
            (
                ConversionDecision::Freeze {
                    constant: source,
                    side: ConversionSide::Right,
                },
                ConversionDecision::Freeze {
                    constant: image,
                    side: ConversionSide::Right,
                },
            ),
            (
                ConversionDecision::EtaExpand {
                    side: ConversionSide::Left,
                    variable: source,
                },
                ConversionDecision::EtaExpand {
                    side: ConversionSide::Left,
                    variable: image,
                },
            ),
            (
                ConversionDecision::Force { thunk: source },
                ConversionDecision::Force { thunk: image },
            ),
            (
                ConversionDecision::ComparedShared {
                    left: source,
                    right: TraceNode::Constant(missing),
                },
                ConversionDecision::ComparedShared {
                    left: image,
                    right: ReplayNode::Other,
                },
            ),
        ];
        for (decision, expected) in decisions {
            assert_eq!(positions.kernel_decision(&operators, decision), expected);
        }
    }
    let position = SubgoalPosition::from(3_u32);
    assert_eq!(
        positions.kernel_decision(&operators, ConversionDecision::NegativeSubgoal { position }),
        ConversionDecision::NegativeSubgoal { position }
    );
}

#[test]
fn every_recursive_node_family_refuses_a_back_edge()
{
    let mut foreign = CoreArena::new();
    let foreign_unit = foreign.value_unit();
    let comp_ahead = foreign.computation_return(foreign_unit);
    let type_ahead = foreign.value_type_unit();
    let mut arena = CoreArena::new();
    let thunk = arena.value_thunk(comp_ahead);
    let force = arena.computation_force(thunk);
    let returner = arena.comp_type_returner(type_ahead);
    let suspended = arena.value_type_thunk(returner);
    assert_eq!(force, comp_ahead);
    assert_eq!(suspended, type_ahead);
    for root in [
        CoreNode::Term(TermNode::Value(thunk)),
        CoreNode::Term(TermNode::Computation(force)),
        CoreNode::Type(TypeNode::Value(suspended)),
        CoreNode::Type(TypeNode::Computation(returner)),
    ] {
        assert_eq!(
            erase(&mut arena, root).1,
            Err(Refusal::Cyclic { node: root })
        );
    }
}

/// The small value universe `Type`.
///
/// # Specification
/// trivial.
fn small(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// `\X. El X * El X`, an operator of one parameter over small codes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one static lambda quoting a product of two decodes of its bound
///   variable, at de Bruijn zero and level zero.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one operator at two atom-code instances exposes two
///   distinct normalized product bodies and replayed certificates; wrong binder
///   index, level or product operand changes these observations.
/// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
#[spec(ensures: |ret| {
        let Some(&gandr_core_term::Value::StaticLambda(body)) = arena.value(ret) else { return false; };
        let Some(&gandr_core_term::Value::Quote(product)) = arena.value(body) else { return false; };
        let Some(held) = arena.value_type(product) else { return false; };
        let ValueType::Product(ref parts) = *held else { return false; };
        let [first, second] = **parts else { return false; };
        first == second && matches!(arena.value_type(first), Some(ValueType::Element { code, target })
            if bool::from(target.is_zero()) && matches!(arena.value(*code), Some(gandr_core_term::Value::Variable { zone: Zone::Intuitionistic, index }) if *index == DeBruijnIndex::from(0_u32)))
    })]
fn pair_operator(arena: &mut CoreArena) -> ValueId
{
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound, Level::zero());
    let product = arena.value_type_product(&[decoded, decoded]);
    let code = arena.value_quote(product);
    arena.value_static_lambda(code)
}

/// The content digest of each exported definition's body, in export
/// order.
///
/// # Specification
/// - requires: the readmission is a valid export.
/// - ensures: one canonical content digest per defined body, in export order;
///   axioms and refused declarations contribute none.
/// - panics: the export cannot be decoded.
///
/// # Adequacy
/// - hypothesis: L3 — two instances of one static operator expose exact
///   expected normalized body digests; hashing a signature, dropping a body or
///   retaining an unreduced application changes those comparisons.
/// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
#[spec(ensures: |ret| ret.len() == readmission.admitted.iter().filter(|declaration| matches!(declaration.content(), DeclarationContent::Def { .. })).count())]
fn exported_bodies(readmission: &Readmission) -> Vec<ContentDigest>
{
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    artifact
        .declarations()
        .iter()
        .filter_map(|marked| match *marked.declaration().content() {
            DeclarationContent::Def { body, .. } => {
                Some(content_digest(artifact.arena(), AnyNode::Value(body)))
            },
            DeclarationContent::Data { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::AbstractType { .. } => None,
        })
        .collect()
}

#[test]
fn a_step_fault_keeps_only_a_dangling_node()
{
    let node = CoreNode::Term(TermNode::Value(dangling_value()));
    assert_eq!(
        fault(CheckRefusal::DanglingNode { node }),
        Refusal::DanglingNode { node },
        "a dangling node stays one, at the same node"
    );
    for refusal in [
        CheckRefusal::Undecided {
            at: dangling_value(),
        },
        CheckRefusal::BudgetExceeded {
            budget: CheckBudget::DEFAULT,
        },
    ] {
        assert_eq!(
            fault(refusal),
            Refusal::MachineInvariant,
            "a step over a judged arena meets no other fault"
        );
    }
}

#[test]
fn family_applied_at_wrong_arity_raises_the_exact_variant()
{
    // def Pair : Type -> Type = \X. El X * El X ;
    // def Num : Type = Integer ;
    // def over : Type = Pair Integer Integer ;
    // def nullary : Type = Num Integer ;
    // def control : Type = Pair Integer ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let operator_type = arena.value_type_static_pi(small, small);
    let operator = pair_operator(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_code = arena.value_quote(integer);
    let pair = arena.value_constant(ConstantIndex::from(0_usize));
    let num = arena.value_constant(ConstantIndex::from(1_usize));
    let control = arena.value_static_application(pair, integer_code);
    let over = arena.value_static_application(control, integer_code);
    let nullary = arena.value_static_application(num, integer_code);
    let (report, _) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(operator_type),
            Maybe::Present(operator),
        ),
        declaration(At(1), Maybe::Present(small), Maybe::Present(integer_code)),
        declaration(At(2), Maybe::Present(small), Maybe::Present(over)),
        declaration(At(3), Maybe::Present(small), Maybe::Present(nullary)),
        declaration(At(4), Maybe::Present(small), Maybe::Present(control)),
    ]);
    let arity = |count: u32| StaticArity::from(count);
    assert_eq!(
        report.judged()[2].verdict(),
        Verdict::Refused(CheckRefusal::FamilyArity {
            at: over,
            expected: arity(1),
            actual: arity(2),
        }),
        "an operator of one parameter at two arguments names both counts, at the whole \
             application"
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::FamilyArity {
            at: nullary,
            expected: arity(0),
            actual: arity(1),
        }),
        "a code that is no operator takes no argument"
    );
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "the saturated instance checks: {:?}",
        report.judged()[4].verdict()
    );
}

#[test]
fn family_argument_at_wrong_classifier_raises_the_exact_variant()
{
    // def Both : Type -> Type -> Type = \A. \B. El A * El B ;
    // def literal : Type = Both Integer 0 ;
    // def negative : Type = Both (F Integer) Integer ;
    // def control : Type = Both Integer String ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let inner_type = arena.value_type_static_pi(small, small);
    let operator_type = arena.value_type_static_pi(small, inner_type);
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first = arena.value_type_element(outer, Level::zero());
    let second = arena.value_type_element(inner, Level::zero());
    let product = arena.value_type_product(&[first, second]);
    let code = arena.value_quote(product);
    let inner_lambda = arena.value_static_lambda(code);
    let operator = arena.value_static_lambda(inner_lambda);
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let integer_code = arena.value_quote(integer);
    let string_code = arena.value_quote(string);
    let returns = arena.comp_type_returner(integer);
    let action_code = arena.value_quote_computation(returns);
    let zero = arena.value_literal(integer_literal());
    let both = arena.value_constant(ConstantIndex::from(0_usize));
    let at_integer = arena.value_static_application(both, integer_code);
    let literal = arena.value_static_application(at_integer, zero);
    let at_action = arena.value_static_application(both, action_code);
    let negative = arena.value_static_application(at_action, integer_code);
    let control = arena.value_static_application(at_integer, string_code);
    let (report, _) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(operator_type),
            Maybe::Present(operator),
        ),
        declaration(At(1), Maybe::Present(small), Maybe::Present(literal)),
        declaration(At(2), Maybe::Present(small), Maybe::Present(negative)),
        declaration(At(3), Maybe::Present(small), Maybe::Present(control)),
    ]);
    let refused = |position: usize| match report.judged()[position].verdict() {
        Verdict::Refused(CheckRefusal::FamilyArgumentClassifier {
            at,
            position,
            synthesised,
            expected,
        }) => (
            at,
            u32::from(position),
            arena.value_type(synthesised).cloned(),
            expected,
        ),
        verdict @ (Verdict::Data
        | Verdict::Checked { .. }
        | Verdict::Synthesised { .. }
        | Verdict::Owed(_)
        | Verdict::Refused(_)) => panic!("refused at the argument's classifier: {verdict:?}"),
    };
    assert_eq!(
        refused(1),
        (zero, 1_u32, Some(ValueType::Base(BaseType::Integer)), small),
        "a value where a code stands names the argument, its position from the head, and \
             both classifiers"
    );
    assert_eq!(
        refused(2),
        (
            action_code,
            0_u32,
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Computation),
                level: Level::zero(),
            }),
            small
        ),
        "a code of the other sort names the universe it synthesised, sort and level"
    );
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "both arguments at their classifiers check: {:?}",
        report.judged()[3].verdict()
    );
}

#[test]
fn a_static_pi_over_a_type_that_classifies_no_codes_is_refused_by_name()
{
    // def from : Integer -> Type ;
    // def into : Type -> Integer ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let from = arena.value_type_static_pi(integer, small);
    let into = arena.value_type_static_pi(small, integer);
    let (report, _) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(from), HOLE),
        declaration(At(1), Maybe::Present(into), HOLE),
    ]);
    let verdicts: Vec<Verdict> = report.judged().iter().map(Judged::verdict).collect();
    assert_eq!(
        verdicts,
        [
            Verdict::Refused(CheckRefusal::StaticClassifierExpected {
                at: from,
                found: integer,
            }),
            Verdict::Refused(CheckRefusal::StaticClassifierExpected {
                at: into,
                found: integer,
            }),
        ],
        "a domain and a codomain that classify no codes are each named"
    );
}

#[test]
fn a_static_lambda_at_a_static_parameter_normalizes_away()
{
    // def Apply : (Type -> Type) -> Type -> Type = \F. \X. F X ;
    // def applied : Type = Apply (\Y. El Y * El Y) Integer ;
    // def written : Type = Integer * Integer ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let operator_type = arena.value_type_static_pi(small, small);
    let tail = arena.value_type_static_pi(small, small);
    let apply_type = arena.value_type_static_pi(operator_type, tail);
    let function = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let applied_variable = arena.value_static_application(function, argument);
    let inner = arena.value_static_lambda(applied_variable);
    let apply = arena.value_static_lambda(inner);
    let operator = pair_operator(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_code = arena.value_quote(integer);
    let head = arena.value_constant(ConstantIndex::from(0_usize));
    let partial = arena.value_static_application(head, operator);
    let applied = arena.value_static_application(partial, integer_code);
    let product = arena.value_type_product(&[integer, integer]);
    let written = arena.value_quote(product);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(apply_type), Maybe::Present(apply)),
        declaration(At(1), Maybe::Present(small), Maybe::Present(applied)),
        declaration(At(2), Maybe::Present(small), Maybe::Present(written)),
    ]);
    for judged in report.judged() {
        assert!(
            matches!(judged.verdict(), Verdict::Checked { .. }),
            "the lambda checks at the static parameter: {:?}",
            judged.verdict()
        );
    }
    assert_eq!(
        readmission.readmitted()[0].outcome(),
        &Outcome::Static,
        "the operator stays on the checker's side"
    );
    assert!(
        matches!(steps(&readmission.readmitted()[1]).as_slice(), [
                (Unfolded::Definition(position), KernelVerdict::Convertible),
                (Unfolded::Abstraction(_), KernelVerdict::Convertible),
            ] if *position == ConstantIndex::from(0_usize)),
        "the definition unfolds, then the lambda it was handed, each certified: {:?}",
        steps(&readmission.readmitted()[1])
    );
    let bodies = exported_bodies(&readmission);
    assert_eq!(
        bodies.len(),
        2_usize,
        "the instance and the written type cross, the operator does not"
    );
    assert_eq!(
        bodies.first(),
        bodies.last(),
        "the instance crosses as the static normal form, the lambda gone"
    );
}

#[test]
fn a_static_lambda_at_a_dynamic_parameter_is_refused_by_name()
{
    // def use : U ((F : Type -> Type) -> F Unit) ;
    // def Pair : Type -> Type = \X. El X * El X ;
    // def G : Type -> Type ;
    // def lambda : U (F Unit) = thunk ((force use) (\X. X)) ;
    // def named : U (F Unit) = thunk ((force use) Pair) ;
    // def rigid : U (F Unit) = thunk ((force use) G) ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let operator_type = arena.value_type_static_pi(small, small);
    let unit_type = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit_type);
    let takes_operator = arena.comp_type_pi(operator_type, returns_unit);
    let use_type = arena.value_type_thunk(takes_operator);
    let suspended = arena.value_type_thunk(returns_unit);
    let operator = pair_operator(&mut arena);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = arena.value_static_lambda(bound);
    let used = arena.value_constant(ConstantIndex::from(0_usize));
    let pair = arena.value_constant(ConstantIndex::from(1_usize));
    let opaque = arena.value_constant(ConstantIndex::from(2_usize));
    let forced = arena.computation_force(used);
    let mut thunk_of = |argument: ValueId| {
        let applied = arena.computation_application(forced, argument);
        arena.value_thunk(applied)
    };
    let lambda = thunk_of(identity);
    let named = thunk_of(pair);
    let rigid = thunk_of(opaque);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(use_type), HOLE),
        declaration(
            At(1),
            Maybe::Present(operator_type),
            Maybe::Present(operator),
        ),
        declaration(At(2), Maybe::Present(operator_type), HOLE),
        declaration(At(3), Maybe::Present(suspended), Maybe::Present(lambda)),
        declaration(At(4), Maybe::Present(suspended), Maybe::Present(named)),
        declaration(At(5), Maybe::Present(suspended), Maybe::Present(rigid)),
    ]);
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::StaticLambdaArgument { at: identity }),
        "a static lambda handed to a dynamic parameter is refused at the lambda"
    );
    assert_eq!(
        report.judged()[4].verdict(),
        Verdict::Refused(CheckRefusal::StaticLambdaArgument { at: pair }),
        "so is a static definition that unfolds to one"
    );
    assert!(
        matches!(report.judged()[5].verdict(), Verdict::Checked { .. }),
        "an opaque operator is a value the kernel types: {:?}",
        report.judged()[5].verdict()
    );
    assert!(
        matches!(
            *readmission.readmitted()[5].outcome(),
            Outcome::Defined { .. }
        ),
        "and the kernel admits it: {:?}",
        readmission.readmitted()[5].outcome()
    );
}

#[test]
fn one_static_definition_at_two_instances_records_two_certificates()
{
    // def Pair : Type -> Type = \X. El X * El X ;
    // def both : Type = El (Pair Integer) * El (Pair String) ;
    // def twice : Type = El (Pair Integer) * El (Pair Integer) ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let operator_type = arena.value_type_static_pi(small, small);
    let operator = pair_operator(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let integer_code = arena.value_quote(integer);
    let again = arena.value_quote(integer);
    let string_code = arena.value_quote(string);
    let pair = arena.value_constant(ConstantIndex::from(0_usize));
    let at_integer = arena.value_static_application(pair, integer_code);
    let at_string = arena.value_static_application(pair, string_code);
    let at_again = arena.value_static_application(pair, again);
    let first = arena.value_type_element(at_integer, Level::zero());
    let second = arena.value_type_element(at_string, Level::zero());
    let repeated = arena.value_type_element(at_again, Level::zero());
    let both = arena.value_type_product(&[first, second]);
    let twice = arena.value_type_product(&[first, repeated]);
    let both_code = arena.value_quote(both);
    let twice_code = arena.value_quote(twice);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(
            At(0),
            Maybe::Present(operator_type),
            Maybe::Present(operator),
        ),
        declaration(At(1), Maybe::Present(small), Maybe::Present(both_code)),
        declaration(At(2), Maybe::Present(small), Maybe::Present(twice_code)),
    ]);
    for judged in report.judged() {
        assert!(
            matches!(judged.verdict(), Verdict::Checked { .. }),
            "every declaration checks: {:?}",
            judged.verdict()
        );
    }
    let [ref operator_entry, ref both_entry, ref twice_entry] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert_eq!(
        operator_entry.outcome(),
        &Outcome::Static,
        "the operator itself crosses as nothing"
    );
    assert_eq!(
        steps(both_entry),
        [convertible(At(0)), convertible(At(0))],
        "two instances of one definition each record a certificate naming it: {:?}",
        both_entry.outcome()
    );
    let [ref at_one, ref at_other] = *both_entry.certificates()
    else {
        panic!("two certificates");
    };
    assert_ne!(
        at_one.redex(),
        at_other.redex(),
        "each certificate is addressed by its own instance"
    );
    assert_eq!(
        steps(twice_entry),
        [convertible(At(0))],
        "one instance written twice is certified once, whatever its nodes"
    );
    for entry in [both_entry, twice_entry] {
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "{:?} is admitted",
            entry.outcome()
        );
    }
}

#[test]
fn a_rigid_static_instance_crosses_as_a_kernel_application()
{
    // def G : Type -> Type ;
    // def applied : Type = G Integer ;
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let operator_type = arena.value_type_static_pi(small, small);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_code = arena.value_quote(integer);
    let opaque = arena.value_constant(ConstantIndex::from(0_usize));
    let applied = arena.value_static_application(opaque, integer_code);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(operator_type), HOLE),
        declaration(At(1), Maybe::Present(small), Maybe::Present(applied)),
    ]);
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "an instance of an opaque operator checks"
    );
    let [ref axiom, ref instance] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert!(
        matches!(*axiom.outcome(), Outcome::Assumed { .. })
            && matches!(*instance.outcome(), Outcome::Defined { .. }),
        "the opaque operator crosses as an axiom and its instance as a definition: {:?}",
        instance.outcome()
    );
    assert!(
        instance.certificates().is_empty(),
        "nothing unfolds at a rigid head"
    );
    let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
    let body = artifact
        .declarations()
        .iter()
        .find_map(|marked| match *marked.declaration().content() {
            DeclarationContent::Def { body, .. } => Some(body),
            DeclarationContent::Data { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::AbstractType { .. } => None,
        })
        .unwrap();
    let Some(&KernelValue::StaticApplication(head, argument)) = artifact.arena().value(body)
    else {
        panic!("the instance crosses as the kernel's static application");
    };
    assert_eq!(
        artifact.arena().value(head),
        Some(&KernelValue::Constant(crossed_at(&readmission, At(0)))),
        "its head is the axiom's position"
    );
    let Some(&KernelValue::Quote(quoted)) = artifact.arena().value(argument)
    else {
        panic!("its argument is a quote");
    };
    assert_eq!(
        artifact.arena().value_type(quoted),
        Some(&KernelValueType::Base(BaseType::Integer)),
        "of the atom it was applied at"
    );
}

#[test]
fn a_static_lambda_crosses_only_as_a_closed_operator()
{
    let mut arena = CoreArena::new();
    let closed = pair_operator(&mut arena);
    let free = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let open = arena.value_static_lambda(free);
    let positions = Positions::default();
    let lifts = alloc::collections::BTreeMap::new();
    let definitions = alloc::collections::BTreeMap::new();
    let source = Source {
        lifts: &lifts,
        funexts: &BTreeMap::new(),
        equivalences: &BTreeMap::new(),
        flows: &BTreeMap::new(),
        directed: &BTreeMap::new(),
        reflexivities: &BTreeMap::new(),
        relations: &BTreeMap::new(),
        laws: &BTreeMap::new(),
        natives: &BTreeMap::new(),
        definitions: &definitions,
    };
    let base = ConstantIndex::from(3_usize);
    let mut erasure = Erasure::new(&mut arena, source, &positions, base);
    let refused = |at: ValueId| {
        Err(Refusal::OutOfFragment {
            at: CoreNode::Term(TermNode::Value(at)),
            former: UnadmittedFormer::StaticLambda,
        })
    };
    assert_eq!(
        erasure.abstraction(closed),
        refused(closed),
        "a static normal form holds no lambda"
    );
    erasure.mode = Reading::Verbatim;
    assert_eq!(
        erasure.abstraction(closed),
        Ok(base),
        "a closed lambda read verbatim is the first operator, numbered from the base"
    );
    assert_eq!(
        erasure.abstraction(closed),
        Ok(base),
        "and keeps its number when met again"
    );
    assert_eq!(
        erasure.abstraction(open),
        refused(open),
        "a lambda reaching a binder outside itself stands for no closed operator"
    );
}

#[test]
fn every_checked_static_declaration_is_readmitted()
{
    // def RawRelMonad : (Type -> Type[-]) -> Type -> Type -> Type ;
    // def RawRelMonad = \T. \A. \B.
    //   U (El A -> T A) * U (U (T A) -> U (El A -> T B) -> T B) ;
    // def Witness : Type = RawRelMonad (\X. F (El X * El X)) Integer Integer ;
    // def Elided : Type =
    //   U (Integer -> F (Integer * Integer))
    //   * U (U (F (Integer * Integer)) -> U (Integer -> F (Integer * Integer)) -> F
    //     (Integer * Integer)) ;
    // def unit_and_bind : El Witness ;
    //
    // The kernel is the oracle: the instance crosses as the same content
    // the elided spelling does, every step it took replays, and a hole at
    // its decode is an axiom of the normal form.
    let mut arena = CoreArena::new();
    let small = small(&mut arena);
    let negative = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let family_type = arena.value_type_static_pi(small, negative);
    let last = arena.value_type_static_pi(small, small);
    let middle = arena.value_type_static_pi(small, last);
    let monad_type = arena.value_type_static_pi(family_type, middle);
    let result = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let carrier = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let family = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let element = arena.value_type_element(carrier, Level::zero());
    let at_carrier = arena.value_static_application(family, carrier);
    let at_result = arena.value_static_application(family, result);
    let acts_on_carrier = arena.comp_type_element(at_carrier, Level::zero());
    let acts_on_result = arena.comp_type_element(at_result, Level::zero());
    let unit_arrow = arena.comp_type_arrow(element, acts_on_carrier);
    let unit_thunk = arena.value_type_thunk(unit_arrow);
    let suspended_carrier = arena.value_type_thunk(acts_on_carrier);
    let continuation_arrow = arena.comp_type_arrow(element, acts_on_result);
    let continuation = arena.value_type_thunk(continuation_arrow);
    let bind_tail = arena.comp_type_arrow(continuation, acts_on_result);
    let bind_arrow = arena.comp_type_arrow(suspended_carrier, bind_tail);
    let bind_thunk = arena.value_type_thunk(bind_arrow);
    let monad_product = arena.value_type_product(&[unit_thunk, bind_thunk]);
    let monad_code = arena.value_quote(monad_product);
    let over_result = arena.value_static_lambda(monad_code);
    let over_carrier = arena.value_static_lambda(over_result);
    let monad = arena.value_static_lambda(over_carrier);

    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound, Level::zero());
    let squared = arena.value_type_product(&[decoded, decoded]);
    let returns_squared = arena.comp_type_returner(squared);
    let squared_code = arena.value_quote_computation(returns_squared);
    let squaring = arena.value_static_lambda(squared_code);
    let integer = arena.value_type_base(BaseType::Integer);
    let carrier_code = arena.value_quote(integer);
    let result_code = arena.value_quote(integer);
    let head = arena.value_constant(ConstantIndex::from(0_usize));
    let at_family = arena.value_static_application(head, squaring);
    let at_carrier_code = arena.value_static_application(at_family, carrier_code);
    let witness = arena.value_static_application(at_carrier_code, result_code);

    let pair = arena.value_type_product(&[integer, integer]);
    let returns_pair = arena.comp_type_returner(pair);
    let unit_spelled = arena.comp_type_arrow(integer, returns_pair);
    let unit_spelled = arena.value_type_thunk(unit_spelled);
    let suspended_pair = arena.value_type_thunk(returns_pair);
    let continuation_spelled = arena.comp_type_arrow(integer, returns_pair);
    let continuation_spelled = arena.value_type_thunk(continuation_spelled);
    let bind_tail_spelled = arena.comp_type_arrow(continuation_spelled, returns_pair);
    let bind_spelled = arena.comp_type_arrow(suspended_pair, bind_tail_spelled);
    let bind_spelled = arena.value_type_thunk(bind_spelled);
    let elided_product = arena.value_type_product(&[unit_spelled, bind_spelled]);
    let elided = arena.value_quote(elided_product);
    let witness_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let decoded_witness = arena.value_type_element(witness_constant, Level::zero());

    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), Maybe::Present(monad_type), Maybe::Present(monad)),
        declaration(At(1), Maybe::Present(small), Maybe::Present(witness)),
        declaration(At(2), Maybe::Present(small), Maybe::Present(elided)),
        declaration(At(3), Maybe::Present(decoded_witness), HOLE),
    ]);
    assert!(
        matches!(
            report
                .judged()
                .iter()
                .map(Judged::verdict)
                .collect::<Vec<_>>()
                .as_slice(),
            [
                Verdict::Checked { .. },
                Verdict::Checked { .. },
                Verdict::Checked { .. },
                Verdict::Owed(_),
            ]
        ),
        "the operator, its instance and the elided spelling check, and the hole is owed: \
             {:?}",
        report
            .judged()
            .iter()
            .map(Judged::verdict)
            .collect::<Vec<_>>()
    );
    let [ref operator, ref instance, ref spelled, ref hole] = *readmission.readmitted()
    else {
        panic!("one outcome per declaration");
    };
    assert_eq!(
        operator.outcome(),
        &Outcome::Static,
        "the operator stays on the checker's side"
    );
    assert!(
        matches!(*instance.outcome(), Outcome::Defined { .. })
            && matches!(*spelled.outcome(), Outcome::Defined { .. })
            && matches!(*hole.outcome(), Outcome::Assumed { .. }),
        "the instance and the spelling cross as definitions and the hole as an axiom: \
             {:?}",
        readmission.readmitted()
    );
    assert!(
        matches!(steps(instance).first(), Some(&(Unfolded::Definition(position), _))
                if position == ConstantIndex::from(0_usize)),
        "the instance unfolds the operator first: {:?}",
        steps(instance)
    );
    for entry in [instance, hole] {
        assert!(
            !entry.certificates().is_empty()
                && entry
                    .certificates()
                    .iter()
                    .all(|replayed| replayed.verdict() == KernelVerdict::Convertible),
            "every step the kernel replays converts: {:?}",
            steps(entry)
        );
    }
    let bodies = exported_bodies(&readmission);
    assert_eq!(
        bodies.len(),
        2_usize,
        "the instance and the spelling are the definitions that cross"
    );
    assert_eq!(
        bodies.first(),
        bodies.last(),
        "the instance crosses as exactly the content the elided spelling writes"
    );
}

/// One generated code declaration: which code it defines, the level the
/// code is built at, how far above the code's own universe a value code is
/// declared, and which earlier code a reference names.
#[derive(Clone, Copy, Debug)]
struct CodeRecipe
{
    /// The shape of the code: an atom's quote, a universe's of either sort,
    /// a thunk type's, a returner's, an arrow's, or an earlier code.
    shape: u8,
    /// The level the code's universe is built at.
    level: u8,
    /// How many levels above its own universe a value code is declared.
    bump: u8,
    /// The earlier code a reference names, counted round.
    earlier: u8,
}

/// The code recipe strategy.
///
/// # Specification
/// - requires: nothing.
/// - ensures: recipes choose one of seven shapes, levels below three, bumps
///   below two and an arbitrary byte selecting an earlier code.
/// - panics: none.
/// - executable: none — constructing a strategy cannot observe its future draws
///   or shrink tree; generated recipes are checked by the builder.
///
/// # Adequacy
/// - hypothesis: L1 — one to five generated recipes build checked modules and
///   replayable certificates; wrong sort, natural level or earlier-reference
///   policy changes acceptance or replay. Sampling is not an exhaustive claim
///   about random draws or shrinking.
/// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
/// - witness: `bridge::tests::every_readmission_certificate_replays`
fn code_recipe() -> impl proptest::strategy::Strategy<Value = CodeRecipe>
{
    use proptest::prelude::any;
    use proptest::strategy::Strategy as _;
    (0_u8 .. 7_u8, 0_u8 .. 3_u8, 0_u8 .. 2_u8, any::<u8>()).prop_map(
        |(shape, level, bump, earlier)| CodeRecipe {
            shape,
            level,
            bump,
            earlier,
        },
    )
}

/// The module `recipes` build: one code declaration per recipe, each
/// declared at the universe of its sort, a value code at or above its own
/// level; then one declaration over each code's decode — a value code's as
/// the identity on it, a computation code's as an owed suspension of it.
/// The second list is the positions of the declarations over decodes.
///
/// # Specification
/// - requires: fewer than six recipes, each with shape below seven, level below
///   three and bump below two.
/// - ensures: one declared code per recipe followed by one declaration using
///   each decode, consecutively numbered and located by the returned use
///   positions; every declared type and present body resolves.
/// - panics: none within the bounded recipe domain.
///
/// # Adequacy
/// - hypothesis: L1 — one to five bounded code recipes expose complete
///   readmission, exact axioms and convertible certificates; wrong decode
///   family, numbering, level or reference changes these observations.
/// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
/// - witness: `bridge::tests::every_readmission_certificate_replays`
#[spec(
        requires: recipes.len() < 6 && recipes.iter().all(|recipe| recipe.shape < 7 && recipe.level < 3 && recipe.bump < 2),
        ensures: |ret| ret.0.len() == recipes.len().saturating_mul(2) && ret.1.len() == recipes.len()
            && ret.1.iter().enumerate().all(|(index,at)| at.0 == recipes.len().saturating_add(index))
            && ret.0.iter().enumerate().all(|(index,declaration)| declaration.constant() == ConstantIndex::from(index)
                && match declaration.content() {
                    &crate::DeclarationContent::Value {signature:Maybe::Present(ty),body} => arena.value_type(ty).is_some() && match body { Maybe::Present(body) => arena.value(body).is_some(), Maybe::Absent(_) => true },
                    &crate::DeclarationContent::Value { .. } | &crate::DeclarationContent::Data(_) | &crate::DeclarationContent::Abstract(_) => false,
                }),
    )]
fn universe_module(
    arena: &mut CoreArena,
    recipes: &[CodeRecipe],
) -> (Vec<Declaration>, Vec<At>)
{
    let level_at = |n: u8| Level::constant(LevelConstant::from(u64::from(n)));
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let mut module = Vec::new();
    let mut codes: Vec<(GroundSort, u8)> = Vec::new();
    for recipe in recipes {
        let own = level_at(recipe.level);
        let above = recipe.level.saturating_add(1_u8);
        let (code, sort, natural) = match recipe.shape {
            1_u8 => {
                let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), own);
                (arena.value_quote(universe), GroundSort::Value, above)
            },
            2_u8 => {
                let universe =
                    arena.value_type_universe(Sort::Ground(GroundSort::Computation), own);
                (arena.value_quote(universe), GroundSort::Value, above)
            },
            3_u8 => {
                let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), own);
                let returner = arena.comp_type_returner(universe);
                let thunk = arena.value_type_thunk(returner);
                (arena.value_quote(thunk), GroundSort::Value, above)
            },
            4_u8 => (
                arena.value_quote_computation(returns_integer),
                GroundSort::Computation,
                0_u8,
            ),
            5_u8 => {
                let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), own);
                let returner = arena.comp_type_returner(universe);
                let arrow = arena.comp_type_arrow(integer, returner);
                (
                    arena.value_quote_computation(arrow),
                    GroundSort::Computation,
                    above,
                )
            },
            6_u8 if !codes.is_empty() => {
                let position = usize::from(recipe.earlier)
                    .checked_rem(codes.len())
                    .expect("an earlier code exists");
                let (sort, natural) = codes[position];
                (
                    arena.value_constant(ConstantIndex::from(position)),
                    sort,
                    natural,
                )
            },
            _ => (arena.value_quote(integer), GroundSort::Value, 0_u8),
        };
        let declared_level = match sort {
            GroundSort::Value => natural.saturating_add(recipe.bump),
            GroundSort::Computation => natural,
        };
        let universe = arena.value_type_universe(Sort::Ground(sort), level_at(declared_level));
        module.push(declaration(
            At(module.len()),
            Maybe::Present(universe),
            Maybe::Present(code),
        ));
        codes.push((sort, declared_level));
    }
    let mut uses = Vec::new();
    for (position, &(sort, declared_level)) in codes.iter().enumerate() {
        let name = arena.value_constant(ConstantIndex::from(position));
        uses.push(At(module.len()));
        match sort {
            GroundSort::Value => {
                let decoded = arena.value_type_element(name, level_at(declared_level));
                let returner = arena.comp_type_returner(decoded);
                let arrow = arena.comp_type_arrow(decoded, returner);
                let suspended = arena.value_type_thunk(arrow);
                let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let returned = arena.computation_return(bound);
                let lambda = arena.computation_lambda(returned);
                let thunk = arena.value_thunk(lambda);
                module.push(declaration(
                    At(module.len()),
                    Maybe::Present(suspended),
                    Maybe::Present(thunk),
                ));
            },
            GroundSort::Computation => {
                let decoded = arena.comp_type_element(name, level_at(declared_level));
                let suspended = arena.value_type_thunk(decoded);
                module.push(declaration(
                    At(module.len()),
                    Maybe::Present(suspended),
                    HOLE,
                ));
            },
        }
    }
    (module, uses)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn every_fixture_the_checker_accepts_is_readmitted(
        typed in typed_recipe(),
        free in term_recipe(),
    )
    {
        // The well-typed set: every constant owed, every term declared at
        // its type — a computation as its thunk — and every synthesising
        // value declared unsigned as well.
        let mut arena = CoreArena::new();
        let terms = typed.build(&mut arena);
        let mut module = Vec::new();
        for &declared in &terms.constants {
            module.push(declaration(At(module.len()), Maybe::Present(declared), HOLE));
        }
        for &(value, declared, mode) in &terms.values {
            module.push(declaration(At(module.len()), Maybe::Present(declared), Maybe::Present(value)));
            if mode == Mode::Synthesising {
                module.push(declaration(At(module.len()), UNSIGNED, Maybe::Present(value)));
            }
        }
        for &(comp, comp_type, _) in &terms.comps {
            let thunk = arena.value_thunk(comp);
            let suspended = arena.value_type_thunk(comp_type);
            module.push(declaration(At(module.len()), Maybe::Present(suspended), Maybe::Present(thunk)));
        }
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        prop_assert!(
            report.judged().iter().all(|judged| !matches!(judged.verdict(), Verdict::Refused(_))),
            "the well-typed set is accepted whole"
        );
        assert_crossed(&report, &readmission)?;

        // The free set: six owed constants, every value declared unsigned,
        // and every computation that synthesises declared as its thunk.
        let mut arena = CoreArena::new();
        let terms = free.build(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let unit_type = arena.value_type_unit();
        let returns_integer = arena.comp_type_returner(integer);
        let returns_string = arena.comp_type_returner(string);
        let suspended = arena.value_type_thunk(returns_integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let function = arena.value_type_thunk(arrow);
        let unit_arrow = arena.comp_type_arrow(unit_type, returns_string);
        let unit_function = arena.value_type_thunk(unit_arrow);
        let constants = [integer, string, unit_type, suspended, function, unit_function];
        let synthesised: Vec<_> = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            seed(&mut context, &constants);
            terms
                .comps
                .iter()
                .filter_map(|&comp| match synthesise_comp(&mut context, comp) {
                    | Ok(found) => Some((comp, found.produced().id())),
                    | Err(_) => None,
                })
                .collect()
        };
        let mut module = Vec::new();
        for &declared in &constants {
            module.push(declaration(At(module.len()), Maybe::Present(declared), HOLE));
        }
        for &value in &terms.values {
            module.push(declaration(At(module.len()), UNSIGNED, Maybe::Present(value)));
        }
        for (comp, comp_type) in synthesised {
            let thunk = arena.value_thunk(comp);
            let suspended = arena.value_type_thunk(comp_type);
            module.push(declaration(At(module.len()), Maybe::Present(suspended), Maybe::Present(thunk)));
        }
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        assert_crossed(&report, &readmission)?;
    }

    #[test]
    fn every_checked_function_definition_is_readmitted(
        recipes in proptest::collection::vec(function_recipe(), 1 .. 4),
    )
    {
        // Every constant a statement forces owed first, then every
        // function declared at its type: the shape a lowered function
        // tail takes, well or ill typed by the value it returns.
        let mut arena = CoreArena::new();
        let mut constants = Vec::new();
        let functions: Vec<_> = recipes
            .iter()
            .map(|recipe| recipe.build(&mut arena, &mut constants))
            .collect();
        let mut module = Vec::new();
        for &declared in &constants {
            module.push(declaration(At(module.len()), Maybe::Present(declared), HOLE));
        }
        for function in &functions {
            module.push(declaration(
                At(module.len()),
                Maybe::Present(function.declared),
                Maybe::Present(function.body),
            ));
        }
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        for (recipe, judged) in recipes.iter().zip(&report.judged()[constants.len()..]) {
            prop_assert_eq!(
                matches!(judged.verdict(), Verdict::Checked { .. }),
                recipe.typing() == Typing::WellTyped,
                "the checker accepts a function exactly when it is well typed: {:?}",
                judged.verdict()
            );
        }
        assert_crossed(&report, &readmission)?;
    }

    #[test]
    fn every_checked_universe_declaration_is_readmitted(
        recipes in proptest::collection::vec(code_recipe(), 1 .. 6),
    )
    {
        let mut arena = CoreArena::new();
        let (module, _) = universe_module(&mut arena, &recipes);
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        prop_assert!(
            report.judged().iter().all(|judged| !matches!(judged.verdict(), Verdict::Refused(_))),
            "every code, every reference and every decode is accepted: {:?}",
            report.judged().iter().map(Judged::verdict).collect::<Vec<_>>()
        );
        assert_crossed(&report, &readmission)?;
    }

    #[test]
    fn every_readmission_certificate_replays(
        recipes in proptest::collection::vec(code_recipe(), 1 .. 6),
    )
    {
        let mut arena = CoreArena::new();
        let (module, uses) = universe_module(&mut arena, &recipes);
        let (_, readmission) = judge_and_readmit(&mut arena, &module);
        for position in uses {
            let entry = &readmission.readmitted()[position.0];
            prop_assert!(
                !entry.certificates().is_empty(),
                "a decode of a defined code unfolds at export"
            );
            for certificate in entry.certificates() {
                prop_assert_eq!(
                    certificate.verdict(),
                    KernelVerdict::Convertible,
                    "the kernel re-derives the unfolding of {:?}",
                    certificate.unfolded()
                );
            }
        }
    }
}
