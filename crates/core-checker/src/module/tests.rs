use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::Purity;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::SealExtent;
use quenchant_shape::shape::Maybe;

use super::Verdict;
use super::check_declaration;
use super::check_module;
use super::type_module;
use crate::context::Atom;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::context::Formations;
use crate::conversion::ConversionCount;
use crate::declaration::AbstractType;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::failure::FrameRole;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::fixture::integer_literal;
use crate::fixture::text_literal;
use crate::nested::Nesting;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::seal::ComponentOrdinal;
use crate::seal::SealSite;
use crate::seal::SealingSite;

/// An admission position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

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
        OriginToken::from(position.0.checked_add(100).unwrap()),
    )
}

/// No declared type.
const UNSIGNED: Maybe<ValueTypeId, signature::Absent> = Maybe::Absent(signature::Absent::Unsigned);

/// No body.
const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

#[test]
fn each_combination_of_halves_gets_its_verdict()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let Verdict::Checked {
        declared,
        body,
        evidence,
    } = check_declaration(
        &mut context,
        &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
    )
    else {
        panic!("a signature and a body check");
    };
    assert_eq!(
        (declared.id(), body),
        (integer, zero),
        "the verdict carries the declared type and the body it checked"
    );
    assert_eq!(
        evidence.conversions(),
        ConversionCount::from(1_usize),
        "the literal crossed the value bridge once"
    );
    let Verdict::Owed(entry) = check_declaration(
        &mut context,
        &declaration(At(1), Maybe::Present(integer), HOLE),
    )
    else {
        panic!("a signature over a hole is owed");
    };
    assert_eq!(
        (
            entry.absence().constant(),
            entry.absence().declared().id(),
            entry.absence().origin()
        ),
        (
            ConstantIndex::from(1_usize),
            integer,
            OriginToken::from(101_usize)
        ),
        "the hole in checking position absorbs the declared type and owes it"
    );
    let Verdict::Synthesised { body, synthesised } = check_declaration(
        &mut context,
        &declaration(At(2), UNSIGNED, Maybe::Present(zero)),
    )
    else {
        panic!("a body alone synthesises");
    };
    assert_eq!(
        (body, synthesised.produced()),
        (zero, context.atom(Atom::Integer)),
        "the unsigned literal synthesises its atom, and the verdict carries the body"
    );
    assert_eq!(
        check_declaration(&mut context, &declaration(At(3), UNSIGNED, HOLE)),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(ConstantIndex::from(3_usize)),
        }),
        "a hole in synthesis position has nothing to absorb and is refused"
    );
}

#[test]
fn an_admission_out_of_order_is_refused()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(1), UNSIGNED, Maybe::Present(zero))
            ),
            Verdict::Synthesised { .. }
        ),
        "the first admission may take any position"
    );
    for repeated in [1_usize, 0_usize] {
        let verdict = check_declaration(
            &mut context,
            &declaration(At(repeated), UNSIGNED, Maybe::Present(zero)),
        );
        assert_eq!(
            verdict,
            Verdict::Refused(CheckRefusal::AdmissionOrder {
                constant: ConstantIndex::from(repeated),
                admitted: ConstantIndex::from(1_usize),
            }),
            "a position not above every admitted one is refused with both positions"
        );
        let Verdict::Refused(refusal) = verdict
        else {
            panic!("refused above");
        };
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "an admission out of order is the producer's fault"
        );
    }
}

#[test]
fn a_declaration_cannot_read_its_own_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let itself = arena.value_constant(ConstantIndex::from(0_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let verdict = check_declaration(
        &mut context,
        &declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
    );
    assert_eq!(
        verdict,
        Verdict::Refused(CheckRefusal::UnknownConstant {
            at: itself,
            constant: ConstantIndex::from(0_usize),
        }),
        "a body sees only the declarations strictly before it, so self-reference finds no type"
    );
    let Verdict::Refused(refusal) = verdict
    else {
        panic!("refused above");
    };
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "an unknown constant is the author's"
    );
}

#[test]
fn a_refused_signed_body_still_supplies_its_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(text_literal());
    let earlier = arena.value_constant(ConstantIndex::from(0_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(0), Maybe::Present(integer), Maybe::Present(text))
            ),
            Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
        ),
        "the text does not have the declared integer type"
    );
    let Verdict::Synthesised { synthesised, .. } = check_declaration(
        &mut context,
        &declaration(At(1), UNSIGNED, Maybe::Present(earlier)),
    )
    else {
        panic!("the reference synthesises");
    };
    assert_eq!(
        synthesised.produced().id(),
        integer,
        "the declared type is the contract a later reference reads, whatever the body did"
    );
}

#[test]
fn a_body_that_synthesised_nothing_supplies_no_type()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let earlier = arena.value_constant(ConstantIndex::from(0_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(0), UNSIGNED, Maybe::Present(thunk))
        ),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Thunk(thunk),
        }),
        "an unsigned thunk does not synthesise"
    );
    assert_eq!(
        context.signature(ConstantIndex::from(0_usize)),
        Maybe::Absent(crate::context::signature_table::Absent::Untyped),
        "the refused body supplied no type"
    );
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(1), UNSIGNED, Maybe::Present(earlier))
        ),
        Verdict::Refused(CheckRefusal::UnknownConstant {
            at: earlier,
            constant: ConstantIndex::from(0_usize),
        }),
        "a reference to it finds no type"
    );
}

#[test]
fn a_later_declaration_reads_an_earlier_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let thunk_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let suspended = arena.value_constant(ConstantIndex::from(0_usize));
    let owed = arena.value_constant(ConstantIndex::from(1_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(thunk_type), Maybe::Present(thunk)),
        declaration(At(1), Maybe::Present(integer), HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(suspended)),
        declaration(At(3), Maybe::Present(integer), Maybe::Present(owed)),
    ];
    let report = check_module(&mut context, &module);
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    assert!(
        matches!(verdicts[2], Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == thunk_type),
        "a reference synthesises the exact type its declaration supplied"
    );
    assert!(
        matches!(verdicts[3], Verdict::Checked { .. }),
        "an owed declaration supplies its declared type to later references"
    );
    assert_eq!(
        context
            .signature(ConstantIndex::from(1_usize))
            .map(crate::formation::FormedValueType::id),
        Maybe::Present(integer),
        "the table holds the owed declaration's type"
    );
}

#[test]
fn an_ascription_keeps_the_endpoints_it_related()
{
    // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
    // def j : U (Integer -> F Integer) = k ;
    // def given : Path(U (…), thunk { force j }, k) = here(k) ;
    // def law : Path(U (…), k, k) = given ;
    // def again : Path(U (…), thunk { force j }, k) = given ;
    // `law`'s ascription relates `thunk { force j }` to `k`, unfolding `j`
    // under the thunk; `again`'s endpoints are the same syntax.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let [k, j, given] = [0_usize, 1, 2].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let forced = arena.computation_force(j);
    let delayed = arena.value_thunk(forced);
    let stated = arena.value_type_path(function, delayed, k);
    let diagonal = arena.value_type_path(function, k, k);
    let here = arena.value_here(k);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
        declaration(At(1), Maybe::Present(function), Maybe::Present(k)),
        declaration(At(2), Maybe::Present(stated), Maybe::Present(here)),
        declaration(At(3), Maybe::Present(diagonal), Maybe::Present(given)),
        declaration(At(4), Maybe::Present(stated), Maybe::Present(given)),
    ];
    let report = check_module(&mut context, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "every declaration checks: {:?}",
        report.judged()
    );
    assert_eq!(
        report.relations().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(3_usize)],
        "only the ascription whose endpoints differ keeps a pair"
    );
    let relations = report
        .relations()
        .get(&ConstantIndex::from(3_usize))
        .expect("the law's pairs");
    let [ref relation] = *relations.as_slice()
    else {
        panic!("one pair of endpoints differs: {relations:?}");
    };
    assert_eq!(
        (relation.left(), relation.right()),
        (delayed, k),
        "the pair is the synthesised endpoint against the declared one"
    );
    assert!(
        relation.decisions().iter().any(|decision| matches!(
            decision,
            gandr_kernel_conversion_trace::ConversionDecision::Unfold { .. }
        )),
        "the derivation names the unfoldings the kernel replays"
    );
}

#[test]
fn a_refusal_does_not_stop_the_run()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(2), Maybe::Present(integer), HOLE),
        declaration(At(3), UNSIGNED, HOLE),
        declaration(At(4), UNSIGNED, Maybe::Present(zero)),
    ];
    let report = check_module(&mut context, &module);
    let judged = report.judged();
    for (entry, offered) in judged.iter().zip(&module) {
        assert_eq!(
            (entry.constant(), entry.origin()),
            (offered.constant(), offered.origin()),
            "each verdict echoes its declaration's position and origin, in order"
        );
    }
    let [
        ref mismatched,
        ref checked,
        ref owed,
        ref unsigned_hole,
        ref synthesised,
    ] = *judged
    else {
        panic!("every declaration gets a verdict");
    };
    assert!(
        matches!(
            mismatched.verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "the first declaration is refused"
    );
    assert!(
        matches!(checked.verdict(), Verdict::Checked { .. }),
        "the next is judged on its own"
    );
    assert!(
        matches!(owed.verdict(), Verdict::Owed(_)),
        "the signed hole is owed"
    );
    assert!(
        matches!(
            unsigned_hole.verdict(),
            Verdict::Refused(CheckRefusal::NotSynthesisable { .. })
        ),
        "the unsigned hole is refused"
    );
    assert!(
        matches!(synthesised.verdict(), Verdict::Synthesised { .. }),
        "and the run goes on past it"
    );
}

#[test]
fn every_owed_hole_enters_the_ledger_in_order()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(string), HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(zero)),
        declaration(At(3), Maybe::Present(integer), HOLE),
    ];
    let report = check_module(&mut context, &module);
    let owed: Vec<_> = report
        .ledger()
        .entries()
        .iter()
        .map(|entry| {
            let absence = entry.absence();
            (
                absence.constant(),
                absence.declared().id(),
                absence.origin(),
            )
        })
        .collect();
    assert_eq!(
        owed,
        [
            (
                ConstantIndex::from(1_usize),
                string,
                OriginToken::from(101_usize)
            ),
            (
                ConstantIndex::from(3_usize),
                integer,
                OriginToken::from(103_usize)
            ),
        ],
        "the ledger holds each owed hole, in module order"
    );
    assert_eq!(
        usize::from(report.ledger().count()),
        2_usize,
        "the count is the holes owed"
    );
}

#[test]
fn a_refusal_never_enters_the_ledger()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unformed = arena.value_type_base(BaseType::Numeric);
    let text = arena.value_literal(text_literal());
    let unknown = arena.value_constant(ConstantIndex::from(9_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), UNSIGNED, HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(unknown)),
        declaration(At(3), Maybe::Present(unformed), HOLE),
        declaration(At(3), Maybe::Present(integer), HOLE),
    ];
    let report = check_module(&mut context, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|entry| matches!(entry.verdict(), Verdict::Refused(_))),
        "every declaration of this module is refused"
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(unformed)),
            former: UnadmittedFormer::NumericAtom,
        }),
        "a signed hole under an unformed signature is refused, not owed"
    );
    assert_eq!(
        usize::from(report.ledger().count()),
        0_usize,
        "a refusal of any class leaves the ledger empty"
    );
}

#[test]
fn a_refused_body_keeps_the_rules_it_was_refused_inside()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unformed = arena.value_type_base(BaseType::Numeric);
    let itself = arena.value_constant(ConstantIndex::from(0_usize));
    let text = arena.value_literal(text_literal());
    let zero = arena.value_literal(integer_literal());
    let forced = arena.computation_force(zero);
    let thunk = arena.value_thunk(forced);
    let pair = arena.value_tuple(&[zero, thunk]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
        declaration(At(1), UNSIGNED, Maybe::Present(text)),
        declaration(At(2), Maybe::Present(unformed), Maybe::Present(text)),
        declaration(At(3), UNSIGNED, Maybe::Present(pair)),
    ];
    let report = check_module(&mut context, &module);
    assert_eq!(
        report.failures().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(0_usize), ConstantIndex::from(3_usize)],
        "the two refused bodies keep their failures; the accepted body and \
             the body under an unformed signature, never run, keep none"
    );
    let reference = &report.failures()[&ConstantIndex::from(0_usize)];
    assert_eq!(
        reference.refusal(),
        CheckRefusal::UnknownConstant {
            at: itself,
            constant: ConstantIndex::from(0_usize),
        },
        "the self-reference is refused before its type enters the table"
    );
    let [ref bridge] = *reference.obligations()
    else {
        panic!("one rule waits on the self-reference: {reference:?}");
    };
    assert_eq!(
        (bridge.role(), bridge.at()),
        (
            FrameRole::ValueBridge,
            CoreNode::Term(TermNode::Value(itself))
        ),
        "the check of the body waits on its synthesis, to cross the bridge"
    );
    assert!(
        matches!(bridge.expected(), Maybe::Present(TypeNode::Value(_))),
        "the body was checked against its declared type"
    );
    let synthesis = &report.failures()[&ConstantIndex::from(3_usize)];
    assert_eq!(
        synthesis
            .obligations()
            .iter()
            .map(|obligation| (obligation.role(), obligation.at()))
            .collect::<Vec<_>>(),
        [
            (
                FrameRole::NativeTuple,
                CoreNode::Term(TermNode::Value(pair))
            ),
            (
                FrameRole::NativeCollect,
                CoreNode::Term(TermNode::Value(pair))
            ),
        ],
        "the pair waits on its second component's type, outermost first"
    );
    assert_eq!(
        synthesis.pursuit(),
        Pursuit::new(
            CoreNode::Term(TermNode::Value(thunk)),
            Maybe::Absent(judged::Absent::Synthesised),
            Stage::Starting,
        ),
        "the thunk, which cannot synthesise, is the goal the refusal met"
    );
}

#[test]
fn a_typed_module_keeps_each_judged_body_s_term_types()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[integer, integer]);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let pair = arena.value_tuple(&[zero, text]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(product), Maybe::Present(pair)),
        declaration(At(2), Maybe::Present(integer), HOLE),
    ];
    let typed = type_module(&mut context, &module);
    assert_eq!(
        typed.keys().copied().collect::<Vec<_>>(),
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(2_usize)
        ],
        "both judged bodies are typed, and the hole's signature"
    );
    let owed = &typed[&ConstantIndex::from(2_usize)];
    assert!(
        owed.typings().is_empty()
            && owed
                .formed()
                .iter()
                .any(|formed| formed.ty == TypeNode::Value(integer)),
        "the hole judges no term; its signature is formed: {owed:?}"
    );
    let accepted = typed[&ConstantIndex::from(0_usize)].typings();
    assert_eq!(
        accepted
            .iter()
            .map(|typing| typing.term)
            .collect::<Vec<_>>(),
        [TermNode::Value(zero)],
        "the literal body is its only term"
    );
    let refused = &typed[&ConstantIndex::from(1_usize)];
    assert!(
        refused
            .typings()
            .iter()
            .any(|typing| typing.term == TermNode::Value(text)),
        "the refused component is typed where it was recovered"
    );
    assert_eq!(
        refused.typings().last().map(|typing| typing.term),
        Some(TermNode::Value(pair)),
        "the refused body itself finishes last"
    );
    assert_eq!(
        refused.marks().len(),
        1_usize,
        "the text component is the one mark"
    );
}

/// A typed run keys a declaration exactly when it formed or judged something,
/// refused or not: a formed data declaration and one refused at a field keep
/// the kind they formed, a signature refused at its second component keeps
/// the first, and a signature refused before forming anything is not keyed.
#[test]
fn a_typed_module_keys_what_each_run_formed()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let dangling = crate::fixture::dangling_value_type();
    let partial = arena.value_type_product(&[integer, dangling]);
    let zero = arena.value_literal(integer_literal());
    let [formed, refused] = [Vec::new(), Vec::from([dangling])]
        .map(|fields| gandr_core_term::DataSignature::new(Vec::new(), Vec::from([fields]), kind));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        Declaration::data(
            ConstantIndex::from(0_usize),
            formed.into(),
            OriginToken::from(0_usize),
        ),
        Declaration::data(
            ConstantIndex::from(1_usize),
            refused.into(),
            OriginToken::from(1_usize),
        ),
        declaration(At(2), Maybe::Present(dangling), Maybe::Present(zero)),
        declaration(At(3), Maybe::Present(partial), Maybe::Present(zero)),
    ];
    let typed = type_module(&mut context, &module);
    assert_eq!(
        typed.keys().copied().collect::<Vec<_>>(),
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(3_usize)
        ],
        "a run that formed nothing is not keyed: {typed:?}"
    );
    for (constant, ty) in [(0_usize, kind), (1, kind), (3, integer)] {
        assert!(
            typed[&ConstantIndex::from(constant)]
                .formed()
                .iter()
                .any(|formed| formed.ty == TypeNode::Value(ty)),
            "the declaration at {constant} keeps what it formed: {typed:?}"
        );
    }
}

/// A declaration's judgement says why it carries no elaboration: a body
/// with no nested computation is unnested, and a first run that decided a
/// nesting and was refused is unaccepted.
#[test]
fn a_refused_first_run_leaves_its_nesting_unaccepted()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let pair = arena.value_type_product(&[integer, integer]);
    let (function, identity) = integer_function(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let applied = call(&mut arena, ConstantIndex::from(0_usize), zero);
    let nested = arena.value_nested(applied);
    let refused = arena.value_tuple(&[nested, text]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let plain = super::decide(
        &mut context,
        &declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
        super::Run::Judged,
    );
    assert!(
        matches!(plain.verdict, Verdict::Checked { .. })
            && matches!(
                plain.elaboration,
                Maybe::Absent(super::elaborated::Absent::Unnested)
            ),
        "a body with no nested computation is unnested: {plain:?}"
    );
    let unaccepted = super::decide(
        &mut context,
        &declaration(At(1), Maybe::Present(pair), Maybe::Present(refused)),
        super::Run::Judged,
    );
    assert!(
        matches!(unaccepted.verdict, Verdict::Refused(_))
            && matches!(
                unaccepted.elaboration,
                Maybe::Absent(super::elaborated::Absent::Unaccepted)
            ),
        "a refused first run that decided a nesting is unaccepted: {unaccepted:?}"
    );
}

#[test]
fn a_typed_module_keeps_the_terms_its_signature_judges()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(integer_literal());
    let path = arena.value_type_path(integer, zero, one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [declaration(At(0), Maybe::Present(path), HOLE)];
    let judged = type_module(&mut context, &module);
    let Some(owed) = judged.get(&ConstantIndex::from(0_usize))
    else {
        panic!("the signature's formation is kept");
    };
    for endpoint in [zero, one] {
        assert!(
            owed.typings()
                .iter()
                .any(|typing| typing.term == TermNode::Value(endpoint)
                    && typing.ty == TypeNode::Value(integer)),
            "each endpoint is kept at the carrier: {owed:?}"
        );
    }
    assert!(
        [path, integer].iter().all(|&ty| owed
            .formed()
            .iter()
            .any(|formed| formed.ty == TypeNode::Value(ty))),
        "the path type and its carrier are kept at their levels: {owed:?}"
    );
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(integer_literal());
    let path = arena.value_type_path(integer, zero, one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.keep_formations(Formations::Firsts(Vec::from([TypeNode::Value(path)])));
    let module = [
        declaration(At(0), Maybe::Present(path), HOLE),
        declaration(At(1), Maybe::Present(path), HOLE),
    ];
    let judged = type_module(&mut context, &module);
    let formed = |at: usize| {
        judged.get(&ConstantIndex::from(at)).map(|owed| {
            owed.formed()
                .iter()
                .map(|formed| formed.ty)
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(
        (formed(0_usize), formed(1_usize)),
        (Some(Vec::from([TypeNode::Value(path)])), Some(Vec::new())),
        "asked for the path type's first formation, the first signature keeps it and no other, and the second, forming it again, keeps nothing"
    );
}

/// `U (Integer -> F Integer)`, and the identity function of that type.
///
/// # Specification
/// trivial.
fn integer_function(arena: &mut CoreArena) -> (ValueTypeId, ValueId)
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
fn call(
    arena: &mut CoreArena,
    callee: ConstantIndex,
    argument: ValueId,
) -> gandr_core_term::ComputationId
{
    let callee = arena.value_constant(callee);
    let forced = arena.computation_force(callee);
    arena.computation_application(forced, argument)
}

#[test]
fn a_nested_run_elaborates_into_a_bind_before_its_region()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let [inner_x, expected_x, expected_inner_r, expected_r] = [(); 4].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let inner = call(&mut arena, ConstantIndex::from(0_usize), inner_x);
    let inner = arena.value_nested(inner);
    let outer = call(&mut arena, ConstantIndex::from(0_usize), inner);
    let outer = arena.value_nested(outer);
    let returned = arena.computation_return(outer);
    let lambda = arena.computation_lambda(returned);
    let twice = arena.value_thunk(lambda);
    let expected = {
        let first = call(&mut arena, ConstantIndex::from(0_usize), expected_x);
        let second = call(&mut arena, ConstantIndex::from(0_usize), expected_inner_r);
        let ran = arena.computation_bind(first, second);
        let returned = arena.computation_return(expected_r);
        let bound = arena.computation_bind(ran, returned);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(function), Maybe::Present(twice)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!("the nested calls check: {:?}", report.judged()[1].verdict());
    };
    assert_ne!(body, twice, "the verdict carries the elaborated body");
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the inner call runs inside the outer one's computation, and the outer before the return"
    );
    assert_eq!(
        report.definitions().get(&ConstantIndex::from(1_usize)),
        Some(&body),
        "the constant is defined as the elaborated body"
    );
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration
            .decisions()
            .iter()
            .map(|(&at, &decided)| (at, decided))
            .collect::<Vec<_>>(),
        [
            (inner, Nesting::Ran(Purity::Pure)),
            (outer, Nesting::Ran(Purity::Pure))
        ],
        "both nested calls run, and neither performs an effect"
    );
    assert_eq!(
        elaboration
            .binds()
            .iter()
            .map(|&(run, _)| run)
            .collect::<Vec<_>>(),
        [inner, outer],
        "each run is reported beside the bind minted for it, the inner first"
    );
    assert!(
        elaboration
            .carried()
            .contains(&gandr_core_term::Carried::Value(twice, body)),
        "the rebuild reports the body it stands for the written one: {:?}",
        elaboration.carried()
    );
    assert!(
        !report
            .nested_elaborations()
            .contains_key(&ConstantIndex::from(0_usize)),
        "a body holding no nested computation is not elaborated"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated body: {readmission:?}"
    );
}

#[test]
fn a_nested_call_runs_with_the_effects_its_returner_performs()
{
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let interface = EffectSig::new("Ask".into(), [EffectOp {
        name: OperationName::from("ask"),
        payload: integer,
        reply: integer,
    }])
    .expect("one operation");
    let asks =
        arena.comp_type_returner_with_effects(integer, EffectRow::singleton(interface.clone()));
    let asking_arrow = arena.comp_type_arrow(integer, asks);
    let asking_type = arena.value_type_thunk(asking_arrow);
    let [asked_x, effectful_x, pure_x] = [(); 3].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let asking = {
        let performed = arena.computation_perform(interface, OperationName::from("ask"), asked_x);
        let lambda = arena.computation_lambda(performed);
        arena.value_thunk(lambda)
    };
    let returned_of = |arena: &mut CoreArena, callee: ConstantIndex, argument: ValueId| {
        let called = call(arena, callee, argument);
        let nested = arena.value_nested(called);
        let returned = arena.computation_return(nested);
        let lambda = arena.computation_lambda(returned);
        (nested, arena.value_thunk(lambda))
    };
    let (effectful, asks_twice) =
        returned_of(&mut arena, ConstantIndex::from(1_usize), effectful_x);
    let (pure, identity_twice) = returned_of(&mut arena, ConstantIndex::from(0_usize), pure_x);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(asking_type), Maybe::Present(asking)),
            declaration(
                At(2),
                Maybe::Present(asking_type),
                Maybe::Present(asks_twice),
            ),
            declaration(
                At(3),
                Maybe::Present(function),
                Maybe::Present(identity_twice),
            ),
        ])
    };
    let decided = |constant: usize, at: ValueId| {
        report
            .nested_elaborations()
            .get(&ConstantIndex::from(constant))
            .and_then(|elaboration| elaboration.decisions().get(&at).copied())
    };
    assert_eq!(
        decided(2, effectful),
        Some(Nesting::Ran(Purity::Effectful)),
        "a call whose returner performs `Ask` runs effectfully: {:?}",
        report.judged()[2].verdict()
    );
    assert_eq!(
        decided(3, pure),
        Some(Nesting::Ran(Purity::Pure)),
        "a call whose returner performs nothing runs purely"
    );
}

#[test]
fn a_pure_run_a_type_reads_stands_as_what_it_returns_444()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    // `Σ (y : Integer). Path(Integer, y, y)`.
    let bound = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let looped = arena.value_type_path(integer, bound, bound);
    let sigma = arena.value_type_sigma(integer, looped);
    let returns = arena.comp_type_returner(sigma);
    let arrow = arena.comp_type_arrow(integer, returns);
    let pairing_type = arena.value_type_thunk(arrow);
    // `λx. return (id(x), here(⟨id(x)⟩))`, the first component a nested
    // call the second's type reads.
    let [nested_x, point_x] = [(); 2].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let first = call(&mut arena, ConstantIndex::from(0_usize), nested_x);
    let first = arena.value_nested(first);
    let point = call(&mut arena, ConstantIndex::from(0_usize), point_x);
    let point = arena.value_returned(point);
    let reflexive = arena.value_here(point);
    let pair = arena.value_tuple(&[first, reflexive]);
    let returned = arena.computation_return(pair);
    let lambda = arena.computation_lambda(returned);
    let pairing = arena.value_thunk(lambda);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(pairing_type), Maybe::Present(pairing)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "the second component checks at the first's call: {:?}",
            report.judged()[1].verdict()
        );
    };
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration.decisions().get(&first),
        Some(&Nesting::Returned),
        "a pure call the second component's type reads stands as what it returns"
    );
    assert!(elaboration.binds().is_empty(), "and mints no bind");
    let Some(&gandr_core_term::Value::Thunk(lambda)) = arena.value(body)
    else {
        panic!("the body stays a thunk");
    };
    let Some(&gandr_core_term::Computation::Lambda(returned)) = arena.computation(lambda)
    else {
        panic!("over its lambda");
    };
    let Some(&gandr_core_term::Computation::Return(pair)) = arena.computation(returned)
    else {
        panic!("returning the pair, with nothing bound before it");
    };
    assert!(
        matches!(
            arena.value(pair).and_then(gandr_core_term::Value::components),
            Some(&[component, _]) if matches!(arena.value(component), Some(&gandr_core_term::Value::Returned(_)))
        ),
        "the first component is the call's returned value"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated body: {readmission:?}"
    );
}

#[test]
fn a_nested_computation_is_decided_by_its_expected_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let suspended_type = arena.value_type_thunk(returns);
    let parameter = arena.comp_type_arrow(suspended_type, returns);
    let consumer_type = arena.value_type_thunk(parameter);
    let consumer = {
        let argument = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let forced = arena.computation_force(argument);
        let lambda = arena.computation_lambda(forced);
        arena.value_thunk(lambda)
    };
    let zero = arena.value_literal(integer_literal());
    let produce = arena.computation_return(zero);
    let suspended = arena.value_nested(produce);
    let consumed = call(&mut arena, ConstantIndex::from(0_usize), suspended);
    let use_site = arena.value_thunk(consumed);
    let unsigned_zero = arena.value_literal(integer_literal());
    let unsigned_produce = arena.computation_return(unsigned_zero);
    let unsigned = arena.value_nested(unsigned_produce);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(
                At(0),
                Maybe::Present(consumer_type),
                Maybe::Present(consumer),
            ),
            declaration(
                At(1),
                Maybe::Present(suspended_type),
                Maybe::Present(use_site),
            ),
            declaration(At(2), UNSIGNED, Maybe::Present(unsigned)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "the nested computation checks at the thunk type: {:?}",
            report.judged()[1].verdict()
        );
    };
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration.decisions().get(&suspended),
        Some(&Nesting::Suspended),
        "at a thunk-typed parameter it is suspended"
    );
    assert!(elaboration.binds().is_empty(), "a suspension mints no bind");
    let Some(&gandr_core_term::Value::Thunk(call_body)) = arena.value(body)
    else {
        panic!("the use site stays a thunk");
    };
    let Some(&gandr_core_term::Computation::Application(_, argument)) =
        arena.computation(call_body)
    else {
        panic!("the call stands as written");
    };
    assert_eq!(
        arena.value(argument),
        Some(&gandr_core_term::Value::Thunk(produce)),
        "the argument is the thunk of the written computation"
    );
    assert_eq!(
        report.judged()[2].verdict(),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Nested(unsigned),
        }),
        "with no type expected there is nothing to decide by, and it is refused by name"
    );
}

#[test]
fn a_run_in_a_definition_s_own_value_is_unenclosed()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let computation = call(&mut arena, ConstantIndex::from(0_usize), zero);
    let nested = arena.value_nested(computation);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(nested)),
        ])
    };
    let refusal = CheckRefusal::UnenclosedRun { at: nested };
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(refusal),
        "the call checks at the integer, but no computation encloses it to run before"
    );
    assert_eq!(refusal.classify(), FailureClass::MalformedSource);
    let failure = &report.failures()[&ConstantIndex::from(1_usize)];
    assert!(
        failure.obligations().is_empty(),
        "no rule of the judgement is pending"
    );
    assert_eq!(
        failure.pursuit().at(),
        CoreNode::Term(TermNode::Value(nested))
    );
    assert!(
        !report
            .definitions()
            .contains_key(&ConstantIndex::from(1_usize)),
        "a refused body defines nothing"
    );
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
fn answers(
    supported: &super::Supported
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

#[test]
fn the_support_holds_each_consulted_answer_once_in_position_order()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let inner = arena.comp_type_arrow(integer, returns_integer);
    let outer = arena.comp_type_arrow(integer, inner);
    let function_type = arena.value_type_thunk(outer);
    let suspended_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let x = arena.value_constant(ConstantIndex::from(0_usize));
    let f = arena.value_constant(ConstantIndex::from(1_usize));
    let unknown = arena.value_constant(ConstantIndex::from(7_usize));
    // thunk ((force f) x) x: reads f, then x, then x again.
    let forced = arena.computation_force(f);
    let once = arena.computation_application(forced, x);
    let twice = arena.computation_application(once, x);
    let suspended = arena.value_thunk(twice);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let _x = check_declaration(
        &mut context,
        &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
    );
    let _f = check_declaration(
        &mut context,
        &declaration(At(1), Maybe::Present(function_type), HOLE),
    );
    let _read = check_declaration(
        &mut context,
        &declaration(At(2), UNSIGNED, Maybe::Present(x)),
    );
    let literal = super::check_declaration_supported(
        &mut context,
        &declaration(At(3), UNSIGNED, Maybe::Present(zero)),
    );
    assert_eq!(
        answers(&literal),
        [],
        "a judgement that reads no constant consults nothing, whatever ran before it"
    );
    let applied = super::check_declaration_supported(
        &mut context,
        &declaration(
            At(4),
            Maybe::Present(suspended_type),
            Maybe::Present(suspended),
        ),
    );
    assert!(
        matches!(applied.verdict(), Verdict::Checked { .. }),
        "the application checks"
    );
    assert_eq!(
        answers(&applied),
        [
            (ConstantIndex::from(0_usize), Maybe::Present(integer)),
            (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
        ],
        "f read first and x read twice are each held once, ascending by position"
    );
    let missing = super::check_declaration_supported(
        &mut context,
        &declaration(At(5), UNSIGNED, Maybe::Present(unknown)),
    );
    assert_eq!(
        answers(&missing),
        [(
            ConstantIndex::from(7_usize),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped)
        )],
        "an unadmitted position is consulted and answers its absence"
    );
}

#[test]
fn a_refusal_cuts_the_support_where_the_run_stopped()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let inner = arena.comp_type_arrow(integer, returns_integer);
    let outer = arena.comp_type_arrow(integer, inner);
    let function_type = arena.value_type_thunk(outer);
    let suspended_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let s = arena.value_constant(ConstantIndex::from(0_usize));
    let f = arena.value_constant(ConstantIndex::from(1_usize));
    let x = arena.value_constant(ConstantIndex::from(2_usize));
    // thunk ((force f) s) x: s is a string, so the run stops before x.
    let forced = arena.computation_force(f);
    let once = arena.computation_application(forced, s);
    let twice = arena.computation_application(once, x);
    let suspended = arena.value_thunk(twice);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(text)),
        declaration(At(1), Maybe::Present(function_type), HOLE),
        declaration(At(2), Maybe::Present(integer), Maybe::Present(zero)),
    ];
    for offered in &module {
        let _judged = check_declaration(&mut context, offered);
    }
    let string = context.atom(Atom::String).id();
    let refused = super::check_declaration_supported(
        &mut context,
        &declaration(
            At(3),
            Maybe::Present(suspended_type),
            Maybe::Present(suspended),
        ),
    );
    assert!(
        matches!(
            refused.verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == s
        ),
        "the string argument is refused at the value bridge"
    );
    assert_eq!(
        answers(&refused),
        [
            (ConstantIndex::from(0_usize), Maybe::Present(string)),
            (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
        ],
        "the support holds what the run consulted before the refusal and nothing after it"
    );
}

#[test]
fn an_adopted_answer_is_read_as_if_judged()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(
        gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        gandr_kernel_strata::Level::zero(),
    );
    let code = arena.value_quote(integer);
    let adopted = arena.value_constant(ConstantIndex::from(0_usize));
    let untyped = arena.value_constant(ConstantIndex::from(1_usize));
    let decoded = arena.value_type_element(adopted, gandr_kernel_strata::Level::zero());
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let formed =
        crate::formation::form_value_type(&mut context, small).expect("the universe forms");
    assert_eq!(
        context.adopt(
            ConstantIndex::from(0_usize),
            Maybe::Present(formed),
            Maybe::Present(code)
        ),
        Ok(()),
        "a first adoption takes any position"
    );
    assert_eq!(
        context.adopt(
            ConstantIndex::from(1_usize),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            Maybe::Absent(crate::code::unfolding::Absent::Rigid)
        ),
        Ok(()),
        "an adopted absence is admitted"
    );
    assert!(
        matches!(
            check_declaration(&mut context, &declaration(At(2), UNSIGNED, Maybe::Present(adopted))),
            Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == small
        ),
        "a later declaration reads the adopted type"
    );
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(3), UNSIGNED, Maybe::Present(untyped))
        ),
        Verdict::Refused(CheckRefusal::UnknownConstant {
            at: untyped,
            constant: ConstantIndex::from(1_usize),
        }),
        "a later declaration finds no type at an adopted absence"
    );
    assert_eq!(
        context.adopt(
            ConstantIndex::from(2_usize),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            Maybe::Absent(crate::code::unfolding::Absent::Rigid)
        ),
        Err(CheckRefusal::AdmissionOrder {
            constant: ConstantIndex::from(2_usize),
            admitted: ConstantIndex::from(3_usize),
        }),
        "an adoption out of order is refused with both positions"
    );
    assert_eq!(
        context
            .signature(ConstantIndex::from(2_usize))
            .map(crate::formation::FormedValueType::id),
        Maybe::Present(small),
        "the refused adoption left the table as it was"
    );
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(4), Maybe::Present(decoded), Maybe::Present(zero))
            ),
            Verdict::Checked { .. }
        ),
        "a decode of the adopted code unfolds to the adopted body"
    );
}

/// The abstract type at `position`, of `kind`, represented by
/// `representation`, sealing the `extent` declarations after it, minted at
/// component `component` of ascription zero; its origin `position + 100`.
///
/// # Specification
/// - requires: adding the origin offset one hundred does not overflow.
/// - ensures: the abstract type is offered at the fixture position with the
///   distinct origin.
/// - panics: the position lies outside the offset domain.
///
/// # Adequacy
/// - hypothesis: L3 — a sealed module observes each premise of abstract type
///   formation and the reach of its seal.
/// - witness: `module::tests::an_abstract_type_forms_at_a_value_universe_and_mints_its_site`
/// - witness: `module::tests::a_sealed_member_checks_at_the_representation_inside`
#[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| usize::from(ret.constant()) == position.0
            && matches!(ret.content(), &crate::DeclarationContent::Abstract(held)
                if held.kind() == kind && held.representation() == representation),
    )]
fn sealed(
    position: At,
    kind: ValueTypeId,
    representation: ValueTypeId,
    extent: SealExtent,
    component: ComponentOrdinal,
) -> Declaration
{
    Declaration::abstract_type(
        ConstantIndex::from(position.0),
        AbstractType::new(
            kind,
            representation,
            extent,
            SealSite::new(SealingSite::from(0_usize), component),
        ),
        OriginToken::from(position.0.checked_add(100).unwrap()),
    )
}

#[test]
fn an_abstract_type_forms_at_a_value_universe_and_mints_its_site()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let module = [
        sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
        sealed(At(1), integer, integer, 0_usize.into(), 1_usize.into()),
        sealed(At(2), small, small, 0_usize.into(), 2_usize.into()),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    assert_eq!(
        verdicts,
        [
            Verdict::Data,
            Verdict::Refused(CheckRefusal::AbstractKindNotUniverse(integer)),
            Verdict::Refused(CheckRefusal::RepresentationAboveKind {
                representation: small,
                kind: small,
            }),
        ],
        "a kind at a value universe forms; a kind that is no universe and a representation above its kind are refused by name"
    );
    assert_eq!(
        report.seal_table().sites(),
        [SealSite::new(
            SealingSite::from(0_usize),
            ComponentOrdinal::from(0_usize)
        )],
        "only the abstract type that formed minted its site"
    );
    assert_eq!(
        report.abstract_types().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(0_usize)],
        "and only it is retained for readmission"
    );
    assert_eq!(
        context.abstract_level(ConstantIndex::from(0_usize)),
        Ok(Level::zero()),
        "its atom inhabits its kind's universe"
    );
}

#[test]
fn a_repeated_sealing_site_is_refused_and_mints_nothing()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let module = [
        sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
        sealed(At(1), small, integer, 0_usize.into(), 0_usize.into()),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let site = SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize));
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(CheckRefusal::SealSiteRepeated(site)),
        "a second abstract type at one site is refused naming the site"
    );
    assert_eq!(
        (report.seal_table().sites(), report.abstract_types().len()),
        ([site].as_slice(), 1),
        "the refused one minted no second atom and was not retained"
    );
}

#[test]
fn an_atom_naming_no_abstract_type_is_refused()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let named = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(named), HOLE),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(CheckRefusal::NotAnAbstractType(ConstantIndex::from(
            0_usize
        ))),
        "an atom at a value declaration's position is no type"
    );
}

/// `module Counter :> #{ type T, seed : T } { type T = Integer ; def seed
/// = 7 ; }` as the lowering admits it: the atom, the body member, the
/// witness exporting it at the component type, then two clients.
#[test]
fn a_sealed_member_checks_at_the_representation_inside()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let seven = arena.value_literal(integer_literal());
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let member = arena.value_constant(ConstantIndex::from(1_usize));
    let export = arena.value_constant(ConstantIndex::from(2_usize));
    let module = [
        sealed(At(0), small, integer, 2_usize.into(), 0_usize.into()),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(seven)),
        declaration(At(2), Maybe::Present(atom), Maybe::Present(member)),
        declaration(At(3), Maybe::Present(atom), Maybe::Present(export)),
        declaration(At(4), Maybe::Present(integer), Maybe::Present(export)),
        declaration(At(5), Maybe::Present(atom), Maybe::Present(seven)),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    assert!(
        matches!(verdicts[2], Verdict::Checked { .. }),
        "inside the seal the member's Integer is the atom's representation"
    );
    assert!(
        matches!(verdicts[3], Verdict::Checked { .. }),
        "outside, the export reads at the atom, which is itself"
    );
    assert_eq!(
        verdicts[4],
        Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value {
            at: export,
            synthesised: atom,
            expected: integer,
        })),
        "outside, the atom is not its representation, and the mismatch names it"
    );
    assert!(
        matches!(verdicts[5], Verdict::Refused(CheckRefusal::TypeMismatch(_))),
        "nor does a literal of the representation inhabit it"
    );
}
