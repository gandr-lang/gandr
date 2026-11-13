//! Executable route laws, separately from the kernel's typing oracle.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_term::Binders;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::TypeNode;
use crate::check_module;
use crate::fixture::elaboration::At;
use crate::fixture::elaboration::declaration;
use crate::fixture::elaboration::route;
use crate::fixture::integer_literal;
use crate::refusal::Unsolved;

#[test]
fn a_supported_judgement_keeps_the_suspension_that_the_module_run_reports()
{
    // The route and a reader of its first suspended declaration: judged one
    // at a time, each suspended declaration waits on what the module run
    // reports, the reader's equations joined with those it reads. The parts
    // of a suspension seat that suspension again.
    let mut arena = CoreArena::new();
    let mut fixture = route(&mut arena);
    let reference = arena.value_constant(ConstantIndex::from(1_usize));
    fixture.declarations.push(declaration(
        At(4),
        fixture.decoded,
        Maybe::Present(reference),
    ));
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &fixture.declarations)
    };
    let supported = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let mut prior = BTreeMap::new();
        for declaration in &fixture.declarations {
            let judged = crate::check_declaration_supported(&mut context, declaration);
            if let Maybe::Present(suspension) = judged.suspension(&context, &prior) {
                let _earlier = prior.insert(declaration.constant(), suspension);
            }
        }
        prior
    };
    assert_eq!(
        supported.keys().collect::<Vec<_>>(),
        report.suspensions().keys().collect::<Vec<_>>(),
        "the same declarations wait"
    );
    // Each judgement mints the rigid side afresh: compare it by its node.
    let rigid = |node: TypeNode| match node {
        TypeNode::Value(id) => arena.value_type(id),
        TypeNode::Computation(_) => None,
    };
    for (one, other) in supported.values().zip(report.suspensions().values()) {
        assert_eq!(
            (one.declared(), one.blockers(), one.dependencies()),
            (other.declared(), other.blockers(), other.dependencies()),
        );
        assert!(
            one.equations()
                .iter()
                .map(|equation| (equation.hole(), equation.flex(), rigid(equation.rigid())))
                .eq(other.equations().iter().map(|equation| (
                    equation.hole(),
                    equation.flex(),
                    rigid(equation.rigid())
                ))),
            "the equations agree: {one:?} against {other:?}"
        );
    }
    let Some(reader) = supported.get(&ConstantIndex::from(4_usize))
    else {
        panic!("the reader waits: {supported:?}");
    };
    assert_eq!(
        (reader.dependencies(), reader.equations().len()),
        (&BTreeSet::from([ConstantIndex::from(1_usize)]), 1),
        "the reader waits on the hole through the declaration it reads"
    );
    let seated = super::Suspension::seated(
        (reader.declared().id(), reader.equations().to_vec()),
        (reader.blockers().clone(), reader.dependencies().clone()),
    );
    assert_eq!(&seated, reader, "the parts of a suspension seat it again");
}

#[test]
fn an_off_collector_never_defers()
{
    // A judgement that does not collect decides every comparison rigidly,
    // whatever holes are owed: deferring there would accept a mismatch.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let mut deferrals = super::Deferrals::default();
    deferrals.owed.insert(ConstantIndex::from(0_usize));
    let (flex, rigid) = (
        TypeNode::Value(fixture.decoded),
        TypeNode::Value(fixture.integer),
    );
    deferrals.open(super::Collecting::Off);
    assert_eq!(deferrals.defer(&arena, flex, rigid), super::Deferred::No);
    assert!(deferrals.take().equations.is_empty());
    deferrals.open(super::Collecting::On);
    assert_eq!(deferrals.defer(&arena, flex, rigid), super::Deferred::Yes);
}

/// A collector open for a value declaration, with the first nominated hole
/// declared at no binder: the hole, its node and its decode.
///
/// # Specification
/// trivial.
fn nominated(
    arena: &mut CoreArena,
    deferrals: &mut super::Deferrals,
) -> (gandr_core_term::hole::HoleId, ValueId, ValueTypeId)
{
    let hole = gandr_core_term::hole::HoleId::nominated(
        gandr_core_term::hole::NominationIndex::from(0_u32),
    )
    .expect("the first nominated name");
    let at = arena.value_hole(hole);
    deferrals.open(super::Collecting::On);
    deferrals.nominate(at, hole, Binders::NONE);
    (hole, at, arena.value_type_element(at, Level::zero()))
}

#[test]
fn an_omitted_implicit_is_solved_from_the_argument_1216()
{
    // `same(3)`: the decode of `a` against the type the argument synthesises
    // binds `a` to that type's code. A pair neither side of which is a
    // metavariable's decode is conversion's, and nothing is bound by it.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (hole, _, decoded) = nominated(&mut arena, &mut deferrals);
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let rigid = (TypeNode::Value(integer), TypeNode::Value(unit));
    assert_eq!(
        deferrals.unify(&mut arena, Binders::NONE, rigid.0, rigid.1),
        super::Unified::Rigid
    );
    assert_eq!(
        deferrals.unify(
            &mut arena,
            Binders::NONE,
            TypeNode::Value(decoded),
            TypeNode::Value(integer)
        ),
        super::Unified::Agreed
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved.len() == 1
            && solved.get(&hole).is_some_and(|&(code, scope)| {
                scope == Binders::NONE
                    && matches!(arena.value(code), Some(&Value::Quote(quoted)) if quoted == integer)
            })),
        "`a` is solved as the integers' code, at the binders it was declared under: {solutions:?}"
    );
}

#[test]
fn two_arguments_disagreeing_on_an_implicit_are_apart_1216()
{
    // `both(3, unit)`: the first argument binds `a` to the integers, and the
    // second's type is refuted against the same decode.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (_, _, decoded) = nominated(&mut arena, &mut deferrals);
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let [first, second] = [integer, unit].map(|argument| {
        deferrals.unify(
            &mut arena,
            Binders::NONE,
            TypeNode::Value(decoded),
            TypeNode::Value(argument),
        )
    });
    assert_eq!(first, super::Unified::Agreed);
    assert_eq!(second, super::Unified::Refuted);
}

#[test]
fn an_open_end_is_solved_from_its_point_1979()
{
    // `(here(0) : Path[.A = Integer](0, _))`: two rigid values are conversion's;
    // the open end against the point that reaches it is bound to the point;
    // a second, different point is then refuted against the same end.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (hole, open, _) = nominated(&mut arena, &mut deferrals);
    let zero = arena.value_literal(integer_literal());
    let one = gandr_kernel_term::Magnitude::from_decimal_text("1".into())
        .expect("the digits are decimal");
    let one = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(gandr_kernel_term::Sign::NonNegative, one),
    ));
    let outcomes = [(zero, one), (zero, open), (one, open)]
        .map(|(point, end)| deferrals.unify_values(&mut arena, Binders::NONE, point, end));
    assert_eq!(
        outcomes,
        [
            super::Unified::Rigid,
            super::Unified::Agreed,
            super::Unified::Refuted
        ],
        "rigid values are left to conversion, the open end is solved, and a second point is apart"
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved.len() == 1
            && solved.get(&hole).is_some_and(|&(end, scope)| {
                scope == Binders::NONE
                    && gandr_core_term::equal_certificate_syntax(&arena, end, zero)
                        == gandr_core_term::CertificateEquality::Equal
            })),
        "the end is solved as the point, at the binders it was declared under: {solutions:?}"
    );
}

#[test]
fn an_implicit_no_argument_forces_is_unsolved_1216()
{
    // `twice(3)`'s combination: met and declared, compared with nothing.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (_, at, _) = nominated(&mut arena, &mut deferrals);
    assert_eq!(deferrals.solutions(&arena), Err((at, Unsolved::Unforced)));
}

#[test]
fn an_implicit_solved_past_its_scope_escapes_1216()
{
    // `konst(fun (t) { fun (y) { return y } })`: under the lambda's binder the
    // decode of `b`, declared outside it, meets the decode of `t`. The only
    // solution names `t`, so the equation waits on its escape, and the
    // refusal says so.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (_, at, decoded) = nominated(&mut arena, &mut deferrals);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded_bound = arena.value_type_element(bound, Level::zero());
    assert_eq!(
        deferrals.unify(
            &mut arena,
            Binders::ONE,
            TypeNode::Value(decoded),
            TypeNode::Value(decoded_bound)
        ),
        super::Unified::Agreed
    );
    assert_eq!(deferrals.solutions(&arena), Err((at, Unsolved::Escape)));
}

#[test]
fn a_row_open_through_an_implicit_is_solved_by_the_row_equation_2270()
{
    // `log("a")` where `[Console, Partial]` is asked: `log`'s row `[Console | r]`,
    // `r` omitted, against the closed row binds `r` to `[Partial]`. Two closed
    // rows are conversion's; against `[Partial]`, which lacks `Console`, the open
    // row is apart.
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;

    let row = |names: &[&str]| {
        names.iter().fold(EffectRow::EMPTY, |row, &name| {
            let signature = EffectSig::new(EffectName::from(name), Vec::<EffectOp>::new())
                .expect("an interface without operations has no duplicate");
            row.union(&EffectRow::singleton(signature), &CoreArena::new())
                .expect("each interface once")
        })
    };
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (hole, at, _) = nominated(&mut arena, &mut deferrals);
    let tail = arena.value_type_row_tail(at);
    let open = row(&["Console"]).with_tail(Some(tail));
    let (asked, lacking) = (row(&["Console", "Partial"]), row(&["Partial"]));
    assert_eq!(
        deferrals.unify_rows(&mut arena, Binders::NONE, (&asked, &lacking)),
        super::Unified::Rigid,
        "two closed rows are conversion's"
    );
    assert_eq!(
        deferrals.unify_rows(&mut arena, Binders::NONE, (&open, &asked)),
        super::Unified::Agreed,
        "the open row meets the asked one"
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions
            .as_ref()
            .is_ok_and(|solved| solved.get(&hole).is_some_and(|&(code, _)| {
                matches!(arena.value(code), Some(Value::Row(solved))
                if solved.tail().is_none()
                    && solved.signatures().map(|signature| signature.name().as_ref()).eq(["Partial"]))
            })),
        "`r` is solved as `[Partial]`, closed: {solutions:?}"
    );
    assert_eq!(
        deferrals.unify_rows(&mut arena, Binders::NONE, (&open, &lacking)),
        super::Unified::Refuted,
        "a row lacking `Console` is apart from `log`'s"
    );
}

/// A collector open for a value declaration over a counter's model slot: its
/// sort's hole and its step's, both declared at no binder, the sort's forced
/// to the integers as `stepped(4)`'s argument forces it. The holes, the sort
/// hole's node, and the codes of the integers and of the unit type.
///
/// # Specification
/// trivial.
fn forced_slot(
    arena: &mut CoreArena,
    deferrals: &mut super::Deferrals,
) -> ([gandr_core_term::hole::HoleId; 2], ValueId, [ValueId; 2])
{
    let [sort, step] = [0_u32, 1].map(|index| {
        gandr_core_term::hole::HoleId::nominated(gandr_core_term::hole::NominationIndex::from(
            index,
        ))
        .expect("a nominated name")
    });
    let [sort_at, step_at] = [sort, step].map(|hole| arena.value_hole(hole));
    deferrals.open(super::Collecting::On);
    deferrals.nominate(sort_at, sort, Binders::NONE);
    deferrals.nominate(step_at, step, Binders::NONE);
    let decoded = arena.value_type_element(sort_at, Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    assert_eq!(
        deferrals.unify(
            arena,
            Binders::NONE,
            TypeNode::Value(decoded),
            TypeNode::Value(integer)
        ),
        super::Unified::Agreed,
        "the argument forces the sort"
    );
    let unit = arena.value_type_unit();
    let codes = [integer, unit].map(|ty| arena.value_quote(ty));
    ([sort, step], sort_at, codes)
}

/// The candidate passing the sort `code` and the step named by the constant
/// at `step`.
///
/// # Specification
/// trivial.
fn candidate(
    arena: &mut CoreArena,
    code: ValueId,
    step: ConstantIndex,
) -> gandr_core_term::model::Candidate
{
    gandr_core_term::model::Candidate {
        components: Vec::from([code, arena.value_constant(step)]),
        fixed: Vec::new(),
    }
}

#[test]
fn a_model_slot_resolves_to_the_candidate_its_sort_admits_739()
{
    // `stepped(4)` with `Up` over the integers and `Flag` over the unit type
    // in scope: the argument forces the sort, so only `Up` is left, and the
    // step is solved as `Up`'s.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, _, [integer, unit]) = forced_slot(&mut arena, &mut deferrals);
    let up = candidate(&mut arena, integer, ConstantIndex::from(1_usize));
    let flag = candidate(&mut arena, unit, ConstantIndex::from(2_usize));
    let up_step = up.components[1];
    let slot = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates: Vec::from([flag, up]),
    };
    let definitions = crate::code::CodeDefinitions::new();
    assert_eq!(
        deferrals.resolve(&mut arena, &definitions, &[slot], super::Signing::Body),
        Ok(())
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved
            .get(&holes[1])
            .is_some_and(|&(step, _)| step == up_step)),
        "the step is `Up`'s: {solutions:?}"
    );
}

/// A capability scope answered by the model in scope meets its theory's
/// operations as terms, but its carrier only through a decode the judgement
/// reads as the unknown type, and its laws nowhere: the slot resolves on the
/// holes the judgement met, and its one elaboration answers the others by its
/// own components, closed, at no binder.
#[test]
fn a_slot_hole_the_judgement_never_met_is_answered_by_the_elaboration_2755()
{
    // `Up` and `Flag` as above, each passing one more component the
    // judgement never meets, each its own.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let ([sort, step], _, [integer, unit]) = forced_slot(&mut arena, &mut deferrals);
    let unmet = gandr_core_term::hole::HoleId::nominated(
        gandr_core_term::hole::NominationIndex::from(2_u32),
    )
    .expect("a nominated name");
    let standing = arena.value_hole(unmet);
    let _decoded = arena.value_type_element(standing, Level::zero());
    let [up, flag] = [(integer, 1_usize, 3_usize), (unit, 2, 4)].map(|(code, at, own)| {
        let mut answering = candidate(&mut arena, code, ConstantIndex::from(at));
        answering
            .components
            .push(arena.value_constant(ConstantIndex::from(own)));
        answering
    });
    let (up_step, up_unmet) = (up.components[1], up.components[2]);
    let slot = gandr_core_term::model::ModelSlot {
        holes: Vec::from([sort, step, unmet]),
        fixed: Vec::new(),
        candidates: Vec::from([flag, up]),
    };
    let definitions = crate::code::CodeDefinitions::new();
    assert_eq!(
        deferrals.resolve(&mut arena, &definitions, &[slot], super::Signing::Body),
        Ok(())
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved
            .get(&step)
            .is_some_and(|&(solved, _)| solved == up_step)
            && solved.get(&unmet) == Some(&(up_unmet, Binders::NONE))),
        "the step is `Up`'s, and so is the hole the judgement never met: {solutions:?}"
    );
}

#[test]
fn a_model_slot_two_candidates_answer_is_ambiguous_739()
{
    // `Up` and `Tens`, both over the integers: the argument's sort leaves
    // both, and the refusal names both by their places.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, at, [integer, unit]) = forced_slot(&mut arena, &mut deferrals);
    let candidates = Vec::from([
        candidate(&mut arena, integer, ConstantIndex::from(1_usize)),
        candidate(&mut arena, unit, ConstantIndex::from(2_usize)),
        candidate(&mut arena, integer, ConstantIndex::from(3_usize)),
    ]);
    let slot = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates,
    };
    let survivors = [0_usize, 2]
        .into_iter()
        .map(gandr_core_term::model::CandidatePlace::from)
        .fold(
            gandr_core_term::model::Survivors::default(),
            gandr_core_term::model::Survivors::with,
        );
    let definitions = crate::code::CodeDefinitions::new();
    assert_eq!(
        deferrals.resolve(&mut arena, &definitions, &[slot], super::Signing::Body),
        Err((at, CheckRefusal::ModelAmbiguous { at, survivors }))
    );
}

/// #6550: a candidate whose step the machine declines against the first
/// candidate's step is no second elaboration: at the signature the slot binds
/// nothing, and after the body it is undecided, not ambiguous.
#[test]
fn a_slot_whose_candidates_the_machine_declines_is_undecided_6550()
{
    // `Held` passes the integers and a held call of an axiom as its step,
    // and `Zero` the integers and the literal zero. The call has no body to
    // unfold, and the machine declines it against the literal.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, at, [integer, _]) = forced_slot(&mut arena, &mut deferrals);
    let axiom = arena.value_constant(ConstantIndex::from(5_usize));
    let zero = arena.value_literal(integer_literal());
    let forced = arena.computation_force(axiom);
    let call = arena.computation_application(forced, zero);
    let held = arena.value_returned(call);
    let undecided = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates: Vec::from([
            gandr_core_term::model::Candidate {
                components: Vec::from([integer, held]),
                fixed: Vec::new(),
            },
            gandr_core_term::model::Candidate {
                components: Vec::from([integer, zero]),
                fixed: Vec::new(),
            },
        ]),
    };
    let definitions = crate::code::CodeDefinitions::new();
    assert_eq!(
        deferrals.resolve(
            &mut arena,
            &definitions,
            core::slice::from_ref(&undecided),
            super::Signing::Signature
        ),
        Ok(()),
        "the signature refuses no slot the machine leaves undecided"
    );
    assert!(
        !deferrals
            .solutions(&arena)
            .is_ok_and(|solved| solved.contains_key(&holes[1])),
        "the step stays unbound for the body"
    );
    assert_eq!(
        deferrals.resolve(&mut arena, &definitions, &[undecided], super::Signing::Body),
        Err((at, CheckRefusal::Undecided { at })),
        "after the body, the slot is undecided, not ambiguous"
    );
}

/// A slot the declared type leaves undecided waits for the body (#6158): at
/// the signature, a slot two candidates of the forced sort answer and one no
/// candidate answers bind nothing and are not refused; after the body, the
/// same slots are refused.
#[test]
fn a_slot_the_signature_leaves_undecided_waits_for_the_body_6158()
{
    // `Up` and `Tens`, both over the integers, and `Flag` alone, over the
    // unit type, where the argument forces the integers.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, at, [integer, unit]) = forced_slot(&mut arena, &mut deferrals);
    let ambiguous = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates: Vec::from([
            candidate(&mut arena, integer, ConstantIndex::from(1_usize)),
            candidate(&mut arena, integer, ConstantIndex::from(3_usize)),
        ]),
    };
    let unanswered = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates: Vec::from([candidate(&mut arena, unit, ConstantIndex::from(2_usize))]),
    };
    let definitions = crate::code::CodeDefinitions::new();
    for slot in [&ambiguous, &unanswered] {
        assert_eq!(
            deferrals.resolve(
                &mut arena,
                &definitions,
                core::slice::from_ref(slot),
                super::Signing::Signature
            ),
            Ok(()),
            "the signature refuses no slot it leaves undecided"
        );
        assert!(
            !deferrals
                .solutions(&arena)
                .is_ok_and(|solved| solved.contains_key(&holes[1])),
            "the step stays unbound for the body"
        );
    }
    let after = deferrals.resolve(&mut arena, &definitions, &[ambiguous], super::Signing::Body);
    assert!(
        matches!(after, Err((named, CheckRefusal::ModelAmbiguous { at: hole, .. })) if named == at && hole == at),
        "after the body, two elaborations are refused: {after:?}"
    );
    let after = deferrals.resolve(
        &mut arena,
        &definitions,
        &[unanswered],
        super::Signing::Body,
    );
    assert!(
        matches!(after, Err((named, CheckRefusal::ModelUnanswered { at: hole, .. })) if named == at && hole == at),
        "after the body, no elaboration is refused: {after:?}"
    );
}

#[test]
fn two_candidates_passing_one_member_are_one_elaboration_2333()
{
    // `OrdInteger` includes `EqInteger`, so at `Eq` both pass the integers
    // and the one `eq`: each candidate's values are minted apart, as packing
    // two modules mints them, and still the slot resolves, to the first.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, _, [integer, _]) = forced_slot(&mut arena, &mut deferrals);
    let integer_again = {
        let ty = arena.value_type_base(BaseType::Integer);
        arena.value_quote(ty)
    };
    let included = candidate(&mut arena, integer, ConstantIndex::from(1_usize));
    let including = candidate(&mut arena, integer_again, ConstantIndex::from(1_usize));
    let step = included.components[1];
    assert_ne!(step, including.components[1], "the two are minted apart");
    let slot = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates: Vec::from([included, including]),
    };
    let definitions = crate::code::CodeDefinitions::new();
    assert_eq!(
        deferrals.resolve(&mut arena, &definitions, &[slot], super::Signing::Body),
        Ok(())
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved
            .get(&holes[1])
            .is_some_and(|&(solved, _)| solved == step)),
        "the step is the first candidate's: {solutions:?}"
    );
}

#[test]
fn a_model_slot_no_candidate_answers_is_refused_739()
{
    // Only `Flag`, over the unit type, where the argument forces the
    // integers; and a scope holding no model at all. Each refusal names the
    // integers, the type the argument forces (#3375).
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, at, [_, unit]) = forced_slot(&mut arena, &mut deferrals);
    let flag = candidate(&mut arena, unit, ConstantIndex::from(2_usize));
    let definitions = crate::code::CodeDefinitions::new();
    let [refuted, empty] = [Vec::from([flag]), Vec::new()].map(|candidates| {
        deferrals.resolve(
            &mut arena,
            &definitions,
            &[gandr_core_term::model::ModelSlot {
                holes: Vec::from(holes),
                fixed: Vec::new(),
                candidates,
            }],
            super::Signing::Body,
        )
    });
    for refusal in [refuted, empty] {
        assert!(
            matches!(
                refusal,
                Err((named, CheckRefusal::ModelUnanswered { at: hole, forced: crate::Forced::Type(forced) }))
                    if named == at && hole == at
                        && matches!(arena.value_type(forced), Some(ValueType::Base(BaseType::Integer)))
            ),
            "the refusal names the integers the argument forces: {refusal:?}"
        );
    }
}

#[test]
fn a_manifest_model_slot_resolves_to_the_candidate_of_its_fixed_sort_2317()
{
    // `fromZero()` over `[s : Model(Tally) with sort C = Integer]`: the slot
    // binds the step alone, nothing forces it, and the sort is fixed, so only
    // the fixed sort tells `Up`, over the integers, from `Flips`, over the
    // unit type. A fixed type reading a binder of the callee tests nothing.
    let mut arena = CoreArena::new();
    let step = gandr_core_term::hole::HoleId::nominated(
        gandr_core_term::hole::NominationIndex::from(0_u32),
    )
    .expect("a nominated name");
    let at = arena.value_hole(step);
    let collecting = || {
        let mut deferrals = super::Deferrals::default();
        deferrals.open(super::Collecting::On);
        deferrals.nominate(at, step, Binders::NONE);
        deferrals
    };
    let mut deferrals = collecting();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let [integer, unit] = [integer, unit].map(|ty| arena.value_quote(ty));
    let [up_step, flips_step] =
        [1_usize, 2].map(|constant| arena.value_constant(ConstantIndex::from(constant)));
    let candidates = Vec::from([
        gandr_core_term::model::Candidate {
            components: Vec::from([flips_step]),
            fixed: Vec::from([unit]),
        },
        gandr_core_term::model::Candidate {
            components: Vec::from([up_step]),
            fixed: Vec::from([integer]),
        },
    ]);
    let slot = |fixed| gandr_core_term::model::ModelSlot {
        holes: Vec::from([step]),
        fixed: Vec::from([fixed]),
        candidates: candidates.clone(),
    };
    let mut open = collecting();
    let definitions = crate::code::CodeDefinitions::new();
    assert_eq!(
        deferrals.resolve(
            &mut arena,
            &definitions,
            &[slot(integer)],
            super::Signing::Body
        ),
        Ok(())
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved
            .get(&step)
            .is_some_and(|&(solved, _)| solved == up_step)),
        "the step is `Up`'s: {solutions:?}"
    );
    let bound = arena.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let survivors = [0_usize, 1]
        .into_iter()
        .map(gandr_core_term::model::CandidatePlace::from)
        .fold(
            gandr_core_term::model::Survivors::default(),
            gandr_core_term::model::Survivors::with,
        );
    assert_eq!(
        open.resolve(
            &mut arena,
            &definitions,
            &[slot(bound)],
            super::Signing::Body
        ),
        Err((at, CheckRefusal::ModelAmbiguous { at, survivors })),
        "a fixed type reading the callee's binder refutes neither"
    );
}
