//! Recursive data, fixpoints and their refusals across persistence and reuse.

use alloc::sync::Arc;
use alloc::vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::Program;
use gandr_core_incremental::Refusal;
use gandr_core_incremental::Typing;
use gandr_core_incremental::check_program;
use gandr_core_incremental::decode_checkpoints;
use gandr_core_incremental::encode_checkpoints;
use gandr_core_incremental::resume_from;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::ParameterPosition;
use quenchant_shape::shape::Maybe;

/// A definition at `position`.
///
/// # Specification
/// trivial.
fn definition(
    position: ConstantIndex,
    declared: ValueTypeId,
    body: ValueId,
) -> Declaration
{
    Declaration::new(
        position,
        Maybe::Present(declared),
        Maybe::Present(body),
        OriginToken::from(usize::from(position)),
    )
}

/// A data declaration at `position`.
///
/// # Specification
/// trivial.
fn data(
    position: ConstantIndex,
    signature: DataSignature,
) -> Declaration
{
    Declaration::data(
        position,
        Arc::new(signature),
        OriginToken::from(usize::from(position)),
    )
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn var(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// A one-parameter, one-field declaration at `position` whose field the
/// caller writes over the family applied to its parameter.
///
/// # Specification
/// trivial.
fn occurrence(
    arena: &mut CoreArena,
    position: ConstantIndex,
    field: impl FnOnce(&mut CoreArena, ValueTypeId) -> (Vec<ValueTypeId>, ValueTypeId),
) -> Declaration
{
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let parameter = var(arena, DeBruijnIndex::from(0));
    let own = arena.value_type_data(position, vec![parameter]);
    let (mut extra, field) = field(arena, own);
    let mut parameters = vec![universe];
    parameters.append(&mut extra);
    data(
        position,
        DataSignature::new(parameters, vec![vec![field]], universe),
    )
}

/// `Nat`, fixpoints that check, refuse a claim and stand at a head, a
/// structurally descending `double`, a family consuming its parameter, and
/// each refused occurrence.
///
/// # Specification
/// - ensures: twelve items at ascending positions.
/// - panics: only if the program container refuses the fixture.
///
/// # Adequacy
/// - hypothesis: L3 — each item reaches one admitted form or one refusal of the
///   recursion vocabulary.
/// - witness: `tests::recursive_data::recursive_data_checkpoints_round_trip_and_resume`
#[spec(ensures: |ret| ret.items().len() == 12)]
fn program() -> Program
{
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let nat_data = data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![], vec![nat]], kind),
    );

    let unit_type = arena.value_type_unit();
    let unit_returner = arena.comp_type_returner(unit_type);
    let suspended_unit = arena.value_type_thunk(unit_returner);
    let looping = |arena: &mut CoreArena, evidence| {
        let recursive = var(arena, DeBruijnIndex::from(0));
        let forced = arena.computation_force(recursive);
        let fixpoint = arena.computation_fixpoint(forced, evidence);
        arena.value_thunk(fixpoint)
    };
    let partial = looping(&mut arena, FixpointEvidence::Partial);
    let claimed = looping(&mut arena, FixpointEvidence::StructuralDescent);
    let headed = {
        let unit = arena.value_unit();
        let bound = var(&mut arena, DeBruijnIndex::from(0));
        let returned = arena.computation_return(bound);
        let identity = arena.computation_lambda(returned);
        let fixpoint = arena.computation_fixpoint(identity, FixpointEvidence::Partial);
        let applied = arena.computation_application(fixpoint, unit);
        arena.value_thunk(applied)
    };

    // double = fix rec. λx. case x of { zero ↦ zero; succ p ↦ succ (succ (rec p)) }
    let nat_returner = arena.comp_type_returner(nat);
    let doubling_type = {
        let arrow = arena.comp_type_arrow(nat, nat_returner);
        arena.value_type_thunk(arrow)
    };
    let doubling = {
        let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
        let on_zero = arena.computation_return(zero);
        // Under the field: p 0, x 1, rec 2.
        let recursive = var(&mut arena, DeBruijnIndex::from(2));
        let field = var(&mut arena, DeBruijnIndex::from(0));
        let forced = arena.computation_force(recursive);
        let call = arena.computation_application(forced, field);
        let result = var(&mut arena, DeBruijnIndex::from(0));
        let once = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
        let twice = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![once]);
        let returned = arena.computation_return(twice);
        let bound = arena.computation_bind(call, returned);
        let on_successor = arena.computation_lambda(bound);
        let scrutinee = var(&mut arena, DeBruijnIndex::from(0));
        let case =
            arena.computation_data_case(scrutinee, nat_returner, vec![on_zero, on_successor]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        arena.value_thunk(fixpoint)
    };

    // A lifted occurrence under a domain: no stage reaches it.
    let negative = occurrence(&mut arena, ConstantIndex::from(5_usize), |arena, own| {
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let lifted = arena.value_type_lift(own, Level::zero());
        let function = arena.comp_type_arrow(lifted, returner);
        (vec![], arena.value_type_thunk(function))
    });
    // `Tested A` consumes its parameter: `A` is not strictly positive in it.
    let tested = occurrence(&mut arena, ConstantIndex::from(6_usize), |arena, _own| {
        let parameter = var(arena, DeBruijnIndex::from(0));
        let element = arena.value_type_element(parameter, Level::zero());
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let function = arena.comp_type_arrow(element, returner);
        (vec![], arena.value_type_thunk(function))
    });
    let nested = occurrence(&mut arena, ConstantIndex::from(7_usize), |arena, own| {
        let code = arena.value_quote(own);
        (
            vec![],
            arena.value_type_data(ConstantIndex::from(6_usize), vec![code]),
        )
    });
    let non_uniform = occurrence(&mut arena, ConstantIndex::from(8_usize), |arena, _own| {
        let unit = arena.value_type_unit();
        let code = arena.value_quote(unit);
        (
            vec![],
            arena.value_type_data(ConstantIndex::from(8_usize), vec![code]),
        )
    });
    let later = occurrence(&mut arena, ConstantIndex::from(9_usize), |arena, _own| {
        (
            vec![],
            arena.value_type_data(ConstantIndex::from(10_usize), vec![]),
        )
    });
    let tail = data(
        ConstantIndex::from(10_usize),
        DataSignature::new(vec![], vec![vec![]], kind),
    );
    let telescope = occurrence(&mut arena, ConstantIndex::from(11_usize), |arena, own| {
        let unit = arena.value_type_unit();
        (vec![own], unit)
    });

    Program::new(arena, vec![
        Item::new(ItemKey::from("Nat"), nat_data),
        Item::new(
            ItemKey::from("loop"),
            definition(ConstantIndex::from(1_usize), suspended_unit, partial),
        ),
        Item::new(
            ItemKey::from("claimed"),
            definition(ConstantIndex::from(2_usize), suspended_unit, claimed),
        ),
        Item::new(
            ItemKey::from("headed"),
            definition(ConstantIndex::from(3_usize), suspended_unit, headed),
        ),
        Item::new(
            ItemKey::from("double"),
            definition(ConstantIndex::from(4_usize), doubling_type, doubling),
        ),
        Item::new(ItemKey::from("Negative"), negative),
        Item::new(ItemKey::from("Tested"), tested),
        Item::new(ItemKey::from("Nested"), nested),
        Item::new(ItemKey::from("NonUniform"), non_uniform),
        Item::new(ItemKey::from("Later"), later),
        Item::new(ItemKey::from("Tail"), tail),
        Item::new(ItemKey::from("Telescope"), telescope),
    ])
    .expect("fixture positions ascend")
}

#[test]
fn recursive_data_checkpoints_round_trip_and_resume()
{
    let original =
        check_program(&mut program(), CheckBudget::DEFAULT).expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    let typings: Vec<&Typing> = checkpoints
        .items()
        .iter()
        .map(gandr_core_incremental::ItemCheckpoint::typing)
        .collect();
    let field = OccurrenceSite::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(0_usize),
    };
    assert_eq!(typings[0], &Typing::Data);
    assert!(matches!(typings[1], Typing::Checked { .. }), "{typings:?}");
    assert!(
        matches!(
            typings[2],
            Typing::Refused(Refusal::ShapeMismatch {
                wanted: gandr_core_checker::ExpectedShape::Arrow,
                ..
            })
        ),
        "{typings:?}"
    );
    assert!(
        matches!(
            typings[3],
            Typing::Refused(Refusal::NotSynthesisable {
                form: gandr_core_incremental::Form::Fixpoint(_)
            })
        ),
        "{typings:?}"
    );
    assert!(matches!(typings[4], Typing::Checked { .. }), "{typings:?}");
    assert_eq!(
        typings[5],
        &Typing::Refused(Refusal::NegativeOccurrence(field))
    );
    assert_eq!(typings[6], &Typing::Data);
    assert_eq!(
        typings[7],
        &Typing::Refused(Refusal::NestedOccurrence(field))
    );
    assert_eq!(
        typings[8],
        &Typing::Refused(Refusal::NonUniformOccurrence(field))
    );
    assert!(
        matches!(
            typings[9],
            Typing::Refused(Refusal::CrossBlockReference { site, .. }) if *site == field
        ),
        "{typings:?}"
    );
    assert_eq!(typings[10], &Typing::Data);
    assert_eq!(
        typings[11],
        &Typing::Refused(Refusal::IndexOccurrence(OccurrenceSite::Parameter(
            ParameterPosition::from(1_usize)
        )))
    );

    let encoded = encode_checkpoints(checkpoints).expect("recursion content and refusals persist");
    let restored = decode_checkpoints(&encoded).expect("they decode");
    assert_eq!(&restored, checkpoints);
    let unchanged = resume_from(&restored, &mut program()).expect("the program is adopted");
    assert_eq!(unchanged.checkpoints(), checkpoints);
    assert!(
        unchanged
            .adoptions()
            .iter()
            .all(|adoption| *adoption == Adoption::Adopted),
        "{:?}",
        unchanged.adoptions()
    );
}

/// `(force head) arguments…`, applied left to right.
///
/// # Specification
/// trivial.
fn applied(
    arena: &mut CoreArena,
    head: ValueId,
    arguments: &[ValueId],
) -> gandr_core_term::ComputationId
{
    let forced = arena.computation_force(head);
    arguments.iter().fold(forced, |applied, &argument| {
        arena.computation_application(applied, argument)
    })
}

/// `Nat`, `List`, `Rose` over `List ⌜Rose⌝`, `map`, and `size` handing its
/// node's children and its own claim to `map` at the plain code `⌜Rose⌝`.
///
/// # Specification
/// - ensures: five items at ascending positions.
/// - panics: only if the program container refuses the fixture.
///
/// # Adequacy
/// - hypothesis: L3 — the one item whose check instantiates a type parameter at
///   a staged code.
/// - witness: `tests::recursive_data::a_staged_instantiation_reaches_no_checkpoint`
#[spec(ensures: |ret| ret.items().len() == 5)]
fn rose_program() -> Program
{
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let nat_data = data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![], vec![nat]], kind),
    );
    let list_data = {
        let code = var(&mut arena, DeBruijnIndex::from(0));
        let head = arena.value_type_element(code, Level::zero());
        let past_head = var(&mut arena, DeBruijnIndex::from(1));
        let tail = arena.value_type_data(ConstantIndex::from(1_usize), vec![past_head]);
        data(
            ConstantIndex::from(1_usize),
            DataSignature::new(vec![kind], vec![vec![], vec![head, tail]], kind),
        )
    };
    let rose = arena.value_type_data(ConstantIndex::from(2_usize), vec![]);
    let rose_code = arena.value_quote(rose);
    let kids = arena.value_type_data(ConstantIndex::from(1_usize), vec![rose_code]);
    let rose_data = data(
        ConstantIndex::from(2_usize),
        DataSignature::new(vec![], vec![vec![kids]], kind),
    );
    let map = {
        // Under Π a Π b: `a` 1, `b` 0.
        let a = var(&mut arena, DeBruijnIndex::from(1));
        let b = var(&mut arena, DeBruijnIndex::from(0));
        let source = arena.value_type_element(a, Level::zero());
        let target = arena.value_type_element(b, Level::zero());
        let into = arena.comp_type_returner(target);
        let step = arena.comp_type_arrow(source, into);
        let step = arena.value_type_thunk(step);
        let from = arena.value_type_data(ConstantIndex::from(1_usize), vec![a]);
        let to = arena.value_type_data(ConstantIndex::from(1_usize), vec![b]);
        let into_list = arena.comp_type_returner(to);
        let last = arena.comp_type_arrow(from, into_list);
        let middle = arena.comp_type_arrow(step, last);
        let inner = arena.comp_type_pi(kind, middle);
        let outer = arena.comp_type_pi(kind, inner);
        let declared = arena.value_type_thunk(outer);
        // Under λxs: `xs` 0, `m` 1, `g` 2, `b` 3; the motive binds the
        // scrutinee once more.
        let element = var(&mut arena, DeBruijnIndex::from(4));
        let to = arena.value_type_data(ConstantIndex::from(1_usize), vec![element]);
        let motive = arena.comp_type_returner(to);
        let element = var(&mut arena, DeBruijnIndex::from(3));
        let to = arena.value_type_data(ConstantIndex::from(1_usize), vec![element]);
        let nil = arena.value_constructor(to, ConstructorTag::from(0_usize), vec![]);
        let on_nil = arena.computation_return(nil);
        // Under λx λrest: `rest` 0, `x` 1, `m` 3, `g` 4; under `y`, `rest`
        // 1 and `m` 4; under `r`, `r` 0, `y` 1 and `b` 7.
        let function = var(&mut arena, DeBruijnIndex::from(4));
        let head = var(&mut arena, DeBruijnIndex::from(1));
        let mapped = applied(&mut arena, function, &[head]);
        let recursive = var(&mut arena, DeBruijnIndex::from(4));
        let rest = var(&mut arena, DeBruijnIndex::from(1));
        let recursed = applied(&mut arena, recursive, &[rest]);
        let element = var(&mut arena, DeBruijnIndex::from(7));
        let to = arena.value_type_data(ConstantIndex::from(1_usize), vec![element]);
        let image = var(&mut arena, DeBruijnIndex::from(1));
        let images = var(&mut arena, DeBruijnIndex::from(0));
        let cons = arena.value_constructor(to, ConstructorTag::from(1_usize), vec![image, images]);
        let returned = arena.computation_return(cons);
        let inner = arena.computation_bind(recursed, returned);
        let outer = arena.computation_bind(mapped, inner);
        let rest_lambda = arena.computation_lambda(outer);
        let on_cons = arena.computation_lambda(rest_lambda);
        let xs = var(&mut arena, DeBruijnIndex::from(0));
        let case = arena.computation_data_case(xs, motive, vec![on_nil, on_cons]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        let body = (0_u8 .. 3).fold(fixpoint, |body, _binder| arena.computation_lambda(body));
        let body = arena.value_thunk(body);
        definition(ConstantIndex::from(3_usize), declared, body)
    };
    let size = {
        let returner = arena.comp_type_returner(nat);
        let classifier = arena.comp_type_arrow(rose, returner);
        let declared = arena.value_type_thunk(classifier);
        let nat_code = arena.value_quote(nat);
        let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
        let one = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![zero]);
        let counted = arena.computation_return(one);
        // The node's arm under `kids` 0, `t` 1, `s` 2.
        let helper = arena.value_constant(ConstantIndex::from(3_usize));
        let claim = var(&mut arena, DeBruijnIndex::from(2));
        let children = var(&mut arena, DeBruijnIndex::from(0));
        let mapped = applied(&mut arena, helper, &[rose_code, nat_code, claim, children]);
        let on_node = arena.computation_bind(mapped, counted);
        let on_node = arena.computation_lambda(on_node);
        let t = var(&mut arena, DeBruijnIndex::from(0));
        let case = arena.computation_data_case(t, returner, vec![on_node]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        let body = arena.value_thunk(fixpoint);
        definition(ConstantIndex::from(4_usize), declared, body)
    };
    Program::new(arena, vec![
        Item::new(ItemKey::from("Nat"), nat_data),
        Item::new(ItemKey::from("List"), list_data),
        Item::new(ItemKey::from("Rose"), rose_data),
        Item::new(ItemKey::from("map"), map),
        Item::new(ItemKey::from("size"), size),
    ])
    .expect("fixture positions ascend")
}

#[test]
fn a_staged_instantiation_reaches_no_checkpoint()
{
    // `size` checks only by instantiating `map`'s element at its children's
    // stage; that instantiation lives in the judgement, never in the item, so
    // the checkpoint holds no stage — a staged type would persist as an
    // unresolved node and refuse to encode — and resumes unchanged.
    let original = check_program(&mut rose_program(), CheckBudget::DEFAULT)
        .expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    let typings: Vec<&Typing> = checkpoints
        .items()
        .iter()
        .map(gandr_core_incremental::ItemCheckpoint::typing)
        .collect();
    assert!(matches!(typings[3], Typing::Checked { .. }), "{typings:?}");
    assert!(matches!(typings[4], Typing::Checked { .. }), "{typings:?}");
    let encoded = encode_checkpoints(checkpoints).expect("no stage reaches a checkpoint");
    let restored = decode_checkpoints(&encoded).expect("they decode");
    assert_eq!(&restored, checkpoints);
    let unchanged = resume_from(&restored, &mut rose_program()).expect("the program is adopted");
    assert_eq!(unchanged.checkpoints(), checkpoints);
    assert!(
        unchanged
            .adoptions()
            .iter()
            .all(|adoption| *adoption == Adoption::Adopted),
        "{:?}",
        unchanged.adoptions()
    );
}
