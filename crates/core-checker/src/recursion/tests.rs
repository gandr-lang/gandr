use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_core::stage_order::below;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::Standing;
use quenchant_shape::shape::Maybe;

use crate::bridge;
use crate::bridge::Outcome;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::Judged;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;
use crate::refusal::UnadmittedFormer;

/// The variable at `index`.
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

/// `(force head) arguments…`.
///
/// # Specification
/// trivial.
fn call(
    arena: &mut CoreArena,
    head: ValueId,
    arguments: &[ValueId],
) -> ComputationId
{
    let mut built = arena.computation_force(head);
    for &argument in arguments {
        built = arena.computation_application(built, argument);
    }
    built
}

/// The universe of small value types.
///
/// # Specification
/// trivial.
fn kind(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// The data type at `constant`, applied to `arguments`.
///
/// # Specification
/// trivial.
fn data(
    arena: &mut CoreArena,
    constant: ConstantIndex,
    arguments: Vec<ValueId>,
) -> ValueTypeId
{
    arena.value_type_data(constant, arguments)
}

/// `El code`.
///
/// # Specification
/// trivial.
fn element(
    arena: &mut CoreArena,
    code: ValueId,
) -> ValueTypeId
{
    arena.value_type_element(code, Level::zero())
}

/// A data declaration at `constant`.
///
/// # Specification
/// trivial.
fn declare_data(
    constant: ConstantIndex,
    signature: DataSignature,
) -> Declaration
{
    Declaration::data(
        constant,
        Arc::new(signature),
        OriginToken::from(usize::from(constant)),
    )
}

/// A definition at `constant`, declared at `declared`.
///
/// # Specification
/// trivial.
fn define(
    constant: ConstantIndex,
    declared: ValueTypeId,
    body: ValueId,
) -> Declaration
{
    Declaration::new(
        constant,
        Maybe::Present(declared),
        Maybe::Present(body),
        OriginToken::from(usize::from(constant)),
    )
}

/// `Nat`, at position 0: `Zero`, `Succ Nat`.
///
/// # Specification
/// trivial.
fn nat_signature(arena: &mut CoreArena) -> DataSignature
{
    let kind = kind(arena);
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    DataSignature::new(vec![], vec![vec![], vec![nat]], kind)
}

/// `Zero`.
///
/// # Specification
/// trivial.
fn zero(arena: &mut CoreArena) -> ValueId
{
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![])
}

/// `Succ value`.
///
/// # Specification
/// trivial.
fn succ(
    arena: &mut CoreArena,
    value: ValueId,
) -> ValueId
{
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![value])
}

/// `Nat → F Nat`, thunked.
///
/// # Specification
/// trivial.
fn unary(arena: &mut CoreArena) -> ValueTypeId
{
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let returner = arena.comp_type_returner(nat);
    let classifier = arena.comp_type_arrow(nat, returner);
    arena.value_type_thunk(classifier)
}

/// The verdict and the kernel's readmission of each declaration, judged as
/// one module.
///
/// # Specification
/// trivial.
fn judge(
    arena: &mut CoreArena,
    declarations: &[Declaration],
) -> (Vec<Verdict>, Vec<Outcome>)
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, declarations);
    let readmission = bridge::readmit(arena, &report);
    (
        report.judged().iter().map(Judged::verdict).collect(),
        readmission
            .readmitted()
            .iter()
            .map(|readmitted| readmitted.outcome().clone())
            .collect(),
    )
}

/// `Nat`, then at position 1 a recursion `fix f. λ. λ. case …` over `Nat →
/// Nat → F Nat` claiming `evidence`: the case is on the variable
/// `scrutinee` under the two lambdas, its zero arm returns the variable
/// `returned`, and its successor arm calls `f` on what `arguments` builds
/// under `p` 0, then the second parameter 1, the first 2, `f` 3.
///
/// # Specification
/// trivial.
fn two_parameter(
    arena: &mut CoreArena,
    evidence: FixpointEvidence,
    (scrutinee, returned): (DeBruijnIndex, DeBruijnIndex),
    arguments: impl FnOnce(&mut CoreArena) -> Vec<ValueId>,
) -> Vec<Declaration>
{
    let nat_signature = nat_signature(arena);
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let returner = arena.comp_type_returner(nat);
    let inner = arena.comp_type_arrow(nat, returner);
    let classifier = arena.comp_type_arrow(nat, inner);
    let declared = arena.value_type_thunk(classifier);
    let scrutinee = var(arena, scrutinee);
    let returned = var(arena, returned);
    let on_zero = arena.computation_return(returned);
    let recursive = var(arena, DeBruijnIndex::from(3));
    let built = arguments(arena);
    let called = call(arena, recursive, &built);
    let on_successor = arena.computation_lambda(called);
    let case = arena.computation_data_case(scrutinee, returner, vec![on_zero, on_successor]);
    let second = arena.computation_lambda(case);
    let first = arena.computation_lambda(second);
    let fixpoint = arena.computation_fixpoint(first, evidence);
    let body = arena.value_thunk(fixpoint);
    vec![
        declare_data(ConstantIndex::from(0), nat_signature),
        define(ConstantIndex::from(1), declared, body),
    ]
}

#[test]
fn a_recursion_descends_on_its_first_parameter()
{
    // plus(Succ p, n) = plus(p, Succ n): the first parameter descends and the
    // second varies; both checkers admit it.
    let mut arena = CoreArena::new();
    let declarations = two_parameter(
        &mut arena,
        FixpointEvidence::StructuralDescent,
        (DeBruijnIndex::from(1), DeBruijnIndex::from(0)),
        |arena| {
            let p = var(arena, DeBruijnIndex::from(0));
            let n = var(arena, DeBruijnIndex::from(1));
            let bumped = succ(arena, n);
            vec![p, bumped]
        },
    );
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[1], Verdict::Checked { .. }),
        "{:?}",
        verdicts[1]
    );
    assert!(
        matches!(outcomes[1], Outcome::Defined { .. }),
        "{:?}",
        outcomes[1]
    );

    // plus(n, Succ p) = plus(Succ n, p), claiming the second parameter: the
    // staged position names it, and both checkers admit it.
    let mut arena = CoreArena::new();
    let declarations = two_parameter(
        &mut arena,
        FixpointEvidence::Staged {
            position: StagedPosition::from(1_usize),
        },
        (DeBruijnIndex::from(0), DeBruijnIndex::from(1)),
        |arena| {
            let p = var(arena, DeBruijnIndex::from(0));
            let n = var(arena, DeBruijnIndex::from(2));
            let bumped = succ(arena, n);
            vec![bumped, p]
        },
    );
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[1], Verdict::Checked { .. }),
        "{:?}",
        verdicts[1]
    );
    assert!(
        matches!(outcomes[1], Outcome::Defined { .. }),
        "{:?}",
        outcomes[1]
    );

    // The control: the staged first parameter handed the second, which
    // stands at no stage.
    let mut arena = CoreArena::new();
    let declarations = two_parameter(
        &mut arena,
        FixpointEvidence::StructuralDescent,
        (DeBruijnIndex::from(1), DeBruijnIndex::from(0)),
        |arena| {
            let p = var(arena, DeBruijnIndex::from(0));
            let n = var(arena, DeBruijnIndex::from(1));
            vec![n, p]
        },
    );
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[1],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Top,
                bound,
                ..
            }) if bound == below(Stage::At(StageId::from(0_usize)))
        ),
        "{:?}",
        verdicts[1]
    );
}

/// What a predecessor's successor arm returns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Returning
{
    /// The field `p`, below the argument.
    Field,
    /// `Succ n`, one step above the argument.
    Successor,
}

/// `Nat`; at position 1 `pred : U (Nat → F Nat)`, `fix f. λn. case n { Zero ⇒
/// return Zero ; Succ ⇒ λp. return v }`, `v` what `returning` names under `p`
/// 0, `n` 1; at position 2 `halve`, `fix h. λn. case n { Zero ⇒ return Zero ;
/// Succ ⇒ λp. q ← (force pred) p; (force h) q }`, under `q` 0, `p` 1, `n` 2,
/// `h` 3.
///
/// # Specification
/// trivial.
fn through_predecessor(
    arena: &mut CoreArena,
    returning: Returning,
) -> Vec<Declaration>
{
    let nat_signature = nat_signature(arena);
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let returner = arena.comp_type_returner(nat);
    let declared = unary(arena);
    let fixpoint = |arena: &mut CoreArena, on_successor| {
        let on_zero = {
            let zero = zero(arena);
            arena.computation_return(zero)
        };
        let scrutinee = var(arena, DeBruijnIndex::from(0));
        let case = arena.computation_data_case(scrutinee, returner, vec![on_zero, on_successor]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        arena.value_thunk(fixpoint)
    };
    let given = match returning {
        Returning::Field => var(arena, DeBruijnIndex::from(0)),
        Returning::Successor => {
            let argument = var(arena, DeBruijnIndex::from(1));
            succ(arena, argument)
        },
    };
    let given = arena.computation_return(given);
    let on_successor = arena.computation_lambda(given);
    let pred = fixpoint(arena, on_successor);
    let head = arena.value_constant(ConstantIndex::from(1));
    let field = var(arena, DeBruijnIndex::from(0));
    let predecessor = call(arena, head, &[field]);
    let recursive = var(arena, DeBruijnIndex::from(3));
    let bound = var(arena, DeBruijnIndex::from(0));
    let recursed = call(arena, recursive, &[bound]);
    let bind = arena.computation_bind(predecessor, recursed);
    let on_successor = arena.computation_lambda(bind);
    let halve = fixpoint(arena, on_successor);
    vec![
        declare_data(ConstantIndex::from(0), nat_signature),
        define(ConstantIndex::from(1), declared, pred),
        define(ConstantIndex::from(2), declared, halve),
    ]
}

#[test]
fn a_result_follows_the_parameter_it_recurses_on()
{
    // A predecessor returning its field returns at its argument's stage, so
    // `halve` recursing on the predecessor of its own field descends, and
    // both checkers admit it.
    let mut arena = CoreArena::new();
    let declarations = through_predecessor(&mut arena, Returning::Field);
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[2], Verdict::Checked { .. }),
        "{:?}",
        verdicts[2]
    );
    assert!(
        matches!(outcomes[2], Outcome::Defined { .. }),
        "{:?}",
        outcomes[2]
    );

    // One returning `Succ n` stands above its argument, so its result stands
    // at no stage and the same recursion is refused at the top.
    let mut arena = CoreArena::new();
    let declarations = through_predecessor(&mut arena, Returning::Successor);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[1], Verdict::Checked { .. }),
        "{:?}",
        verdicts[1]
    );
    assert!(
        matches!(
            verdicts[2],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Top,
                bound,
                ..
            }) if bound == below(Stage::At(StageId::from(0_usize)))
        ),
        "{:?}",
        verdicts[2]
    );
}

#[test]
fn a_structural_fixpoint_needs_an_arrow_to_recurse_on()
{
    let body = |arena: &mut CoreArena, evidence| {
        let nat_signature = nat_signature(arena);
        let nat = data(arena, ConstantIndex::from(0), vec![]);
        let returner = arena.comp_type_returner(nat);
        let declared = arena.value_type_thunk(returner);
        let zero = zero(arena);
        let returned = arena.computation_return(zero);
        let fixpoint = arena.computation_fixpoint(returned, evidence);
        let body = arena.value_thunk(fixpoint);
        vec![
            declare_data(ConstantIndex::from(0), nat_signature),
            define(ConstantIndex::from(1), declared, body),
        ]
    };
    let mut arena = CoreArena::new();
    let declarations = body(&mut arena, FixpointEvidence::StructuralDescent);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[1],
            Verdict::Refused(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Arrow,
                ..
            })
        ),
        "{:?}",
        verdicts[1]
    );
    // The control: the same fixpoint, partial, checks at any type.
    let mut arena = CoreArena::new();
    let declarations = body(&mut arena, FixpointEvidence::Partial);
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[1], Verdict::Checked { .. }),
        "{:?}",
        verdicts[1]
    );
    assert!(
        matches!(outcomes[1], Outcome::Defined { .. }),
        "{:?}",
        outcomes[1]
    );
}

/// `Nat`, then at position 1 `fix f. λn. case n { Zero ↦ Zero; Succ p ↦
/// case p { Zero ↦ Zero; Succ q ↦ f (argument) } }`, `argument` built under
/// `q` 0, `p` 1, `n` 2, `f` 3.
///
/// # Specification
/// trivial.
fn two_deep(
    arena: &mut CoreArena,
    argument: impl FnOnce(&mut CoreArena) -> ValueId,
) -> Vec<Declaration>
{
    let nat_signature = nat_signature(arena);
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let returner = arena.comp_type_returner(nat);
    let declared = unary(arena);
    let zero = zero(arena);
    let on_zero = arena.computation_return(zero);
    let recursive = var(arena, DeBruijnIndex::from(3));
    let built = argument(arena);
    let called = call(arena, recursive, &[built]);
    let on_inner = arena.computation_lambda(called);
    let inner_scrutinee = var(arena, DeBruijnIndex::from(0));
    let inner = arena.computation_data_case(inner_scrutinee, returner, vec![on_zero, on_inner]);
    let on_outer = arena.computation_lambda(inner);
    let outer_scrutinee = var(arena, DeBruijnIndex::from(0));
    let outer = arena.computation_data_case(outer_scrutinee, returner, vec![on_zero, on_outer]);
    let lambda = arena.computation_lambda(outer);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    vec![
        declare_data(ConstantIndex::from(0), nat_signature),
        define(ConstantIndex::from(1), declared, body),
    ]
}

#[test]
fn a_call_on_a_value_rebuilt_below_the_stage_is_admitted()
{
    // f(Succ q) under n = Succ (Succ q): below n by one, and both checkers
    // admit it.
    let mut arena = CoreArena::new();
    let declarations = two_deep(&mut arena, |arena| {
        let q = var(arena, DeBruijnIndex::from(0));
        succ(arena, q)
    });
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[1], Verdict::Checked { .. }),
        "{:?}",
        verdicts[1]
    );
    assert!(
        matches!(outcomes[1], Outcome::Defined { .. }),
        "{:?}",
        outcomes[1]
    );

    // f(Succ p) under n = Succ p: `n` itself. Its field `p` stands at the
    // outer case's stage, one below the fixpoint's, where two are wanted.
    let mut arena = CoreArena::new();
    let declarations = two_deep(&mut arena, |arena| {
        let p = var(arena, DeBruijnIndex::from(1));
        succ(arena, p)
    });
    let (verdicts, _) = judge(&mut arena, &declarations);
    let root = Stage::At(StageId::from(0_usize));
    assert!(
        matches!(
            verdicts[1],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Staged(Stage::At(found)),
                bound,
                ..
            }) if found == StageId::from(1_usize) && bound == below(below(root))
        ),
        "{:?}",
        verdicts[1]
    );
}

/// The arm of [`nullary_call`]'s case that calls `f Zero`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CallingArm
{
    /// The zero arm, which binds nothing.
    Zero,
    /// The successor arm, under its field.
    Successor,
}

/// `Nat`, then at position 1 `fix f. λn. case n { Zero ↦ on_zero; Succ p ↦
/// on_successor }`, the `calling` arm `f Zero` and the other `return Zero`.
///
/// # Specification
/// trivial.
fn nullary_call(
    arena: &mut CoreArena,
    calling: CallingArm,
) -> Vec<Declaration>
{
    let nat_signature = nat_signature(arena);
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let returner = arena.comp_type_returner(nat);
    let declared = unary(arena);
    let arm = |arena: &mut CoreArena, calls, recursive| {
        let zero = zero(arena);
        if calls {
            let recursive = var(arena, DeBruijnIndex::from(recursive));
            call(arena, recursive, &[zero])
        }
        else {
            arena.computation_return(zero)
        }
    };
    // Under the zero arm: `n` 0, `f` 1; under the successor's field: `p` 0,
    // `n` 1, `f` 2.
    let on_zero = arm(arena, calling == CallingArm::Zero, 1);
    let on_successor = arm(arena, calling == CallingArm::Successor, 2);
    let on_successor = arena.computation_lambda(on_successor);
    let scrutinee = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(scrutinee, returner, vec![on_zero, on_successor]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    vec![
        declare_data(ConstantIndex::from(0), nat_signature),
        define(ConstantIndex::from(1), declared, body),
    ]
}

#[test]
fn a_nullary_argument_needs_a_value_below_the_stage()
{
    // `f Zero` under `Succ p`: `p` is a value below the fixpoint's stage, so
    // that stage is not the empty first one, and both checkers admit it.
    let mut arena = CoreArena::new();
    let declarations = nullary_call(&mut arena, CallingArm::Successor);
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[1], Verdict::Checked { .. }),
        "{:?}",
        verdicts[1]
    );
    assert!(
        matches!(outcomes[1], Outcome::Defined { .. }),
        "{:?}",
        outcomes[1]
    );

    // `f Zero` under `Zero`: nothing in scope stands below the stage, which
    // may be the first, and `f Zero` there need not terminate.
    let mut arena = CoreArena::new();
    let declarations = nullary_call(&mut arena, CallingArm::Zero);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[1],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Top,
                bound,
                ..
            }) if bound == below(Stage::At(StageId::from(0_usize)))
        ),
        "{:?}",
        verdicts[1]
    );
}

#[test]
fn a_constructor_of_plain_fields_needs_a_value_below_the_stage()
{
    // `T = Leaf Integer | Node T`, and `fix f. λt. case t { Leaf n ⇒ f (Leaf
    // n) ; Node c ⇒ return c }`: `Leaf n` holds no recursive field, so it
    // stands at no stage below `t`'s, and under `Leaf` nothing in scope
    // stands below the fixpoint's stage.
    let mut arena = CoreArena::new();
    let kind = kind(&mut arena);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let own = data(&mut arena, ConstantIndex::from(0), vec![]);
    let signature = DataSignature::new(vec![], vec![vec![integer], vec![own]], kind);
    let returner = arena.comp_type_returner(own);
    let arrow = arena.comp_type_arrow(own, returner);
    let declared = arena.value_type_thunk(arrow);
    // Under `Leaf`'s field: `n` 0, `t` 1, `f` 2.
    let n = var(&mut arena, DeBruijnIndex::from(0));
    let leaf = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![n]);
    let recursive = var(&mut arena, DeBruijnIndex::from(2));
    let on_leaf = call(&mut arena, recursive, &[leaf]);
    let on_leaf = arena.computation_lambda(on_leaf);
    let child = var(&mut arena, DeBruijnIndex::from(0));
    let on_node = arena.computation_return(child);
    let on_node = arena.computation_lambda(on_node);
    let scrutinee = var(&mut arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(scrutinee, returner, vec![on_leaf, on_node]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    let declarations = vec![
        declare_data(ConstantIndex::from(0), signature),
        define(ConstantIndex::from(1), declared, body),
    ];
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[1],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Top,
                ..
            })
        ),
        "{:?}",
        verdicts[1]
    );
}

/// `Empty` at 0, `T = Mk (U (Empty → F T))` at 1, and at 2 `fix f. λt. f (Mk
/// (thunk (λx. fix y. force y)))` claiming `evidence`, the inner fixpoint
/// partial.
///
/// # Specification
/// trivial.
fn thunked_call(
    arena: &mut CoreArena,
    evidence: FixpointEvidence,
) -> Vec<Declaration>
{
    let kind = kind(arena);
    let empty_signature = DataSignature::new(vec![], vec![], kind);
    let empty = data(arena, ConstantIndex::from(0), vec![]);
    let own = data(arena, ConstantIndex::from(1), vec![]);
    let into = arena.comp_type_returner(own);
    let branch = arena.comp_type_arrow(empty, into);
    let field = arena.value_type_thunk(branch);
    let signature = DataSignature::new(vec![], vec![vec![field]], kind);
    let arrow = arena.comp_type_arrow(own, into);
    let declared = arena.value_type_thunk(arrow);
    // Under λx, fix y: `y` 0.
    let y = var(arena, DeBruijnIndex::from(0));
    let forced = arena.computation_force(y);
    let diverging = arena.computation_fixpoint(forced, FixpointEvidence::Partial);
    let lambda = arena.computation_lambda(diverging);
    let thunked = arena.value_thunk(lambda);
    let built = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![thunked]);
    // Under λt: `t` 0, `f` 1.
    let recursive = var(arena, DeBruijnIndex::from(1));
    let called = call(arena, recursive, &[built]);
    let lambda = arena.computation_lambda(called);
    let fixpoint = arena.computation_fixpoint(lambda, evidence);
    let body = arena.value_thunk(fixpoint);
    vec![
        declare_data(ConstantIndex::from(0), empty_signature),
        declare_data(ConstantIndex::from(1), signature),
        define(ConstantIndex::from(2), declared, body),
    ]
}

#[test]
fn a_thunked_field_shows_no_value_below_the_stage_598()
{
    // #598: `Mk`'s one recursive field is thunked, and the thunk never
    // returns, so `Mk (…)` holds no value below the stage and nothing in
    // scope shows the stage is above the first: `f (Mk …)` calls itself
    // forever.
    let mut arena = CoreArena::new();
    let declarations = thunked_call(&mut arena, FixpointEvidence::StructuralDescent);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[2],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Top,
                bound,
                ..
            }) if bound == below(Stage::At(StageId::from(0_usize)))
        ),
        "{:?}",
        verdicts[2]
    );
    // The control: claiming nothing, the same fixpoint is partial, and at a
    // row that does not state `Div` it is refused by the divergence rule, not
    // the stage rule.
    let mut arena = CoreArena::new();
    let declarations = thunked_call(&mut arena, FixpointEvidence::Partial);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[2],
            Verdict::Refused(CheckRefusal::TypeMismatch(
                crate::refusal::Mismatch::Computation { .. }
            ))
        ),
        "{:?}",
        verdicts[2]
    );
}

/// `List a`, at position 1: `Nil`, `Cons (El a) (List a)`.
///
/// # Specification
/// trivial.
fn list_signature(arena: &mut CoreArena) -> DataSignature
{
    let kind = kind(arena);
    let code = var(arena, DeBruijnIndex::from(0));
    let head = element(arena, code);
    // The tail stands past the head's binder: the element code is one out.
    let past_head = var(arena, DeBruijnIndex::from(1));
    let tail = data(arena, ConstantIndex::from(1), vec![past_head]);
    DataSignature::new(vec![kind], vec![vec![], vec![head, tail]], kind)
}

/// `Rose`, at position 2: `Node (List Rose)`.
///
/// # Specification
/// trivial.
fn rose_signature(arena: &mut CoreArena) -> DataSignature
{
    let kind = kind(arena);
    let rose = data(arena, ConstantIndex::from(2), vec![]);
    let code = arena.value_quote(rose);
    let kids = data(arena, ConstantIndex::from(1), vec![code]);
    DataSignature::new(vec![], vec![vec![kids]], kind)
}

/// `map : Π(a b : Type). U (El a → F (El b)) → List a → F (List b)` at
/// position 3, a structural fixpoint over its list.
///
/// # Specification
/// trivial.
fn map_declaration(arena: &mut CoreArena) -> Declaration
{
    let declared = {
        // Under Π a Π b: `a` 1, `b` 0.
        let a = var(arena, DeBruijnIndex::from(1));
        let b = var(arena, DeBruijnIndex::from(0));
        let source = element(arena, a);
        let target = element(arena, b);
        let into = arena.comp_type_returner(target);
        let step = arena.comp_type_arrow(source, into);
        let step = arena.value_type_thunk(step);
        let from = data(arena, ConstantIndex::from(1), vec![a]);
        let to = data(arena, ConstantIndex::from(1), vec![b]);
        let into_list = arena.comp_type_returner(to);
        let last = arena.comp_type_arrow(from, into_list);
        let middle = arena.comp_type_arrow(step, last);
        let kind = kind(arena);
        let inner = arena.comp_type_pi(kind, middle);
        let outer = arena.comp_type_pi(kind, inner);
        arena.value_type_thunk(outer)
    };
    // Under λxs: `xs` 0, `m` 1, `g` 2, `b` 3, `a` 4; the motive binds the
    // scrutinee once more.
    let motive = {
        let b = var(arena, DeBruijnIndex::from(4));
        let to = data(arena, ConstantIndex::from(1), vec![b]);
        arena.comp_type_returner(to)
    };
    let on_nil = {
        let b = var(arena, DeBruijnIndex::from(3));
        let to = data(arena, ConstantIndex::from(1), vec![b]);
        let nil = arena.value_constructor(to, ConstructorTag::from(0_usize), vec![]);
        arena.computation_return(nil)
    };
    let on_cons = {
        // Under λx λrest: `rest` 0, `x` 1, `xs` 2, `m` 3, `g` 4, `b` 5, `a` 6.
        let function = var(arena, DeBruijnIndex::from(4));
        let head = var(arena, DeBruijnIndex::from(1));
        let mapped = call(arena, function, &[head]);
        // Under `y`: `m` 4, `rest` 1.
        let recursive = var(arena, DeBruijnIndex::from(4));
        let rest = var(arena, DeBruijnIndex::from(1));
        let recursed = call(arena, recursive, &[rest]);
        // Under `r`: `r` 0, `y` 1, `b` 7.
        let element = var(arena, DeBruijnIndex::from(7));
        let to = data(arena, ConstantIndex::from(1), vec![element]);
        let image = var(arena, DeBruijnIndex::from(1));
        let images = var(arena, DeBruijnIndex::from(0));
        let cons = arena.value_constructor(to, ConstructorTag::from(1_usize), vec![image, images]);
        let returned = arena.computation_return(cons);
        let inner = arena.computation_bind(recursed, returned);
        let outer = arena.computation_bind(mapped, inner);
        let rest_lambda = arena.computation_lambda(outer);
        arena.computation_lambda(rest_lambda)
    };
    let xs = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(xs, motive, vec![on_nil, on_cons]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let g_lambda = arena.computation_lambda(fixpoint);
    let b_lambda = arena.computation_lambda(g_lambda);
    let a_lambda = arena.computation_lambda(b_lambda);
    let body = arena.value_thunk(a_lambda);
    define(ConstantIndex::from(3), declared, body)
}

/// How `size` hands its node's children to `map`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Children
{
    /// The node's own field, at the stage the case bound it.
    Field,
    /// A one-element list of the node itself, at the plain `List Rose`.
    Forged,
}

/// `size : Rose → F Nat` at position 4: `fix s. λt. case t { Node kids ↦
/// map ⌜Rose⌝ ⌜Nat⌝ (λu. s u) children to _. return 1 }`, the codes the
/// plain ones a source writes.
///
/// # Specification
/// trivial.
fn size_declaration(
    arena: &mut CoreArena,
    children: Children,
) -> Declaration
{
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let rose = data(arena, ConstantIndex::from(2), vec![]);
    let returner = arena.comp_type_returner(nat);
    let classifier = arena.comp_type_arrow(rose, returner);
    let declared = arena.value_type_thunk(classifier);
    let map = arena.value_constant(ConstantIndex::from(3_usize));
    let rose_code = arena.value_quote(rose);
    let nat_code = arena.value_quote(nat);
    let zero = zero(arena);
    let one = succ(arena, zero);
    let counted = arena.computation_return(one);
    // The node's arm under `kids` 0, `t` 1, `s` 2; under λu, `s` is 3.
    let mapped_function = {
        let recursive = var(arena, DeBruijnIndex::from(3));
        let u = var(arena, DeBruijnIndex::from(0));
        let called = call(arena, recursive, &[u]);
        let lambda = arena.computation_lambda(called);
        arena.value_thunk(lambda)
    };
    let listed = match children {
        Children::Field => var(arena, DeBruijnIndex::from(0)),
        Children::Forged => {
            let list = data(arena, ConstantIndex::from(1), vec![rose_code]);
            let nil = arena.value_constructor(list, ConstructorTag::from(0_usize), vec![]);
            let t = var(arena, DeBruijnIndex::from(1));
            arena.value_constructor(list, ConstructorTag::from(1_usize), vec![t, nil])
        },
    };
    let mapped = call(arena, map, &[rose_code, nat_code, mapped_function, listed]);
    let on_node = arena.computation_bind(mapped, counted);
    let on_node = arena.computation_lambda(on_node);
    let t = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(t, returner, vec![on_node]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    define(ConstantIndex::from(4), declared, body)
}

/// `Nat`, `List`, `Rose`, `map` and `size` handing `map` `children`, one
/// module.
///
/// # Specification
/// trivial.
fn rose_module(
    arena: &mut CoreArena,
    children: Children,
) -> Vec<Declaration>
{
    let nat = nat_signature(arena);
    let list = list_signature(arena);
    let rose = rose_signature(arena);
    let map = map_declaration(arena);
    let size = size_declaration(arena, children);
    vec![
        declare_data(ConstantIndex::from(0), nat),
        declare_data(ConstantIndex::from(1), list),
        declare_data(ConstantIndex::from(2), rose),
        map,
        size,
    ]
}

/// `Nat`, then `apply : Π(a b : Type). U (El a → F (El b)) → El a → F (El
/// b)` at position 1, `λa λb λf λx. f x`, then `count : Nat → F Nat` at
/// position 2, `fix c. λn. case n { Zero ↦ return Zero; Succ p ↦ apply ⌜Nat⌝
/// ⌜Nat⌝ c v }`, `v` the variable `handed` under `p` 0, `n` 1, `c` 2.
///
/// # Specification
/// trivial.
fn count_module(
    arena: &mut CoreArena,
    handed: DeBruijnIndex,
) -> Vec<Declaration>
{
    let nat_signature = nat_signature(arena);
    let apply = {
        // Under Π a Π b: `a` 1, `b` 0.
        let a = var(arena, DeBruijnIndex::from(1));
        let b = var(arena, DeBruijnIndex::from(0));
        let source = element(arena, a);
        let target = element(arena, b);
        let into = arena.comp_type_returner(target);
        let function = arena.comp_type_arrow(source, into);
        let thunked = arena.value_type_thunk(function);
        let applying = arena.comp_type_arrow(thunked, function);
        let kind = kind(arena);
        let inner = arena.comp_type_pi(kind, applying);
        let outer = arena.comp_type_pi(kind, inner);
        let declared = arena.value_type_thunk(outer);
        // Under λa λb λf λx: `x` 0, `f` 1.
        let function = var(arena, DeBruijnIndex::from(1));
        let argument = var(arena, DeBruijnIndex::from(0));
        let called = call(arena, function, &[argument]);
        let body = (0_u8 .. 4).fold(called, |body, _binder| arena.computation_lambda(body));
        let body = arena.value_thunk(body);
        define(ConstantIndex::from(1), declared, body)
    };
    let nat = data(arena, ConstantIndex::from(0), vec![]);
    let nat_code = arena.value_quote(nat);
    let returner = arena.comp_type_returner(nat);
    let classifier = arena.comp_type_arrow(nat, returner);
    let declared = arena.value_type_thunk(classifier);
    let helper = arena.value_constant(ConstantIndex::from(1_usize));
    let claim = var(arena, DeBruijnIndex::from(2));
    let handed = var(arena, handed);
    let counted = call(arena, helper, &[nat_code, nat_code, claim, handed]);
    let on_successor = arena.computation_lambda(counted);
    let zero = zero(arena);
    let on_zero = arena.computation_return(zero);
    let n = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(n, returner, vec![on_zero, on_successor]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    vec![
        declare_data(ConstantIndex::from(0), nat_signature),
        apply,
        define(ConstantIndex::from(2), declared, body),
    ]
}

#[test]
fn a_type_parameter_instantiates_at_a_staged_code()
{
    // `kids : List ⌜Rose^{ι1}⌝`, bound by the case one stage below `t`,
    // instantiates `map`'s element at `Rose^{ι1}`, so `λu. s u` takes a `u`
    // below the node's stage (#393).
    let mut arena = CoreArena::new();
    let declarations = rose_module(&mut arena, Children::Field);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[3], Verdict::Checked { .. }),
        "{:?}",
        verdicts[3]
    );
    assert!(
        matches!(verdicts[4], Verdict::Checked { .. }),
        "{:?}",
        verdicts[4]
    );

    // The predecessor `p : Nat^{ι1}` instantiates `apply`'s parameter at its
    // own stage, which the claim takes.
    let mut arena = CoreArena::new();
    let declarations = count_module(&mut arena, DeBruijnIndex::from(0));
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[2], Verdict::Checked { .. }),
        "{:?}",
        verdicts[2]
    );
}

#[test]
fn a_staged_instantiation_erases_and_readmits()
{
    // The term keeps the plain code the source wrote, so it crosses with no
    // stage for the bridge to refuse, and the kernel re-derives the stage from
    // the argument that holds it: each recursion is defined there.
    let mut rose = CoreArena::new();
    let declarations = rose_module(&mut rose, Children::Field);
    let sized = judge(&mut rose, &declarations);
    let mut count = CoreArena::new();
    let declarations = count_module(&mut count, DeBruijnIndex::from(0));
    let counted = judge(&mut count, &declarations);
    for ((verdicts, outcomes), at) in [(sized, 4_usize), (counted, 2_usize)] {
        assert!(
            matches!(verdicts[at], Verdict::Checked { .. }),
            "{:?}",
            verdicts[at]
        );
        assert!(
            matches!(outcomes[at], Outcome::Defined { .. }),
            "{:?}",
            outcomes[at]
        );
    }
}

#[test]
fn a_claim_at_the_scrutinee_through_map_is_refused()
{
    // The node itself in a list of its own stands at no stage, so `map`'s
    // element stays the plain `Rose` and `λu. s u` takes any node.
    let root = Stage::At(StageId::from(0_usize));
    let mut arena = CoreArena::new();
    let declarations = rose_module(&mut arena, Children::Forged);
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[4],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Top,
                bound,
                ..
            }) if bound == below(root)
        ),
        "{:?}",
        verdicts[4]
    );

    // The parameter `n` itself instantiates `apply`'s parameter at the root,
    // which the claim's bound does not reach.
    let mut arena = CoreArena::new();
    let declarations = count_module(&mut arena, DeBruijnIndex::from(1));
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[2],
            Verdict::Refused(CheckRefusal::StageNotBelow {
                found: Standing::Staged(found),
                bound,
                ..
            }) if found == root && bound == below(root)
        ),
        "{:?}",
        verdicts[2]
    );
}

#[test]
fn a_staged_type_never_crosses_to_the_kernel()
{
    // A stage is the judgement's own: a term naming one, here the code of a
    // stage this declaration never minted, is refused before the kernel is
    // offered anything.
    let mut arena = CoreArena::new();
    let nat_signature = nat_signature(&mut arena);
    let nat = data(&mut arena, ConstantIndex::from(0), vec![]);
    let staged = arena.value_type_staged(nat, Stage::At(StageId::from(0_usize)));
    let code = arena.value_quote(staged);
    let declared = kind(&mut arena);
    let declarations = [
        declare_data(ConstantIndex::from(0), nat_signature),
        define(ConstantIndex::from(1), declared, code),
    ];
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(outcomes[1], Outcome::Marked(_)),
        "{:?}",
        outcomes[1]
    );
    assert!(
        matches!(
            verdicts[1],
            Verdict::Refused(CheckRefusal::OutOfFragment {
                former: UnadmittedFormer::Stage,
                ..
            })
        ),
        "{:?}",
        verdicts[1]
    );
}
