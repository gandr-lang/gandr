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
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageBinder;
use gandr_kernel_term::StageBound;
use gandr_kernel_term::StageDepth;
use gandr_kernel_term::StageId;
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

/// `Nat`.
///
/// # Specification
/// trivial.
fn nat(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_data(ConstantIndex::from(0), vec![])
}

/// `Nat` at position 0: `Zero`, `Succ Nat`.
///
/// # Specification
/// trivial.
fn declare_nat(arena: &mut CoreArena) -> Declaration
{
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let nat = nat(arena);
    Declaration::data(
        ConstantIndex::from(0),
        Arc::new(DataSignature::new(vec![], vec![vec![], vec![nat]], kind)),
        OriginToken::from(0_usize),
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

/// `U (domain → F Nat)`.
///
/// # Specification
/// trivial.
fn function_of(
    arena: &mut CoreArena,
    domain: ValueTypeId,
) -> ValueTypeId
{
    let nat = nat(arena);
    let returner = arena.comp_type_returner(nat);
    let arrow = arena.comp_type_arrow(domain, returner);
    arena.value_type_thunk(arrow)
}

/// `applyAt @[i : Size] (f : U (Nat[<i] → F Nat), x : Nat[<i]) : F Nat =
/// (force f) x` at position 1, each `<i` written as the stage below binder 0
/// by `reach`, quantified over `bounds`.
///
/// # Specification
/// trivial.
fn apply_at(
    arena: &mut CoreArena,
    bounds: Vec<StageBound>,
) -> Declaration
{
    let nat = nat(arena);
    let below_i = arena.value_type_staged(nat, Stage::Below {
        anchor: StageId::from(0_usize),
        depth: StageDepth::from(core::num::NonZeroU32::MIN),
    });
    let function = function_of(arena, below_i);
    let returner = arena.comp_type_returner(nat);
    let inner = arena.comp_type_arrow(below_i, returner);
    let outer = arena.comp_type_arrow(function, inner);
    let declared = arena.value_type_thunk(outer);
    let f = var(arena, DeBruijnIndex::from(1));
    let x = var(arena, DeBruijnIndex::from(0));
    let applied = call(arena, f, &[x]);
    let second = arena.computation_lambda(applied);
    let first = arena.computation_lambda(second);
    let body = arena.value_thunk(first);
    define(ConstantIndex::from(1), declared, body).staged(bounds)
}

/// `helped : U (Nat → F Nat) = fix h. λn. case n { Zero ⇒ return Zero ;
/// Succ ⇒ λp. (force applyAt) h a }` at position 2, `a` what `handed` builds
/// under `p` 0, `n` 1, `h` 2.
///
/// # Specification
/// trivial.
fn helped(
    arena: &mut CoreArena,
    handed: impl FnOnce(&mut CoreArena) -> ValueId,
) -> Declaration
{
    let nat = nat(arena);
    let declared = function_of(arena, nat);
    let returner = arena.comp_type_returner(nat);
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
    let on_zero = arena.computation_return(zero);
    let apply = arena.value_constant(ConstantIndex::from(1));
    let h = var(arena, DeBruijnIndex::from(2));
    let argument = handed(arena);
    let called = call(arena, apply, &[h, argument]);
    let on_successor = arena.computation_lambda(called);
    let n = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(n, returner, vec![on_zero, on_successor]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    define(ConstantIndex::from(2), declared, body)
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

#[test]
fn a_helper_at_a_stage_takes_a_recursion_s_claim()
{
    // `helped` hands its own recursion `h`, typed below the stage of `n`, and
    // the field `p` to `applyAt`: the call reads `i` off `h` at `n`'s stage,
    // so both arguments fit, and both checkers admit the recursion.
    let mut arena = CoreArena::new();
    let declarations = vec![
        declare_nat(&mut arena),
        apply_at(&mut arena, vec![StageBound::Unbounded]),
        helped(&mut arena, |arena| var(arena, DeBruijnIndex::from(0))),
    ];
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    for position in [1, 2] {
        assert!(
            matches!(verdicts[position], Verdict::Checked { .. }),
            "{position}: {:?}",
            verdicts[position]
        );
        assert!(
            matches!(outcomes[position], Outcome::Defined { .. }),
            "{position}: {:?}",
            outcomes[position]
        );
    }

    // The control: the same helper quantified over nothing reads its stages
    // as written, which this module never minted, and is refused.
    let mut arena = CoreArena::new();
    let declarations = vec![
        declare_nat(&mut arena),
        apply_at(&mut arena, vec![]),
        helped(&mut arena, |arena| var(arena, DeBruijnIndex::from(0))),
    ];
    let (verdicts, _) = judge(&mut arena, &declarations);
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

#[test]
fn a_call_handing_the_scrutinee_is_refused()
{
    // `applyAt h n`: `i` is read off `h` at the stage of `n`, and `n` itself
    // is not below it.
    let mut arena = CoreArena::new();
    let declarations = vec![
        declare_nat(&mut arena),
        apply_at(&mut arena, vec![StageBound::Unbounded]),
        helped(&mut arena, |arena| var(arena, DeBruijnIndex::from(1))),
    ];
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[2],
            Verdict::Refused(CheckRefusal::StageNotBelow { .. })
        ),
        "{:?}",
        verdicts[2]
    );
}

/// `sameAt @[i : Size] (f : U (Nat[i] → F Nat), x : Nat[i]) : F Nat = (force
/// f) x` at position 1.
///
/// # Specification
/// trivial.
fn same_at(arena: &mut CoreArena) -> Declaration
{
    let nat = nat(arena);
    let at_i = arena.value_type_staged(nat, Stage::At(StageId::from(0_usize)));
    let function = function_of(arena, at_i);
    let returner = arena.comp_type_returner(nat);
    let inner = arena.comp_type_arrow(at_i, returner);
    let outer = arena.comp_type_arrow(function, inner);
    let declared = arena.value_type_thunk(outer);
    let f = var(arena, DeBruijnIndex::from(1));
    let x = var(arena, DeBruijnIndex::from(0));
    let applied = call(arena, f, &[x]);
    let second = arena.computation_lambda(applied);
    let first = arena.computation_lambda(second);
    let body = arena.value_thunk(first);
    define(ConstantIndex::from(1), declared, body).staged(vec![StageBound::Unbounded])
}

#[test]
fn arguments_at_apart_stages_disagree_by_name_1227()
{
    // #1227: `sameAt h p` reads `i` from above under `h`'s domain, one below
    // `n`'s stage, and from below at `p`'s, which fits there: both checkers
    // admit it at `p`'s stage. `sameAt h n` reads it from below at `n`'s own
    // stage, where the solve stands it, and no stage there is under `h`'s
    // domain: refused by name at `h`, the reading the solution leaves unmet.
    let mut arena = CoreArena::new();
    let declarations = vec![
        declare_nat(&mut arena),
        same_at(&mut arena),
        helped(&mut arena, |arena| var(arena, DeBruijnIndex::from(0))),
    ];
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    for position in [1, 2] {
        assert!(
            matches!(verdicts[position], Verdict::Checked { .. }),
            "{position}: {:?}",
            verdicts[position]
        );
        assert!(
            matches!(outcomes[position], Outcome::Defined { .. }),
            "{position}: {:?}",
            outcomes[position]
        );
    }

    let mut arena = CoreArena::new();
    let declarations = vec![
        declare_nat(&mut arena),
        same_at(&mut arena),
        helped(&mut arena, |arena| var(arena, DeBruijnIndex::from(1))),
    ];
    let (verdicts, _) = judge(&mut arena, &declarations);
    assert!(
        matches!(
            verdicts[2],
            Verdict::Refused(CheckRefusal::StagesDisagree { at, binder, .. })
                if binder == StageBinder::from(0_usize)
                    && arena.value(at) == Some(&gandr_core_term::Value::Variable {
                        zone: Zone::Intuitionistic,
                        index: DeBruijnIndex::from(2),
                    })
        ),
        "{:?}",
        verdicts[2]
    );
}

#[test]
fn a_call_at_no_stage_reads_its_result_plain()
{
    // `user n = (force applyAt) identity n` with `identity` and `n` at no
    // stage: `i` stands at none, `applyAt` reads plain, and both checkers
    // admit the call.
    let mut arena = CoreArena::new();
    let nat = nat(&mut arena);
    let declared = function_of(&mut arena, nat);
    let returned = var(&mut arena, DeBruijnIndex::from(0));
    let identity_body = arena.computation_return(returned);
    let identity_lambda = arena.computation_lambda(identity_body);
    let identity = arena.value_thunk(identity_lambda);
    let apply = arena.value_constant(ConstantIndex::from(1));
    let handed = arena.value_constant(ConstantIndex::from(2));
    let n = var(&mut arena, DeBruijnIndex::from(0));
    let called = call(&mut arena, apply, &[handed, n]);
    let user_lambda = arena.computation_lambda(called);
    let user = arena.value_thunk(user_lambda);
    let declarations = vec![
        declare_nat(&mut arena),
        apply_at(&mut arena, vec![StageBound::Unbounded]),
        define(ConstantIndex::from(2), declared, identity),
        define(ConstantIndex::from(3), declared, user),
    ];
    let (verdicts, outcomes) = judge(&mut arena, &declarations);
    assert!(
        matches!(verdicts[3], Verdict::Checked { .. }),
        "{:?}",
        verdicts[3]
    );
    assert!(
        matches!(outcomes[3], Outcome::Defined { .. }),
        "{:?}",
        outcomes[3]
    );
}

/// `boundedAt @[j : Size, k : Size, k < j] (x : Nat[j], y : Nat[k]) : F
/// Nat[<j] = return y` at position 1.
///
/// # Specification
/// trivial.
fn bounded_at(arena: &mut CoreArena) -> Declaration
{
    let nat = nat(arena);
    let at_j = arena.value_type_staged(nat, Stage::At(StageId::from(0_usize)));
    let at_k = arena.value_type_staged(nat, Stage::At(StageId::from(1_usize)));
    let below_j = arena.value_type_staged(nat, Stage::Below {
        anchor: StageId::from(0_usize),
        depth: StageDepth::from(core::num::NonZeroU32::MIN),
    });
    let returner = arena.comp_type_returner(below_j);
    let inner = arena.comp_type_arrow(at_k, returner);
    let outer = arena.comp_type_arrow(at_j, inner);
    let declared = arena.value_type_thunk(outer);
    let y = var(arena, DeBruijnIndex::from(0));
    let returned = arena.computation_return(y);
    let second = arena.computation_lambda(returned);
    let first = arena.computation_lambda(second);
    let body = arena.value_thunk(first);
    define(ConstantIndex::from(1), declared, body).staged(vec![
        StageBound::Unbounded,
        StageBound::Below(StageBinder::from(0_usize)),
    ])
}

/// `looping : U (Nat → F Nat) = fix h. λn. case n { Zero ⇒ return Zero ; Succ
/// ⇒ λp. bind ((force boundedAt) p a) λq. (force h) q }` at position 2, `a`
/// the variable `handed` under `p` 0, `n` 1, `h` 2.
///
/// # Specification
/// trivial.
fn looping(
    arena: &mut CoreArena,
    handed: DeBruijnIndex,
) -> Declaration
{
    let nat = nat(arena);
    let declared = function_of(arena, nat);
    let returner = arena.comp_type_returner(nat);
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
    let on_zero = arena.computation_return(zero);
    let bounded = arena.value_constant(ConstantIndex::from(1));
    let p = var(arena, DeBruijnIndex::from(0));
    let handed = var(arena, handed);
    let called = call(arena, bounded, &[p, handed]);
    // Under λq: `q` 0, `h` 3.
    let own = var(arena, DeBruijnIndex::from(3));
    let q = var(arena, DeBruijnIndex::from(0));
    let recursed = call(arena, own, &[q]);
    let bound = arena.computation_bind(called, recursed);
    let on_successor = arena.computation_lambda(bound);
    let n = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(n, returner, vec![on_zero, on_successor]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    define(ConstantIndex::from(2), declared, body)
}

#[test]
fn a_bounded_binder_read_above_its_bound_is_refused_1241()
{
    // `boundedAt p n` reads `j` at `p`'s stage and `k` at `n`'s, which is not
    // below it; `boundedAt p p` reads `k` at `j`'s own stage. Either would
    // type its result below the recursion's stage and `h` would take it, so
    // both are refused at the argument `k` is read off.
    for (handed, read_off) in [(1_u32, 1_u32), (0, 0)] {
        let mut arena = CoreArena::new();
        let declarations = vec![
            declare_nat(&mut arena),
            bounded_at(&mut arena),
            looping(&mut arena, DeBruijnIndex::from(handed)),
        ];
        let (verdicts, _) = judge(&mut arena, &declarations);
        assert!(
            matches!(verdicts[1], Verdict::Checked { .. }),
            "{:?}",
            verdicts[1]
        );
        assert!(
            matches!(
                verdicts[2],
                Verdict::Refused(CheckRefusal::StageNotBelow { at, .. })
                    if arena.value(at) == Some(&gandr_core_term::Value::Variable {
                        zone: Zone::Intuitionistic,
                        index: DeBruijnIndex::from(read_off),
                    })
            ),
            "handing {handed}: {:?}",
            verdicts[2]
        );
    }
}

#[test]
fn a_bound_naming_a_later_binder_is_refused()
{
    // `@[i < i]`: a bound names a binder stated before it.
    let mut arena = CoreArena::new();
    let declarations = vec![
        declare_nat(&mut arena),
        apply_at(&mut arena, vec![StageBound::Below(StageBinder::from(
            0_usize,
        ))]),
    ];
    let (verdicts, _) = judge(&mut arena, &declarations);
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

#[test]
fn a_stage_on_no_data_type_is_refused()
{
    // `intAt @[i : Size] (n : Integer[i]) -> -F Nat`: the kernel's mark would
    // reach no data type, so the checker refuses the stage too.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let staged = arena.value_type_staged(integer, Stage::At(StageId::from(0_usize)));
    let declared = function_of(&mut arena, staged);
    let nat = nat(&mut arena);
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
    let returned = arena.computation_return(zero);
    let lambda = arena.computation_lambda(returned);
    let body = arena.value_thunk(lambda);
    let declarations = vec![
        declare_nat(&mut arena),
        define(ConstantIndex::from(1), declared, body).staged(vec![StageBound::Unbounded]),
    ];
    let (verdicts, _) = judge(&mut arena, &declarations);
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
