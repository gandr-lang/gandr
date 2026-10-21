//! Definitions quantified over stages: the stage signature a definition
//! carries beside its plain declared type, its own body checked at minted
//! stages, and each call reading its binders off its arguments.

use anodized::spec;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::PlacedChild;
use gandr_kernel_term::StageBinder;
use gandr_kernel_term::StageBound;
use gandr_kernel_term::StageDepth;
use gandr_kernel_term::StageMark;
use gandr_kernel_term::StageReach;
use gandr_kernel_term::StageSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

/// Admit `Nat`: `zero`, and `succ` over the family.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the returned identifier names `Nat` at the environment's next
///   position.
/// - panics: if the strictly positive block is refused.
///
/// # Adequacy
/// - hypothesis: L3 — the data type every signature here stages.
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
fn nat(environment: &mut Environment) -> CheckedId
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let own = arena.value_type_data(position, vec![]);
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        vec![],
        vec![vec![], vec![own]],
        kind,
    );
    environment
        .add_decl(declaration)
        .expect("Nat is strictly positive")
}

/// `U (Nat → F Nat)`.
///
/// # Specification
/// trivial.
fn unary(
    arena: &mut TermArena,
    nat: ConstantIndex,
) -> ValueTypeId
{
    let nat_type = arena.value_type_data(nat, vec![]);
    let returner = arena.comp_type_returner(nat_type);
    let arrow = arena.comp_type_arrow(nat_type, returner);
    arena.value_type_thunk(arrow)
}

/// `(force head) arguments…`.
///
/// # Specification
/// trivial.
fn spine(
    arena: &mut TermArena,
    head: ValueId,
    arguments: &[ValueId],
) -> gandr_kernel_term::ComputationId
{
    let mut built = arena.computation_force(head);
    for &argument in arguments {
        built = arena.computation_application(built, argument);
    }
    built
}

/// The mark of an occurrence one stage below binder `i` at `path`.
///
/// # Specification
/// trivial.
fn below_i(path: &[PlacedChild]) -> StageMark
{
    StageMark::new(
        path.to_vec(),
        StageBinder::from(0_usize),
        StageReach::Below(StageDepth::from(core::num::NonZeroU32::MIN)),
    )
}

/// `applyAt @[i : Size] (f : U (Nat[<i] → F Nat), x : Nat[<i]) : F Nat =
/// (force f) x`: the plain type `U (U (Nat → F Nat) → Nat → F Nat)`, the
/// stage signature `signature` beside it, admitted by the kernel or refused.
///
/// # Specification
/// trivial.
fn apply_at(
    environment: &mut Environment,
    nat: ConstantIndex,
    signature: StageSignature,
) -> Result<CheckedId, KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let function = unary(arena, nat);
    let returner = arena.comp_type_returner(nat_type);
    let inner = arena.comp_type_arrow(nat_type, returner);
    let outer = arena.comp_type_arrow(function, inner);
    let declared = arena.value_type_thunk(outer);
    // Under λf λx: `x` 0, `f` 1.
    let f = arena.value_variable(DeBruijnIndex::from(1));
    let x = arena.value_variable(DeBruijnIndex::from(0));
    let applied = spine(arena, f, &[x]);
    let second = arena.computation_lambda(applied);
    let first = arena.computation_lambda(second);
    let value = arena.value_thunk(first);
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, value)
        .staged(signature);
    environment.add_decl(declaration)
}

/// `applyAt`'s signature: `i` unbounded, `f`'s domain and `x` one stage
/// below it.
///
/// # Specification
/// trivial.
fn quantified() -> StageSignature
{
    StageSignature::new(vec![StageBound::Unbounded], vec![
        below_i(&[0_usize, 0, 0, 0].map(PlacedChild::from)),
        below_i(&[0_usize, 1, 0].map(PlacedChild::from)),
    ])
}

/// `helped : U (Nat → F Nat) = fix h. λn. case n { zero ↦ return zero ;
/// succ ↦ λp. (force applyAt) h v }`, `v` the variable `handed` under `p` 0,
/// `n` 1, `h` 2, admitted by the kernel or refused.
///
/// # Specification
/// trivial.
fn helped(
    environment: &mut Environment,
    (nat, apply): (ConstantIndex, ConstantIndex),
    handed: DeBruijnIndex,
) -> Result<CheckedId, KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let returner = arena.comp_type_returner(nat_type);
    let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
    let on_zero = arena.computation_return(zero);
    let head = arena.value_constant(apply);
    let claim = arena.value_variable(DeBruijnIndex::from(2));
    let handed = arena.value_variable(handed);
    let called = spine(arena, head, &[claim, handed]);
    let on_successor = arena.computation_lambda(called);
    let scrutinee = arena.value_variable(DeBruijnIndex::from(0));
    let case = arena.computation_data_case(scrutinee, returner, vec![on_zero, on_successor]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let declared = unary(arena, nat);
    let value = arena.value_thunk(fixpoint);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    environment.add_decl(declaration)
}

/// A recursion hands its own claim and its field to a helper quantified over
/// a stage: the call reads the stage off the claim, and both arguments fit.
/// The same helper quantified over nothing takes neither.
#[test]
fn a_helper_at_a_stage_takes_a_recursion_s_claim()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let apply = apply_at(&mut environment, nat, quantified())
        .expect("the helper checks at its minted stage")
        .position();
    let admitted = helped(&mut environment, (nat, apply), DeBruijnIndex::from(0));
    assert!(admitted.is_ok(), "{admitted:?}");

    let mut plain = Environment::new();
    let nat = self::nat(&mut plain).position();
    let apply = apply_at(&mut plain, nat, StageSignature::default())
        .expect("the plain helper checks")
        .position();
    let refused = helped(&mut plain, (nat, apply), DeBruijnIndex::from(0));
    assert!(
        matches!(refused, Err(KernelError::StageNotBelow { .. })),
        "{refused:?}"
    );
}

/// The scrutinee itself is not below the stage the call reads off the claim.
#[test]
fn a_call_handing_the_scrutinee_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let apply = apply_at(&mut environment, nat, quantified())
        .expect("the helper checks at its minted stage")
        .position();
    let refused = helped(&mut environment, (nat, apply), DeBruijnIndex::from(1));
    assert!(
        matches!(refused, Err(KernelError::StageNotBelow { .. })),
        "{refused:?}"
    );
}

/// A mark whose path ends at the helper's arrow, no data type, is refused at
/// admission, and so is a bound naming a binder not stated before it.
#[test]
fn a_mark_reaching_no_data_type_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let refused = apply_at(
        &mut environment,
        nat,
        StageSignature::new(vec![StageBound::Unbounded], vec![below_i(&[
            PlacedChild::from(0_usize),
        ])]),
    );
    assert!(
        matches!(refused, Err(KernelError::StageUnplaced)),
        "{refused:?}"
    );
    let refused = apply_at(
        &mut environment,
        nat,
        StageSignature::new(vec![StageBound::Below(StageBinder::from(0_usize))], vec![
            below_i(&[0_usize, 1, 0].map(PlacedChild::from)),
        ]),
    );
    assert!(
        matches!(refused, Err(KernelError::StageUnplaced)),
        "{refused:?}"
    );
}

/// A call on values at no stage instantiates nothing: the helper reads plain.
#[test]
fn a_call_at_no_stage_reads_its_result_plain()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let apply = apply_at(&mut environment, nat, quantified())
        .expect("the helper checks at its minted stage")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = unary(arena, nat);
    let returned = arena.value_variable(DeBruijnIndex::from(0));
    let body = arena.computation_return(returned);
    let lambda = arena.computation_lambda(body);
    let value = arena.value_thunk(lambda);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    let identity = environment
        .add_decl(declaration)
        .expect("the identity checks")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = unary(arena, nat);
    let head = arena.value_constant(apply);
    let handed = arena.value_constant(identity);
    let n = arena.value_variable(DeBruijnIndex::from(0));
    let called = spine(arena, head, &[handed, n]);
    let lambda = arena.computation_lambda(called);
    let value = arena.value_thunk(lambda);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    let admitted = environment.add_decl(declaration);
    assert!(admitted.is_ok(), "{admitted:?}");
}

/// `boundedAt @[j : Size, k : Size, k < j] (x : Nat[j], y : Nat[k]) : F
/// Nat[<j] = return y`: the plain type `U (Nat → Nat → F Nat)` with `x` at
/// `j`, `y` at `k` and the result one below `j`.
///
/// # Specification
/// trivial.
fn bounded_at(
    environment: &mut Environment,
    nat: ConstantIndex,
) -> Result<CheckedId, KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let returner = arena.comp_type_returner(nat_type);
    let inner = arena.comp_type_arrow(nat_type, returner);
    let outer = arena.comp_type_arrow(nat_type, inner);
    let declared = arena.value_type_thunk(outer);
    // Under λx λy: `y` 0.
    let y = arena.value_variable(DeBruijnIndex::from(0));
    let returned = arena.computation_return(y);
    let second = arena.computation_lambda(returned);
    let first = arena.computation_lambda(second);
    let value = arena.value_thunk(first);
    let at = |binder: usize, path: &[usize]| {
        StageMark::new(
            path.iter().copied().map(PlacedChild::from).collect(),
            StageBinder::from(binder),
            StageReach::At,
        )
    };
    let signature = StageSignature::new(
        vec![
            StageBound::Unbounded,
            StageBound::Below(StageBinder::from(0_usize)),
        ],
        vec![
            at(0, &[0, 0]),
            at(1, &[0, 1, 0]),
            StageMark::new(
                [0_usize, 1, 1, 0].map(PlacedChild::from).to_vec(),
                StageBinder::from(0_usize),
                StageReach::Below(StageDepth::from(core::num::NonZeroU32::MIN)),
            ),
        ],
    );
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, value)
        .staged(signature);
    environment.add_decl(declaration)
}

/// #1241: `looping : U (Nat → F Nat) = fix h. λn. case n { zero ↦ return
/// zero ; succ ↦ λp. bind ((force boundedAt) p n) λq. (force h) q }`. The
/// call reads `j` at `p`'s stage and `k` at `n`'s, which is not below it: the
/// result would type `n` below the recursion's stage and `h` would take it.
/// Handing `p` twice reads `k` at `j`'s own stage, refused the same way.
#[test]
fn a_bounded_binder_read_above_its_bound_is_refused_1241()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let bounded = bounded_at(&mut environment, nat)
        .expect("the helper checks at its minted stages")
        .position();
    for second in [1_u32, 0] {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let on_zero = arena.computation_return(zero);
        // Under λp: `p` 0, `n` 1, `h` 2.
        let head = arena.value_constant(bounded);
        let p = arena.value_variable(DeBruijnIndex::from(0));
        let handed = arena.value_variable(DeBruijnIndex::from(second));
        let called = spine(arena, head, &[p, handed]);
        // Under λq: `q` 0, `h` 3.
        let own = arena.value_variable(DeBruijnIndex::from(3));
        let q = arena.value_variable(DeBruijnIndex::from(0));
        let recursed = spine(arena, own, &[q]);
        let bound = arena.computation_bind(called, recursed);
        let on_successor = arena.computation_lambda(bound);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(scrutinee, returner, vec![on_zero, on_successor]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        let declared = unary(arena, nat);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        let refused = environment.add_decl(declaration);
        assert!(
            matches!(refused, Err(KernelError::StageNotBelow { .. })),
            "handing {second}: {refused:?}"
        );
    }
}
