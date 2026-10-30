use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::primitive::PrimitiveType;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;

/// A law's body the module omits.
const DISCHARGED: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Discharged);

/// How a component decides two integers.
#[derive(Clone, Copy, Debug)]
enum Deciding
{
    /// `alike`, which answers `true` whatever it is given.
    Always,
    /// The prelude's `int.eq`.
    Primitive,
}

/// What stands between a law's binder and its path.
#[derive(Clone, Copy, Debug)]
enum Between
{
    /// Nothing: the path follows the binder.
    Nothing,
    /// An arrow over a second integer the path never reads.
    Unused,
}

/// The declaration at `at` with `declared` and `defined`.
///
/// # Specification
/// trivial.
fn declaration(
    at: ConstantIndex,
    declared: ValueTypeId,
    defined: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        at,
        Maybe::Present(declared),
        defined,
        OriginToken::from(usize::from(at)),
    )
}

/// `true`, the boolean the prelude's first summand codes.
///
/// # Specification
/// trivial.
fn truth(arena: &mut CoreArena) -> ValueId
{
    let unit = arena.value_unit();
    arena.value_injection(gandr_kernel_term::Summand::from(0_usize), unit)
}

/// A component deciding two integers as `deciding` says, its type and its
/// body.
///
/// # Specification
/// trivial.
fn component(
    arena: &mut CoreArena,
    deciding: Deciding,
) -> (ValueTypeId, ValueId)
{
    let boolean = PrimitiveType::Boolean.mint(arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let answer = arena.comp_type_returner(boolean);
    let second = arena.comp_type_arrow(integer, answer);
    let first = arena.comp_type_arrow(integer, second);
    let declared = arena.value_type_thunk(first);
    let defined = match deciding {
        Deciding::Always => {
            let answered = truth(arena);
            let returned = arena.computation_return(answered);
            let inner = arena.computation_lambda(returned);
            let outer = arena.computation_lambda(inner);
            arena.value_thunk(outer)
        },
        Deciding::Primitive => PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == "int.eq")
            .expect("the prelude holds `int.eq`")
            .thunk(arena),
    };
    (declared, defined)
}

/// The component at `at` applied to the variable `index` twice.
///
/// # Specification
/// trivial.
fn decided(
    arena: &mut CoreArena,
    at: ConstantIndex,
    index: DeBruijnIndex,
) -> ValueId
{
    let head = arena.value_constant(at);
    let forced = arena.computation_force(head);
    let variable = arena.value_variable(Zone::Intuitionistic, index);
    let once = arena.computation_application(forced, variable);
    let twice = arena.computation_application(once, variable);
    arena.value_returned(twice)
}

/// `refl : (a : Integer) => Path(Bool, c(a, a), true)` for the component at
/// `at`, with `between` standing between the binder and the path.
///
/// # Specification
/// trivial.
fn reflexive(
    arena: &mut CoreArena,
    at: ConstantIndex,
    between: Between,
) -> ValueTypeId
{
    let boolean = PrimitiveType::Boolean.mint(arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let left = decided(arena, at, DeBruijnIndex::from(0_u32));
    let right = truth(arena);
    let path = arena.value_type_path(boolean, left, right);
    let mut chain = arena.comp_type_returner(path);
    if matches!(between, Between::Unused) {
        chain = arena.comp_type_arrow(integer, chain);
    }
    chain = arena.comp_type_pi(integer, chain);
    arena.value_type_thunk(chain)
}

/// The verdicts `declarations` take, one module checked in a fresh context.
///
/// # Specification
/// trivial.
fn verdicts(
    arena: &mut CoreArena,
    declarations: &[Declaration],
) -> Vec<Verdict>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, declarations)
        .judged()
        .iter()
        .map(crate::module::Judged::verdict)
        .collect()
}

#[test]
fn an_omitted_law_whose_sides_convert_is_here()
{
    let mut arena = CoreArena::new();
    let (alike, alike_body) = component(&mut arena, Deciding::Always);
    let refl = reflexive(&mut arena, ConstantIndex::from(0_usize), Between::Nothing);
    let past = reflexive(&mut arena, ConstantIndex::from(0_usize), Between::Unused);
    let verdicts = verdicts(&mut arena, &[
        declaration(
            ConstantIndex::from(0_usize),
            alike,
            Maybe::Present(alike_body),
        ),
        declaration(ConstantIndex::from(1_usize), refl, DISCHARGED),
        declaration(ConstantIndex::from(2_usize), past, DISCHARGED),
    ]);
    for (at, what) in [
        (1, "the sides convert under the law's binder"),
        (2, "an arrow's binder binds in the body, below the endpoint"),
    ] {
        let Some(&Verdict::Checked { body, .. }) = verdicts.get(at)
        else {
            panic!("{what}: {:?}", verdicts.get(at));
        };
        assert!(
            matches!(arena.value(body), Some(Value::Thunk(_))),
            "{what}: the component is a thunk of the telescope's lambdas"
        );
    }
}

#[test]
fn an_omitted_law_whose_sides_part_is_undischarged()
{
    let mut arena = CoreArena::new();
    let (equal, equal_body) = component(&mut arena, Deciding::Primitive);
    let refl = reflexive(&mut arena, ConstantIndex::from(0_usize), Between::Nothing);
    let verdicts = verdicts(&mut arena, &[
        declaration(
            ConstantIndex::from(0_usize),
            equal,
            Maybe::Present(equal_body),
        ),
        declaration(ConstantIndex::from(1_usize), refl, DISCHARGED),
    ]);
    assert_eq!(
        verdicts.get(1).copied(),
        Some(Verdict::Refused(CheckRefusal::UndischargedLaw { at: refl })),
        "a primitive's equality at a variable is stuck, so `here` does not fill the law"
    );
}

#[test]
fn a_law_over_no_binder_is_here_alone()
{
    let mut arena = CoreArena::new();
    let boolean = PrimitiveType::Boolean.mint(&mut arena);
    let (left, right) = (truth(&mut arena), truth(&mut arena));
    let path = arena.value_type_path(boolean, left, right);
    let verdicts = verdicts(&mut arena, &[declaration(
        ConstantIndex::from(0_usize),
        path,
        DISCHARGED,
    )]);
    let Some(&Verdict::Checked { body, .. }) = verdicts.first()
    else {
        panic!("a closed law whose sides convert checks: {verdicts:?}");
    };
    assert!(
        matches!(arena.value(body), Some(&Value::Here(at)) if at == left),
        "the component is `here` at the left side, with no thunk around it"
    );
}
