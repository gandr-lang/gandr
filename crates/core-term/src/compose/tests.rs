use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ShapeSize;

use super::CellCount;
use super::Composite;
use super::Pasting;
use crate::CertificateEquality;
use crate::CoreArena;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::syntax::Value;
use crate::syntax::Zone;
use crate::syntax::equal_certificate_syntax;
use crate::ua::Stratum;

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// `compose[5, 7](chain(cells), …)`.
///
/// # Specification
/// trivial.
fn chain(cells: CellCount) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(5_usize),
            bound: ShapeSize::from(7_usize),
        },
        pasting: Pasting::Chain { cells },
    }
}

/// The realisation a composite holds.
///
/// # Specification
/// trivial.
fn realised(
    arena: &CoreArena,
    composite: ValueId,
) -> ComputationId
{
    match arena.value(composite) {
        Some(&Value::Compose { realised, .. }) => realised,
        other => panic!("a composite, not {other:?}"),
    }
}

/// How two built terms compare as syntax.
///
/// # Specification
/// trivial.
fn compared(
    arena: &CoreArena,
    left: ComputationId,
    right: ComputationId,
) -> CertificateEquality
{
    let mut probe = arena.clone();
    let left = probe.value_thunk(left);
    let right = probe.value_thunk(right);
    equal_certificate_syntax(&probe, left, right)
}

#[test]
fn three_cells_realise_as_the_left_nested_fold()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let start = variable(&mut arena, 0_u32.into());
    let [first, second, third] = [1_u32, 2, 3].map(|index| variable(&mut arena, index.into()));
    let built = super::compose(
        &mut arena,
        chain(CellCount::from(3_usize)),
        (integer, start),
        &[first, second, third],
    );

    let inner = crate::identity::then(&mut arena, integer, start, first, second);
    let inner = arena.value_returned(inner);
    let left = crate::identity::then(&mut arena, integer, start, inner, third);
    assert_eq!(
        compared(&arena, realised(&arena, built), left),
        CertificateEquality::Equal,
        "the composite of three cells moves the first two's composite along the third"
    );

    let outer = crate::identity::then(&mut arena, integer, start, second, third);
    let outer = arena.value_returned(outer);
    let right = crate::identity::then(&mut arena, integer, start, first, outer);
    assert_eq!(
        compared(&arena, realised(&arena, built), right),
        CertificateEquality::Different,
        "the right-nested bracketing is another term"
    );

    let single = super::compose(
        &mut arena,
        chain(CellCount::from(1_usize)),
        (integer, start),
        &[first],
    );
    let returned = arena.computation_return(first);
    assert_eq!(
        compared(&arena, realised(&arena, single), returned),
        CertificateEquality::Equal,
        "one cell realises as itself returned"
    );
}
