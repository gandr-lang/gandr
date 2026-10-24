use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::OccurrenceSite;
use quenchant_shape::shape::Maybe;

use super::Statement;
use super::law;
use crate::Binders;
use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::DataSignature;
use crate::Sort;
use crate::Value;
use crate::ValueId;
use crate::ValueTypeId;
use crate::generic::Derived;
use crate::generic::Uncovered;
use crate::primitive::PrimitiveType;

/// `Type[+, 0]`, every test declaration's universe.
///
/// # Specification
/// trivial.
fn kind(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// `statement` of the equality at `position`, the host answering a constant
/// for each base type in `hosted`.
///
/// # Specification
/// trivial.
fn derived(
    arena: &mut CoreArena,
    position: ConstantIndex,
    signatures: &BTreeMap<ConstantIndex, DataSignature>,
    statement: Statement,
    hosted: &[BaseType],
) -> Result<Derived, Uncovered>
{
    let constants: Vec<(BaseType, ValueId)> = hosted
        .iter()
        .zip(100_usize ..)
        .map(|(&base, at)| (base, arena.value_constant(ConstantIndex::from(at))))
        .collect();
    law(
        arena,
        position,
        &|at| signatures.get(&at),
        statement,
        &|base, _statement| {
            constants
                .iter()
                .find(|&&(hosted, _)| hosted == base)
                .map(|&(_, constant)| constant)
        },
    )
}

/// More binders than any derivation opens: a term strengthening past them
/// names no binder at all.
///
/// # Specification
/// trivial.
fn far() -> Binders
{
    Binders::from(1_000_u32)
}

/// The branches of the nominal case `value` suspends past `count` lambdas.
///
/// # Specification
/// trivial.
fn opened(
    arena: &CoreArena,
    value: ValueId,
    count: Binders,
) -> Vec<ComputationId>
{
    let mut focus: ComputationId = match arena.value(value) {
        Some(&Value::Thunk(body)) => body,
        other => panic!("a thunk, not {other:?}"),
    };
    for _lambda in 0 .. u32::from(count) {
        focus = match arena.computation(focus) {
            Some(&Computation::Lambda(body)) => body,
            other => panic!("a lambda, not {other:?}"),
        };
    }
    match arena.computation(focus) {
        Some(&Computation::DataCase { ref branches, .. }) => branches.clone(),
        other => panic!("a nominal case, not {other:?}"),
    }
}

#[test]
fn a_point_and_a_line_derive_closed_laws_2302()
{
    // Point(Integer, Integer), Line(Point, Point, ()) and Shape = Dot |
    // Seg(Point, String): each law is a closed thunk of its statement, opening
    // one variable for reflexivity and two for symmetry onto a case with a
    // branch per constructor, and records its declaration's cases and those
    // of the declarations it writes in place — symmetry one inner case per
    // constructor besides the outer.
    let mut arena = CoreArena::new();
    let kind = kind(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let unit = arena.value_type_product(&[]);
    let [point_at, line_at, shape_at] = [0_usize, 1, 2].map(ConstantIndex::from);
    let point = arena.value_type_data(point_at, vec![]);
    let signatures = BTreeMap::from([
        (
            point_at,
            DataSignature::new(vec![], vec![vec![integer, integer]], kind),
        ),
        (
            line_at,
            DataSignature::new(vec![], vec![vec![point, point, unit]], kind),
        ),
        (
            shape_at,
            DataSignature::new(vec![], vec![vec![], vec![point, text]], kind),
        ),
    ]);
    let hosted = [BaseType::Integer, BaseType::String];
    // (declaration, statement, lambdas, constructors, cases)
    let [one, two] = [Binders::ONE, Binders::from(2_u32)];
    let expected = [
        (point_at, Statement::Reflexive, one, 1, 1),
        (point_at, Statement::Symmetric, two, 1, 2),
        (line_at, Statement::Reflexive, one, 1, 2),
        (line_at, Statement::Symmetric, two, 1, 4),
        (shape_at, Statement::Reflexive, one, 2, 2),
        (shape_at, Statement::Symmetric, two, 2, 5),
    ];
    for (position, statement, lambdas, constructors, cases) in expected {
        let proved = derived(&mut arena, position, &signatures, statement, &hosted)
            .unwrap_or_else(|fault| panic!("{position:?} {statement:?}: {fault:?}"));
        assert!(
            matches!(
                crate::strengthen_value_type(&mut arena, proved.declared(), far()),
                Maybe::Present(_)
            ),
            "{position:?} {statement:?}: the statement is closed"
        );
        assert!(
            matches!(
                crate::strengthen_value(&mut arena, proved.body(), far()),
                Maybe::Present(_)
            ),
            "{position:?} {statement:?}: the proof is closed"
        );
        assert_eq!(
            opened(&arena, proved.body(), lambdas).len(),
            constructors,
            "{position:?} {statement:?}: a branch per constructor"
        );
        // Past the equalities' own, which the proof writes in place.
        let equalities = crate::generic::equality(&mut arena, position, &|at| signatures.get(&at))
            .expect("the equality derives")
            .cases()
            .len();
        assert_eq!(
            proved.cases().len().checked_sub(equalities),
            Some(cases),
            "{position:?} {statement:?}: the proof's cases recorded"
        );
        assert!(
            proved.cases().iter().any(|&(_, at)| at == position),
            "{position:?} {statement:?}: its own case among them"
        );
    }
}

#[test]
fn an_uncovered_field_refuses_its_law_at_its_site_2302()
{
    // A flag is a sum, whose proof cases under a motive (#2374); a recursion
    // needs induction; an integer whose law the host does not state is
    // uncovered; a declaration reached through a field refuses at its own
    // site. Both laws refuse alike.
    let mut arena = CoreArena::new();
    let site = |tag: usize, field: usize| OccurrenceSite::Field {
        tag: ConstructorTag::from(tag),
        field: FieldPosition::from(field),
    };
    let kind = kind(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let boolean = PrimitiveType::Boolean.mint(&mut arena);
    let [flagged_at, nat_at, point_at, line_at] = [0_usize, 1, 2, 3].map(ConstantIndex::from);
    let nat = arena.value_type_data(nat_at, vec![]);
    let flagged = arena.value_type_data(flagged_at, vec![]);
    let signatures = BTreeMap::from([
        (
            flagged_at,
            DataSignature::new(vec![], vec![vec![integer, boolean]], kind),
        ),
        (
            nat_at,
            DataSignature::new(vec![], vec![vec![], vec![nat]], kind),
        ),
        (
            point_at,
            DataSignature::new(vec![], vec![vec![integer, integer]], kind),
        ),
        (
            line_at,
            DataSignature::new(vec![], vec![vec![integer, flagged]], kind),
        ),
    ]);
    let cases = [
        (
            "a flag",
            flagged_at,
            &[BaseType::Integer][..],
            Uncovered::DependentCase(flagged_at, site(0, 1)),
        ),
        (
            "a recursion",
            nat_at,
            &[BaseType::Integer][..],
            Uncovered::Inductive(nat_at, site(1, 0)),
        ),
        (
            "an integer the host states nothing of",
            point_at,
            &[][..],
            Uncovered::Field(point_at, site(0, 0)),
        ),
        (
            "a flag a field reaches",
            line_at,
            &[BaseType::Integer][..],
            Uncovered::DependentCase(flagged_at, site(0, 1)),
        ),
    ];
    for (name, position, hosted, fault) in cases {
        for statement in [Statement::Reflexive, Statement::Symmetric] {
            assert_eq!(
                derived(&mut arena, position, &signatures, statement, hosted).err(),
                Some(fault),
                "{name} {statement:?}"
            );
        }
    }
}
