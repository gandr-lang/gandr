use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::fixture::Booleans;
use crate::fixture::booleans;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;

/// A declaration position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// The declaration at `position`, its origin the position itself.
///
/// # Specification
/// trivial.
fn declaration(
    At(position): At,
    declared: ValueTypeId,
    defined: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        Maybe::Present(declared),
        defined,
        OriginToken::from(position),
    )
}

/// The three boolean functions at positions zero to two, then `extra`.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    functions: &Booleans,
    extra: &[Declaration],
) -> ModuleReport
{
    let mut module = Vec::from([
        declaration(At(0), functions.function, Maybe::Present(functions.not)),
        declaration(At(1), functions.function, Maybe::Present(functions.not_not)),
        declaration(At(2), functions.function, Maybe::Present(functions.same)),
    ]);
    module.extend_from_slice(extra);
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, &module)
}

/// `Path(Type, ⌜code⌝, ⌜code⌝)`.
///
/// # Specification
/// trivial.
fn identity(
    arena: &mut CoreArena,
    code: ValueTypeId,
) -> ValueTypeId
{
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let quoted = arena.value_quote(code);
    arena.value_type_path(universe, quoted, quoted)
}

/// `equiv(c_forward, c_backward) : Path(Type, ⌜Bool⌝, ⌜Bool⌝)` at
/// `position`, with its `equiv` node.
///
/// # Specification
/// trivial.
fn equivalence(
    arena: &mut CoreArena,
    functions: &Booleans,
    position: At,
    (At(forward), At(backward)): (At, At),
) -> (Declaration, ValueId)
{
    let forward = arena.value_constant(ConstantIndex::from(forward));
    let backward = arena.value_constant(ConstantIndex::from(backward));
    let path = identity(arena, functions.ty);
    let equiv = arena.value_equiv(forward, backward);
    (declaration(position, path, Maybe::Present(equiv)), equiv)
}

#[test]
fn an_involution_is_its_own_inverse_by_computation()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let (negation, at) = equivalence(&mut arena, &functions, At(3), (At(0), At(0)));
    let (doubled, twice) = equivalence(&mut arena, &functions, At(4), (At(1), At(2)));
    let report = judged(&mut arena, &functions, &[negation, doubled]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "negation is its own inverse, and not ∘ not is the identity's: {report:?}"
    );
    assert_eq!(report.equivalences().len(), 2);
    let Some(decided) = report.equivalences().get(&at)
    else {
        panic!("the decision is recorded at the equiv node");
    };
    let Some(&ValueType::PathUniverse(source, target)) = arena.value_type(decided.classifier())
    else {
        panic!("the classifier is the native universe path");
    };
    assert!(
        [source, target]
            .iter()
            .all(|&code| arena.value(code) == Some(&Value::Quote(functions.ty))),
        "both endpoints are the quote of Bool"
    );
    let unfolded = |dialogue: &Vec<ConversionDecision<()>>| {
        dialogue
            .iter()
            .filter(|decision| matches!(decision, ConversionDecision::Unfold { .. }))
            .count()
    };
    let evidence = decided.evidence();
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
            .all(|dialogue| unfolded(dialogue) == 2),
        "each round trip unfolds negation once on the way there and once back"
    );
    let Some(doubled) = report.equivalences().get(&twice)
    else {
        panic!("the second decision is recorded");
    };
    let counts: Vec<usize> = doubled
        .evidence()
        .source
        .iter()
        .chain(&doubled.evidence().target)
        .map(unfolded)
        .collect();
    assert_eq!(
        counts,
        [4, 4, 4, 4],
        "each round trip unfolds not ∘ not, negation twice inside it, and the identity"
    );
}

#[test]
fn what_the_rule_cannot_show_it_refuses_by_name()
{
    // Negation and the identity are not inverse.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let (apart, at) = equivalence(&mut arena, &functions, At(3), (At(0), At(2)));
    let report = judged(&mut arena, &functions, &[apart]);
    assert_eq!(
        report.judged().get(3).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::RoundTripDistinct { at }))
    );
    assert!(
        report.equivalences().is_empty(),
        "a refused equiv records nothing"
    );

    // A list code is the uncertified stratum, even for the identity.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let list = arena.value_type_list(functions.ty);
    let returns = arena.comp_type_returner(list);
    let arrow = arena.comp_type_arrow(list, returns);
    let translator = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let same_list = arena.value_thunk(lambda);
    let constant = arena.value_constant(ConstantIndex::from(3_usize));
    let path = identity(&mut arena, list);
    let equiv = arena.value_equiv(constant, constant);
    let report = judged(&mut arena, &functions, &[
        declaration(At(3), translator, Maybe::Present(same_list)),
        declaration(At(4), path, Maybe::Present(equiv)),
    ]);
    assert!(
        matches!(
            report.judged().get(4).map(Judged::verdict),
            Some(Verdict::Refused(CheckRefusal::UncertifiedStratum { at, code }))
                if at == equiv && arena.value_type(code) == Some(&ValueType::List(functions.ty))
        ),
        "{report:?}"
    );

    // A forward translator that is no function names no codes.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let unit = arena.value_unit();
    let equiv = arena.value_equiv(unit, unit);
    let path = identity(&mut arena, functions.ty);
    let report = judged(&mut arena, &functions, &[declaration(
        At(3),
        path,
        Maybe::Present(equiv),
    )]);
    assert!(
        matches!(
            report.judged().get(3).map(Judged::verdict),
            Some(Verdict::Refused(CheckRefusal::EquivUnsupported { at, .. })) if at == equiv
        ),
        "{report:?}"
    );

    // Open translators: the rule decides closed ones only.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let path = identity(&mut arena, functions.ty);
    let returns_path = arena.comp_type_returner(path);
    let pi = arena.comp_type_pi(functions.function, returns_path);
    let declared = arena.value_type_thunk(pi);
    let equiv = arena.value_equiv(bound, bound);
    let returned = arena.computation_return(equiv);
    let lambda = arena.computation_lambda(returned);
    let open = arena.value_thunk(lambda);
    let report = judged(&mut arena, &functions, &[declaration(
        At(3),
        declared,
        Maybe::Present(open),
    )]);
    assert!(
        matches!(
            report.judged().get(3).map(Judged::verdict),
            Some(Verdict::Refused(CheckRefusal::EquivUnsupported { at, .. })) if at == equiv
        ),
        "{report:?}"
    );
}
