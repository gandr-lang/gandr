use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::bridge::Outcome;
use crate::bridge::Readmission;
use crate::bridge::readmit;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::fixture::booleans;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;

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
    defined: ValueId,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        Maybe::Present(declared),
        Maybe::Present(defined),
        OriginToken::from(position),
    )
}

/// `module` checked, and its acceptances offered to the kernel.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> (ModuleReport, Readmission)
{
    let report = {
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        check_module(&mut context, module)
    };
    let readmission = readmit(arena, &report);
    (report, readmission)
}

/// `Path(Type, ⌜source⌝, ⌜target⌝)`.
///
/// # Specification
/// trivial.
fn identity(
    arena: &mut CoreArena,
    (source, target): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let source = arena.value_quote(source);
    let target = arena.value_quote(target);
    arena.value_type_path(universe, source, target)
}

/// `Flow(Type, ⌜source⌝, ⌜target⌝)`.
///
/// # Specification
/// trivial.
fn directed(
    arena: &mut CoreArena,
    (source, target): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let source = arena.value_quote(source);
    let target = arena.value_quote(target);
    arena.value_type_flow(universe, source, target)
}

/// The refusal of the declaration at `position`.
///
/// # Specification
/// trivial.
fn refusal(
    report: &ModuleReport,
    At(position): At,
) -> CheckRefusal
{
    match report.judged().get(position).map(Judged::verdict) {
        Some(Verdict::Refused(refusal)) => refusal,
        other => panic!("the declaration at {position} is refused: {other:?}"),
    }
}

#[test]
fn a_product_of_written_paths_elaborates_to_the_native_product()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let unit = arena.value_type_unit();
    let negation = arena.value_constant(ConstantIndex::from(0_usize));
    let flipped = arena.value_constant(ConstantIndex::from(1_usize));
    // def flipped : Path(Type, Bool, Bool) = equiv(not, not) ;
    let equiv = arena.value_equiv(negation, negation);
    let flipping = identity(&mut arena, (functions.ty, functions.ty));
    // def paired : Path(Type, #{Unit, Bool}, #{Unit, Bool}) =
    //   pathProduct(here(Unit), equiv(not, not)) ;
    let unit_code = arena.value_quote(unit);
    let here = arena.value_here(unit_code);
    let written = arena.value_equiv(negation, negation);
    let paired = arena.value_path_product(here, written);
    let pair = arena.value_type_product(&[unit, functions.ty]);
    let pairing = identity(&mut arena, (pair, pair));
    // def named : the same type = pathProduct(here(Unit), flipped) ;
    let named = arena.value_path_product(here, flipped);
    let module = [
        declaration(At(0), functions.function, functions.not),
        declaration(At(1), flipping, equiv),
        declaration(At(2), pairing, paired),
        declaration(At(3), pairing, named),
    ];
    let (report, readmission) = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a product of reflexivity at the unit and an equivalence of Bool checks at the identity \
         between their pairs: {report:?}"
    );
    for (position, product, component) in [(2_usize, paired, written), (3, named, equiv)] {
        let Some(&native) = report.natives().get(&product)
        else {
            panic!("the checker records the product's native path");
        };
        let Some(&Value::PathProduct(first, second)) = arena.value(native)
        else {
            panic!("the native path is the kernel's product");
        };
        assert_eq!(
            arena.value(first),
            Some(&Value::PathRefl(unit_code)),
            "here(Unit) is the native reflexivity at the unit's code"
        );
        let Some(decided) = report.equivalences().get(&component)
        else {
            panic!("the equivalence's decision is recorded at its node");
        };
        assert!(
            matches!(
                arena.value(second),
                Some(&Value::PathEquiv { path_type, forward, backward, .. })
                    if path_type == decided.classifier() && forward == negation && backward == negation
            ),
            "equiv(not, not), written or named, is the native certificate over the same \
             translators at its decision's classifier"
        );
        assert_eq!(
            report.definitions().get(&ConstantIndex::from(position)),
            Some(&native),
            "the constant the product defines unfolds to its native path"
        );
    }
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the bridge erases each product to its native path and the kernel admits it: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn a_product_of_native_paths_keeps_the_native_classifier()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let code = arena.value_quote(unit);
    let reflexivity = arena.value_path_refl(code);
    let product = arena.value_path_product(reflexivity, reflexivity);
    let pair = arena.value_type_product(&[unit, unit]);
    let pair = arena.value_quote(pair);
    let native = arena.value_type_path_universe(pair, pair);
    let (report, readmission) = judged(&mut arena, &[declaration(At(0), native, product)]);
    assert!(
        matches!(
            report.judged().first().map(Judged::verdict),
            Some(Verdict::Checked { .. })
        ),
        "the product of two native reflexivities is a native path: {report:?}"
    );
    assert!(
        report.natives().is_empty(),
        "a product of native components is already native"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "and crosses as written: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn a_product_with_a_native_and_a_written_component_reads_as_an_element()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let unit = arena.value_type_unit();
    let negation = arena.value_constant(ConstantIndex::from(0_usize));
    let unit_code = arena.value_quote(unit);
    // def mixed : Path(Type, #{Unit, Bool}, #{Unit, Bool}) =
    //   pathProduct(refl(⌜Unit⌝), equiv(not, not)) ;
    let reflexivity = arena.value_path_refl(unit_code);
    let written = arena.value_equiv(negation, negation);
    let mixed = arena.value_path_product(reflexivity, written);
    let pair = arena.value_type_product(&[unit, functions.ty]);
    let pairing = identity(&mut arena, (pair, pair));
    // def nested : Path(Type, #{#{Unit, Bool}, Unit}, …) =
    //   pathProduct(pathProduct(here(Unit), equiv(not, not)), here(Unit)) ;
    let here = arena.value_here(unit_code);
    let inner_equiv = arena.value_equiv(negation, negation);
    let inner = arena.value_path_product(here, inner_equiv);
    let outer = arena.value_path_product(inner, here);
    let nesting = arena.value_type_product(&[pair, unit]);
    let nesting = identity(&mut arena, (nesting, nesting));
    let module = [
        declaration(At(0), functions.function, functions.not),
        declaration(At(1), pairing, mixed),
        declaration(At(2), nesting, outer),
    ];
    let (report, readmission) = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "one written component makes the product an element identity: {report:?}"
    );
    let Some(&native) = report.natives().get(&mixed)
    else {
        panic!("a product with one written component records its native path");
    };
    assert!(
        matches!(arena.value(native), Some(&Value::PathProduct(first, _)) if first == reflexivity),
        "the native reflexivity is its own certificate"
    );
    let (Some(&inner_native), Some(&outer_native)) =
        (report.natives().get(&inner), report.natives().get(&outer))
    else {
        panic!("both products record their native paths");
    };
    assert!(
        matches!(arena.value(outer_native), Some(&Value::PathProduct(first, _)) if first == inner_native),
        "a product component's certificate is its recorded native"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "and the kernel admits each native path: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn what_the_product_cannot_read_it_refuses_by_name()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let unit = arena.value_type_unit();
    let negation = arena.value_constant(ConstantIndex::from(0_usize));
    let unit_code = arena.value_quote(unit);
    let here = arena.value_here(unit_code);
    let equiv = arena.value_equiv(negation, negation);
    // pathProduct(here(Unit), equiv(not, not)) declared with the components'
    // codes swapped: the product relates `() × Bool`, not `Bool × ()`.
    let swapped = arena.value_path_product(here, equiv);
    let crossed = arena.value_type_product(&[functions.ty, unit]);
    let crossed = identity(&mut arena, (crossed, crossed));
    // pathProduct(here(0), here(Unit)): an identity at Integer is no path of
    // the universe.
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let zero = arena.value_literal(crate::fixture::integer_literal());
    let at_integer = arena.value_here(zero);
    let integral = arena.value_path_product(at_integer, here);
    let pair = arena.value_type_product(&[integer, unit]);
    let integral_type = identity(&mut arena, (pair, pair));
    // λ p. return pathProduct(p, p) at U (Path(Type, Bool, Bool) →
    // F Path(Type, #{Bool, Bool}, #{Bool, Bool})): a path a parameter binds
    // names no certificate.
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let open = arena.value_path_product(parameter, parameter);
    let returned = arena.computation_return(open);
    let lambda = arena.computation_lambda(returned);
    let thunk = arena.value_thunk(lambda);
    let flipping = identity(&mut arena, (functions.ty, functions.ty));
    let both = arena.value_type_product(&[functions.ty, functions.ty]);
    let doubled = identity(&mut arena, (both, both));
    let result = arena.comp_type_returner(doubled);
    let arrow = arena.comp_type_arrow(flipping, result);
    let function = arena.value_type_thunk(arrow);
    let module = [
        declaration(At(0), functions.function, functions.not),
        declaration(At(1), crossed, swapped),
        declaration(At(2), integral_type, integral),
        declaration(At(3), function, thunk),
    ];
    let (report, _readmission) = judged(&mut arena, &module);
    assert!(
        matches!(refusal(&report, At(1)), CheckRefusal::TypeMismatch(_)),
        "a product checked at another pairing is a mismatch: {report:?}"
    );
    assert!(
        matches!(
            refusal(&report, At(2)),
            CheckRefusal::ShapeMismatch { at, wanted: ExpectedShape::PathUniverse, .. }
                if at == TermNode::Value(at_integer)
        ),
        "an identity at Integer is refused at the component: {report:?}"
    );
    assert!(
        matches!(
            refusal(&report, At(3)),
            CheckRefusal::ShapeMismatch { at, wanted: ExpectedShape::PathUniverse, .. }
                if at == TermNode::Value(parameter)
        ),
        "a parameter is refused at the component: {report:?}"
    );
    let refused: Vec<usize> = report
        .judged()
        .iter()
        .enumerate()
        .filter(|&(_, judged)| matches!(judged.verdict(), Verdict::Refused(_)))
        .map(|(position, _)| position)
        .collect();
    assert_eq!(refused, [1, 2, 3], "negation itself checks");
}

#[test]
fn a_flow_product_synthesises_the_flow_between_its_pairs()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let unit = arena.value_type_unit();
    let negation = arena.value_constant(ConstantIndex::from(0_usize));
    // def paired : Flow(Type, #{Unit, Bool}, #{Unit, Bool}) =
    //   flowProduct(stay(Unit), forward(not)) ;
    let unit_code = arena.value_quote(unit);
    let stay = arena.value_stay(unit_code);
    let forward = arena.value_forward(negation);
    let paired = arena.value_flow_product(stay, forward);
    let pair = arena.value_type_product(&[unit, functions.ty]);
    let pairing = directed(&mut arena, (pair, pair));
    // def nested : Flow(Type, #{Unit, #{Unit, Bool}}, …) =
    //   flowProduct(stay(Unit), paired) ;
    let nested = arena.value_flow_product(stay, paired);
    let deep = arena.value_type_product(&[unit, pair]);
    let deepening = directed(&mut arena, (deep, deep));
    // λ p. return flowProduct(p, stay(Unit)) at U (Flow(Type, Bool, Bool) →
    // F Flow(Type, #{Bool, Unit}, #{Bool, Unit})): a flow a parameter binds is
    // a flow, unlike a path, which must name a certificate.
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let open = arena.value_flow_product(parameter, stay);
    let returned = arena.computation_return(open);
    let lambda = arena.computation_lambda(returned);
    let thunk = arena.value_thunk(lambda);
    let flipping = directed(&mut arena, (functions.ty, functions.ty));
    let both = arena.value_type_product(&[functions.ty, unit]);
    let doubled = directed(&mut arena, (both, both));
    let result = arena.comp_type_returner(doubled);
    let arrow = arena.comp_type_arrow(flipping, result);
    let function = arena.value_type_thunk(arrow);
    let module = [
        declaration(At(0), functions.function, functions.not),
        declaration(At(1), pairing, paired),
        declaration(At(2), deepening, nested),
        declaration(At(3), function, thunk),
    ];
    let (report, readmission) = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a product of stay at the unit and a forward flow of Bool checks at the flow between \
         their pairs, nested and over a parameter: {report:?}"
    );
    assert!(
        report.natives().is_empty(),
        "a flow product is the kernel's own former and elaborates to nothing"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the bridge erases each product componentwise and the kernel admits it: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn what_the_flow_product_cannot_read_it_refuses_by_name()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let unit = arena.value_type_unit();
    let negation = arena.value_constant(ConstantIndex::from(0_usize));
    let unit_code = arena.value_quote(unit);
    let stay = arena.value_stay(unit_code);
    let forward = arena.value_forward(negation);
    // flowProduct(stay(Unit), forward(not)) declared with the components'
    // codes swapped: the product flows over `() × Bool`, not `Bool × ()`.
    let swapped = arena.value_flow_product(stay, forward);
    let crossed = arena.value_type_product(&[functions.ty, unit]);
    let crossed = directed(&mut arena, (crossed, crossed));
    // flowProduct(stay(0), stay(Unit)): a flow at Integer is no flow of the
    // universe.
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let zero = arena.value_literal(crate::fixture::integer_literal());
    let at_integer = arena.value_stay(zero);
    let integral = arena.value_flow_product(at_integer, stay);
    let pair = arena.value_type_product(&[integer, unit]);
    let integral_type = directed(&mut arena, (pair, pair));
    // flowProduct(stay(+U (Bool -> -F Bool)), stay(Unit)): a pair over a
    // function code is no code of the universe's flows.
    let function_code = arena.value_quote(functions.function);
    let at_function = arena.value_stay(function_code);
    let higher = arena.value_flow_product(at_function, stay);
    let pair = arena.value_type_product(&[functions.function, unit]);
    let higher_type = directed(&mut arena, (pair, pair));
    let module = [
        declaration(At(0), functions.function, functions.not),
        declaration(At(1), crossed, swapped),
        declaration(At(2), integral_type, integral),
        declaration(At(3), higher_type, higher),
    ];
    let (report, _readmission) = judged(&mut arena, &module);
    assert!(
        matches!(refusal(&report, At(1)), CheckRefusal::TypeMismatch(_)),
        "a flow product checked at another pairing is a mismatch: {report:?}"
    );
    assert!(
        matches!(
            refusal(&report, At(2)),
            CheckRefusal::ShapeMismatch { at, wanted: ExpectedShape::Flow, .. }
                if at == TermNode::Value(at_integer)
        ),
        "a flow at Integer is refused at the component: {report:?}"
    );
    assert!(
        matches!(refusal(&report, At(3)), CheckRefusal::PathCode(code) if code == function_code),
        "a function code is refused by name: {report:?}"
    );
    let refused: Vec<usize> = report
        .judged()
        .iter()
        .enumerate()
        .filter(|&(_, judged)| matches!(judged.verdict(), Verdict::Refused(_)))
        .map(|(position, _)| position)
        .collect();
    assert_eq!(refused, [1, 2, 3], "negation itself checks");
}
