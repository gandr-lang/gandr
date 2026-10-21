use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::identity::back;
use gandr_core_term::identity::cong;
use gandr_core_term::identity::then;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::NullSink;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;

use super::Clause;
use super::Coordinate;
use super::Fibre;
use super::clause;
use super::fibre;
use crate::arena::DomainArena;
use crate::arena::DomainValueId;
use crate::eval::Definitions;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_computation;
use crate::eval::eval_value;
use crate::machine::MachineSettings;
use crate::machine::MachineVerdict;
use crate::machine::Problem;
use crate::machine::decide;
use crate::readback::ReadbackMode;
use crate::readback::readback_computation;

/// A budget far above any fixture below.
///
/// # Specification
/// trivial.
fn ample() -> Fuel
{
    Fuel::from(4_096_u32)
}

/// The text literals the fixtures below compare.
#[derive(Clone, Copy)]
enum Word
{
    /// `"five"`.
    Five,
    /// `"six"`.
    Six,
    /// `"seven"`.
    Seven,
}

/// A text literal.
///
/// # Specification
/// trivial.
fn literal(
    core: &mut CoreArena,
    word: Word,
) -> ValueId
{
    let content = match word {
        Word::Five => "five",
        Word::Six => "six",
        Word::Seven => "seven",
    };
    core.value_literal(Literal::Text(StringLiteral::new(String::from(content))))
}

/// A rigid stand-in for a path no rule reduces: a constant with no body.
///
/// # Specification
/// trivial.
fn stuck(
    core: &mut CoreArena,
    position: ConstantIndex,
) -> ValueId
{
    core.value_constant(position)
}

/// The normal form of a computation, wrapped as a thunk for comparison.
///
/// # Specification
/// trivial.
fn normal(
    core: &mut CoreArena,
    computation: ComputationId,
) -> ValueId
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(core, &mut domain, definitions, ample(), computation)
        .expect("closed identity terms evaluate");
    let read = readback_computation(
        core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("closed identity terms read back");
    core.value_thunk(read)
}

/// How the normal form of `computation` compares with `expected` as
/// written.
///
/// # Specification
/// trivial.
fn normalises_to(
    core: &mut CoreArena,
    computation: ComputationId,
    expected: ComputationId,
) -> CertificateEquality
{
    let read = normal(core, computation);
    let expected = core.value_thunk(expected);
    equal_certificate_syntax(core, read, expected)
}

/// The evaluated values `values` stand for, in a fresh domain.
///
/// # Specification
/// trivial.
fn evaluated<const N: usize>(
    core: &CoreArena,
    domain: &mut DomainArena,
    values: [ValueId; N],
) -> [DomainValueId; N]
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    values.map(|value| {
        eval_value(core, domain, definitions, ample(), value).expect("closed values evaluate")
    })
}

/// The string base type.
///
/// # Specification
/// trivial.
fn text_type(core: &mut CoreArena) -> ValueTypeId
{
    core.value_type_base(BaseType::String)
}

/// The diagonal `y. Path(Text, y, y)`: a motive that reads its binder at
/// both endpoints, so no rule moves it along a stuck path.
///
/// # Specification
/// trivial.
fn diagonal(core: &mut CoreArena) -> ValueTypeId
{
    let carrier = text_type(core);
    let moving = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    core.value_type_path(carrier, moving, moving)
}

#[test]
fn transport_along_here_is_the_identity()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let seven = literal(&mut core, Word::Seven);
    let carrier = text_type(&mut core);
    let moving = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let motive = core.value_type_path(carrier, moving, moving);
    let path = core.value_here(five);
    let operand = core.value_here(seven);
    let transported = core.computation_path_transport(motive, path, operand);
    let expected = core.computation_return(operand);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "transport along reflexivity returns its operand untouched"
    );
}

#[test]
fn transport_in_the_singleton_returns_the_path()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let carrier = text_type(&mut core);
    let endpoint = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let singleton = core.value_type_path(carrier, five, endpoint);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let start = core.value_here(five);
    let transported = core.computation_path_transport(singleton, path, start);
    let expected = core.computation_return(path);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "reflexivity transported in the singleton is the path itself"
    );
    let diagonal = core.value_type_path(carrier, endpoint, endpoint);
    let moved = core.computation_path_transport(diagonal, path, start);
    assert_eq!(
        normalises_to(&mut core, moved, moved),
        CertificateEquality::Equal,
        "a family whose left endpoint is the binder is no singleton and stays stuck"
    );
}

#[test]
fn transport_along_a_stuck_path_is_stuck()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let here = core.value_here(five);
    let motive = diagonal(&mut core);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let transported = core.computation_path_transport(motive, path, here);
    assert_eq!(
        normalises_to(&mut core, transported, transported),
        CertificateEquality::Equal,
        "a transport along a path no rule reduces reads back as itself"
    );
}

#[test]
fn transport_in_a_constant_motive_returns_the_operand()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let carrier = text_type(&mut core);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let transported = core.computation_path_transport(carrier, path, five);
    let returned = core.computation_return(five);
    assert_eq!(
        normalises_to(&mut core, transported, returned),
        CertificateEquality::Equal,
        "a motive that never reads its binder returns the operand along any path, as the kernel's constant row does"
    );
}

/// The telescope motive `Π (y : Text). Π (z : Text). F Path(Text, z, y)`,
/// whose fibre at a point is no singleton, so its transport keeps the
/// operand's own form.
///
/// # Specification
/// trivial.
fn telescope_motive(core: &mut CoreArena) -> gandr_core_term::CompTypeId
{
    let carrier = text_type(core);
    let outer = core.value_variable(gandr_core_term::Zone::Intuitionistic, 1_u32.into());
    let inner = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let body = core.value_type_path(carrier, inner, outer);
    let returned = core.comp_type_returner(body);
    let entry = core.comp_type_pi(carrier, returned);
    core.comp_type_pi(carrier, entry)
}

#[test]
fn telescope_transport_along_here_is_the_identity()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let seven = literal(&mut core, Word::Seven);
    let motive = telescope_motive(&mut core);
    let path = core.value_here(five);
    let over = core.value_here(six);
    let operand = core.value_here(seven);
    let transported = core.computation_telescope_transport(motive, path, six, over, operand);
    let expected = core.computation_return(operand);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "transport along reflexivity over reflexivity returns its operand untouched"
    );
}

#[test]
fn telescope_transport_along_here_replays_the_fibre()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let seven = literal(&mut core, Word::Seven);
    let motive = telescope_motive(&mut core);
    let path = core.value_here(five);
    let over = stuck(&mut core, ConstantIndex::from(0_usize));
    let operand = core.value_here(seven);
    let transported = core.computation_telescope_transport(motive, path, six, over, operand);
    let carrier = text_type(&mut core);
    let inner = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let fibre = core.value_type_path(carrier, inner, five);
    let expected = core.computation_path_transport(fibre, over, operand);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "along reflexivity the operand transports along the identity over it in the fibre \
             at the path's point"
    );
}

#[test]
fn telescope_transport_along_a_stuck_path_is_stuck()
{
    let mut core = CoreArena::new();
    let six = literal(&mut core, Word::Six);
    let seven = literal(&mut core, Word::Seven);
    let motive = telescope_motive(&mut core);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let over = stuck(&mut core, ConstantIndex::from(1_usize));
    let transported = core.computation_telescope_transport(motive, path, six, over, seven);
    assert_eq!(
        normalises_to(&mut core, transported, transported),
        CertificateEquality::Equal,
        "a telescope transport along a path no rule reduces reads back as itself"
    );
    let other = core.computation_telescope_transport(motive, path, seven, over, seven);
    assert_eq!(
        normalises_to(&mut core, transported, other),
        CertificateEquality::Different,
        "the stuck form keeps its start"
    );
}

#[test]
fn transport_through_a_product_is_componentwise()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let seven = literal(&mut core, Word::Seven);
    let here = core.value_here(five);
    let diagonal = diagonal(&mut core);
    let unit = core.value_type_unit();
    let motive = core.value_type_product(&[diagonal, unit]);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let empty = core.value_unit();
    let operand = core.value_tuple(&[here, empty]);
    let transported = core.computation_path_transport(motive, path, operand);

    let first = core.computation_path_transport(diagonal, path, here);
    // The first coordinate's transport is stuck on the path, so the second
    // waits under its bind; the unit coordinate never reads the binder, so
    // its transport returns the empty tuple there.
    let moved = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let pair = core.value_tuple(&[moved, empty]);
    let returned = core.computation_return(pair);
    let expected = core.computation_bind(first, returned);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "each coordinate is transported in its own motive, bound before the next"
    );
    let held = core.value_returned(first);
    let standing = core.value_tuple(&[held, empty]);
    let standing = core.computation_return(standing);
    assert_eq!(
        normalises_to(&mut core, transported, standing),
        CertificateEquality::Different,
        "a stuck coordinate holds the tuple rather than standing for what it returns"
    );
    let swapped = core.value_tuple(&[empty, moved]);
    let swapped = core.computation_return(swapped);
    let swapped = core.computation_bind(first, swapped);
    assert_eq!(
        normalises_to(&mut core, transported, swapped),
        CertificateEquality::Different
    );
    let elsewhere = core.value_here(seven);
    let other = core.computation_path_transport(diagonal, path, elsewhere);
    let other = core.computation_bind(other, returned);
    assert_eq!(
        normalises_to(&mut core, transported, other),
        CertificateEquality::Different
    );
}

#[test]
fn transport_through_a_sum_keeps_the_summand()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let here = core.value_here(five);
    let diagonal = diagonal(&mut core);
    let unit = core.value_type_unit();
    let motive = core.value_type_sum(&[unit, diagonal]);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let operand = core.value_injection(Side::Right.into(), here);
    let transported = core.computation_path_transport(motive, path, operand);

    let payload = core.computation_path_transport(diagonal, path, here);
    let moved = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let injected = core.value_injection(Side::Right.into(), moved);
    let injected = core.computation_return(injected);
    let expected = core.computation_bind(payload, injected);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "the payload is transported in its summand's motive and bound into its injection"
    );
    let wrong = core.value_injection(Side::Left.into(), moved);
    let wrong = core.computation_return(wrong);
    let wrong = core.computation_bind(payload, wrong);
    assert_eq!(
        normalises_to(&mut core, transported, wrong),
        CertificateEquality::Different
    );
}

#[test]
fn transport_moves_a_list_through_a_universe_path()
{
    // Negation as a universe equivalence of Bool with itself, in the
    // motive `y. List(El y)`: each head is carried along it, in order.
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let [truth, falsity] =
        [Side::Left, Side::Right].map(|side| core.value_injection(side.into(), unit));
    let negated = [falsity, truth].map(|value| core.computation_return(value));
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_case(bound, &negated);
    let lambda = core.computation_lambda(body);
    let not = core.value_thunk(lambda);
    let path = core.value_equiv(not, not);
    let element = core.value_type_element(bound, gandr_kernel_strata::Level::zero());
    let motive = core.value_type_list(element);
    let list = |core: &mut CoreArena, heads: [ValueId; 2]| {
        let nil = core.value_list_nil();
        heads
            .iter()
            .rev()
            .fold(nil, |tail, &head| core.value_list_cons(head, tail))
    };
    let operand = list(&mut core, [truth, falsity]);
    let transported = core.computation_path_transport(motive, path, operand);
    let moved = list(&mut core, [falsity, truth]);
    let expected = core.computation_return(moved);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "each head is negated and the spine kept"
    );
    let kept = core.computation_return(operand);
    assert_eq!(
        normalises_to(&mut core, transported, kept),
        CertificateEquality::Different
    );
    let nil = core.value_list_nil();
    let empty = core.computation_path_transport(motive, path, nil);
    let returned = core.computation_return(nil);
    assert_eq!(
        normalises_to(&mut core, empty, returned),
        CertificateEquality::Equal,
        "the empty list is carried unchanged"
    );
}

#[test]
fn transport_in_the_decoded_binder_along_a_stuck_path_stays_in_its_motive()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let truth = core.value_injection(Side::Left.into(), unit);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let motive = core.value_type_element(bound, gandr_kernel_strata::Level::zero());
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let transported = core.computation_path_transport(motive, path, truth);
    assert_eq!(
        normalises_to(&mut core, transported, transported),
        CertificateEquality::Equal,
        "only a universe path is handed to native transport; a stuck one keeps its motive"
    );
}

#[test]
fn transport_along_univalence_applies_the_forward_map()
{
    // A record whose forward map is negation and whose inverses are the
    // identity: transport in the decoded binder applies the forward map,
    // never an inverse, and the laws are not run.
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let [truth, falsity] =
        [Side::Left, Side::Right].map(|side| core.value_injection(side.into(), unit));
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let negated = [falsity, truth].map(|value| core.computation_return(value));
    let body = core.computation_case(bound, &negated);
    let lambda = core.computation_lambda(body);
    let not = core.value_thunk(lambda);
    let kept = core.computation_return(bound);
    let lambda = core.computation_lambda(kept);
    let same = core.value_thunk(lambda);
    let left = core.value_tuple(&[same, unit]);
    let right = core.value_tuple(&[same, unit]);
    let inverses = core.value_tuple(&[left, right]);
    let record = core.value_tuple(&[not, inverses]);
    let forward = gandr_core_term::identity::univalence_forward(&mut core, record);
    let path = core.value_univalence(record, forward);
    let motive = core.value_type_element(bound, gandr_kernel_strata::Level::zero());
    let transported = core.computation_path_transport(motive, path, truth);
    let moved = core.computation_return(falsity);
    assert_eq!(
        normalises_to(&mut core, transported, moved),
        CertificateEquality::Equal,
        "the point is carried by the record's forward map"
    );
    let unmoved = core.computation_return(truth);
    assert_eq!(
        normalises_to(&mut core, transported, unmoved),
        CertificateEquality::Different
    );
}

/// A map on the booleans, `truth` the left injection of the unit.
#[derive(Clone, Copy)]
enum Map
{
    /// The identity.
    Same,
    /// Negation.
    Not,
    /// Constantly `falsity`.
    False,
}

/// The booleans' two points, `[truth, falsity]`.
///
/// # Specification
/// trivial.
fn booleans(core: &mut CoreArena) -> [ValueId; 2]
{
    let unit = core.value_unit();
    [Side::Left, Side::Right].map(|side| core.value_injection(side.into(), unit))
}

/// The thunk of a map on the booleans.
///
/// # Specification
/// trivial.
fn boolean_map(
    core: &mut CoreArena,
    map: Map,
) -> ValueId
{
    let [truth, falsity] = booleans(core);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let body = match map {
        Map::Same => core.computation_return(bound),
        Map::Not => {
            let negated = [falsity, truth].map(|value| core.computation_return(value));
            core.computation_case(bound, &negated)
        },
        Map::False => core.computation_return(falsity),
    };
    let lambda = core.computation_lambda(body);
    core.value_thunk(lambda)
}

/// `ua(#{f, #{#{g, ()}, #{h, ()}}})` over three maps on the booleans: the
/// forward map, the left inverse and the right inverse. The laws are the
/// unit, which the evaluator never runs.
///
/// # Specification
/// trivial.
fn boolean_univalence(
    core: &mut CoreArena,
    maps: [Map; 3],
) -> ValueId
{
    let unit = core.value_unit();
    let [forward, left, right] = maps.map(|map| boolean_map(core, map));
    let left = core.value_tuple(&[left, unit]);
    let right = core.value_tuple(&[right, unit]);
    let inverses = core.value_tuple(&[left, right]);
    let record = core.value_tuple(&[forward, inverses]);
    let forward = gandr_core_term::identity::univalence_forward(core, record);
    core.value_univalence(record, forward)
}

/// The universe of value codes at level zero, a code standing as a path's
/// fixed endpoint, and the decode of a motive's own binder.
///
/// # Specification
/// trivial.
fn universe_parts(core: &mut CoreArena) -> (ValueTypeId, ValueId, ValueTypeId)
{
    let universe = core.value_type_universe(
        gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let text = text_type(core);
    let code = core.value_quote(text);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let decode = core.value_type_element(bound, Level::zero());
    (universe, code, decode)
}

#[test]
fn transport_back_along_univalence_applies_the_left_inverse()
{
    // Forward negation, the identity as left inverse and constant falsity
    // as right inverse: back along the path carries `truth` to itself, where
    // the forward map or the right inverse would carry it to `falsity`.
    let mut core = CoreArena::new();
    let path = boolean_univalence(&mut core, [Map::Not, Map::Same, Map::False]);
    let (universe, code, decode) = universe_parts(&mut core);
    let reversed = back(&mut core, universe, code, path);
    let reversed = core.value_returned(reversed);
    let [truth, falsity] = booleans(&mut core);
    let transported = core.computation_path_transport(decode, reversed, truth);
    let [kept, moved] = [truth, falsity].map(|value| core.computation_return(value));
    assert_eq!(
        normalises_to(&mut core, transported, kept),
        CertificateEquality::Equal,
        "back along `ua(e)` applies the record's left inverse"
    );
    assert_eq!(
        normalises_to(&mut core, transported, moved),
        CertificateEquality::Different
    );
}

#[test]
fn transport_back_along_univalence_projects_a_held_record()
{
    // A record the evaluator holds as itself, as it holds a definition the
    // conversion has not unfolded: back along `ua(e)` the left inverse is
    // projected from it one component at a time and forced at the operand,
    // each projection on the record's spine. The spine reads back with each
    // projection bound in the next one's head,
    // `g ← (l ← (x ← e.1; x.0); l.0); force g v`.
    let mut core = CoreArena::new();
    let record = stuck(&mut core, ConstantIndex::from(0_usize));
    let forward = gandr_core_term::identity::univalence_forward(&mut core, record);
    let path = core.value_univalence(record, forward);
    let (universe, code, decode) = universe_parts(&mut core);
    let reversed = back(&mut core, universe, code, path);
    let reversed = core.value_returned(reversed);
    let [truth, _] = booleans(&mut core);
    let transported = core.computation_path_transport(decode, reversed, truth);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let [first, second] = [0_usize, 1_usize].map(gandr_kernel_term::Component::from);
    let inverses = core.computation_tuple_projection(record, second);
    let section = core.computation_tuple_projection(bound, first);
    let inverse_pair = core.computation_bind(inverses, section);
    let inverse = core.computation_bind(inverse_pair, section);
    let forced = core.computation_force(bound);
    let applied = core.computation_application(forced, truth);
    let expected = core.computation_bind(inverse, applied);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "the left inverse is projected from a held record"
    );
}

/// `x ← tr(motive, path, function); force x truth`: the transported function
/// applied to `truth`.
///
/// # Specification
/// trivial.
fn applied_after_transport(
    core: &mut CoreArena,
    (motive, path, function): (ValueTypeId, ValueId, ValueId),
) -> gandr_core_term::ComputationId
{
    let [truth, _] = booleans(core);
    let transported = core.computation_path_transport(motive, path, function);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let forced = core.computation_force(bound);
    let applied = core.computation_application(forced, truth);
    core.computation_bind(transported, applied)
}

#[test]
fn a_function_moves_along_univalence_by_its_maps()
{
    // In `y. U(El(y) → F El(y))` along `ua(e)` with negation forward and the
    // identity as left inverse, the identity function moves to `a. not(id(a))`,
    // so `truth` goes to `falsity`. Moving the argument forward, moving it
    // back by the right inverse (constant `falsity`), or leaving the result
    // unmoved each send `truth` to `truth`.
    let mut core = CoreArena::new();
    let path = boolean_univalence(&mut core, [Map::Not, Map::Same, Map::False]);
    let (_, _, decode) = universe_parts(&mut core);
    let returner = core.comp_type_returner(decode);
    let arrow = core.comp_type_arrow(decode, returner);
    let motive = core.value_type_thunk(arrow);
    let function = boolean_map(&mut core, Map::Same);
    let run = applied_after_transport(&mut core, (motive, path, function));
    let [truth, falsity] = booleans(&mut core);
    let [kept, moved] = [truth, falsity].map(|value| core.computation_return(value));
    assert_eq!(
        normalises_to(&mut core, run, moved),
        CertificateEquality::Equal,
        "the argument moves back by the left inverse and the result forward"
    );
    assert_eq!(
        normalises_to(&mut core, run, kept),
        CertificateEquality::Different
    );
}

#[test]
fn a_function_moves_along_an_equivalence_by_its_maps()
{
    // In `y. U(El(y) → F El(y))` along `equiv(not, id)`, the identity
    // function moves to `a. not(id(a))`: the argument moves back by the
    // backward map and the result forward by the forward map, so `truth`
    // goes to `falsity`. Moving the argument forward too would send `truth`
    // to `truth`.
    let mut core = CoreArena::new();
    let [forward, backward] = [Map::Not, Map::Same].map(|map| boolean_map(&mut core, map));
    let path = core.value_equiv(forward, backward);
    let (_, _, decode) = universe_parts(&mut core);
    let returner = core.comp_type_returner(decode);
    let arrow = core.comp_type_arrow(decode, returner);
    let motive = core.value_type_thunk(arrow);
    let function = boolean_map(&mut core, Map::Same);
    let run = applied_after_transport(&mut core, (motive, path, function));
    let [truth, falsity] = booleans(&mut core);
    let [kept, moved] = [truth, falsity].map(|value| core.computation_return(value));
    assert_eq!(
        normalises_to(&mut core, run, moved),
        CertificateEquality::Equal,
        "the argument moves back by the backward map and the result forward"
    );
    assert_eq!(
        normalises_to(&mut core, run, kept),
        CertificateEquality::Different
    );
}

#[test]
fn a_function_with_a_constant_argument_moves_its_result_only()
{
    // In `y. U(Bool → F El(y))` the argument's type reads no binder, so the
    // argument stays as it is and only the result moves: the identity
    // function moves to `a. not(a)` and `truth` goes to `falsity`. Moving
    // the argument back by the left inverse, constant `falsity` here, would
    // send `truth` to `truth`.
    let mut core = CoreArena::new();
    let path = boolean_univalence(&mut core, [Map::Not, Map::False, Map::Same]);
    let (_, _, decode) = universe_parts(&mut core);
    let unit = core.value_type_unit();
    let boolean = core.value_type_sum(&[unit, unit]);
    let returner = core.comp_type_returner(decode);
    let arrow = core.comp_type_arrow(boolean, returner);
    let motive = core.value_type_thunk(arrow);
    let function = boolean_map(&mut core, Map::Same);
    let run = applied_after_transport(&mut core, (motive, path, function));
    let [truth, falsity] = booleans(&mut core);
    let [kept, moved] = [truth, falsity].map(|value| core.computation_return(value));
    assert_eq!(
        normalises_to(&mut core, run, moved),
        CertificateEquality::Equal,
        "only the result moves along the path"
    );
    assert_eq!(
        normalises_to(&mut core, run, kept),
        CertificateEquality::Different
    );
}

#[test]
fn a_transported_function_returns_a_stuck_result_as_its_value()
{
    // In `y. U(Bool → F El(y))` along `ua(e)` with negation forward, a
    // function `f` no definition reaches moves to `b. not(⟨f b⟩)`: its stuck
    // result is bound as the value it returns, so the endpoint the conversion
    // holds converts with the forward map at the returned call, and not with
    // the call left where it was.
    let mut core = CoreArena::new();
    let path = boolean_univalence(&mut core, [Map::Not, Map::False, Map::Same]);
    let (_, _, decode) = universe_parts(&mut core);
    let unit = core.value_type_unit();
    let boolean = core.value_type_sum(&[unit, unit]);
    let returner = core.comp_type_returner(decode);
    let arrow = core.comp_type_arrow(boolean, returner);
    let motive = core.value_type_thunk(arrow);
    let function = stuck(&mut core, ConstantIndex::from(0_usize));
    let transported = core.computation_path_transport(motive, path, function);
    let endpoint = core.value_returned(transported);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let forced = core.computation_force(function);
    let call = core.computation_application(forced, bound);
    let result = core.value_returned(call);
    let negation = boolean_map(&mut core, Map::Not);
    let negate = core.computation_force(negation);
    let moved = core.computation_application(negate, result);
    let kept = core.computation_return(result);
    let [moved, kept] = [moved, kept].map(|body| {
        let lambda = core.computation_lambda(body);
        core.value_thunk(lambda)
    });
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root())
        .reading_endpoints(crate::eval::Endpoints::Hold);
    let mut domain = DomainArena::new();
    let [endpoint, moved, kept] = [endpoint, moved, kept].map(|value| {
        eval_value(&core, &mut domain, definitions, ample(), value).expect("closed values evaluate")
    });
    let mut decided = |point| {
        decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(endpoint, point),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict()
    };
    assert_eq!(
        decided(moved),
        MachineVerdict::Convertible,
        "the result moves forward as the value the call returns"
    );
    assert_ne!(decided(kept), MachineVerdict::Convertible);
}

#[test]
fn a_function_with_a_constant_result_leaves_its_call_unmoved()
{
    // In `y. U(El(y) → F Bool)` along `ua(e)` with negation as left inverse,
    // a function `f` no definition reaches moves to `b. f(⟨not(b)⟩)`: the
    // argument's stuck move is bound as the value it returns, and the
    // result's type reads no binder, so the call stays as it is.
    let mut core = CoreArena::new();
    let path = boolean_univalence(&mut core, [Map::Same, Map::Not, Map::Same]);
    let (_, _, decode) = universe_parts(&mut core);
    let unit = core.value_type_unit();
    let boolean = core.value_type_sum(&[unit, unit]);
    let returner = core.comp_type_returner(boolean);
    let arrow = core.comp_type_arrow(decode, returner);
    let motive = core.value_type_thunk(arrow);
    let function = stuck(&mut core, ConstantIndex::from(0_usize));
    let transported = core.computation_path_transport(motive, path, function);
    let endpoint = core.value_returned(transported);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let negation = boolean_map(&mut core, Map::Not);
    let negate = core.computation_force(negation);
    let negated = core.computation_application(negate, bound);
    let argument = core.value_returned(negated);
    let forced = core.computation_force(function);
    let call = core.computation_application(forced, argument);
    let unmoved = core.computation_application(forced, bound);
    let [call, unmoved] = [call, unmoved].map(|body| {
        let lambda = core.computation_lambda(body);
        core.value_thunk(lambda)
    });
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root())
        .reading_endpoints(crate::eval::Endpoints::Hold);
    let mut domain = DomainArena::new();
    let [endpoint, call, unmoved] = [endpoint, call, unmoved].map(|value| {
        eval_value(&core, &mut domain, definitions, ample(), value).expect("closed values evaluate")
    });
    let mut decided = |point| {
        decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(endpoint, point),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict()
    };
    assert_eq!(
        decided(call),
        MachineVerdict::Convertible,
        "the argument moves back and the call stays as it is"
    );
    assert_ne!(decided(unmoved), MachineVerdict::Convertible);
}

#[test]
fn a_held_back_reads_back_as_its_transport()
{
    // `back(ua(e))` returns the transport that formed it, held as a path:
    // its reversed family, the univalence it moved along and `here` at the
    // fixed endpoint, each in its own slot.
    use gandr_core_term::Computation;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;

    let mut core = CoreArena::new();
    let path = boolean_univalence(&mut core, [Map::Not, Map::Same, Map::False]);
    let (universe, code, _) = universe_parts(&mut core);
    let reversed = back(&mut core, universe, code, path);
    let normal = normal(&mut core, reversed);
    let Some(&Value::Thunk(read)) = core.value(normal)
    else {
        panic!("a normal form is wrapped as a thunk");
    };
    let Some(&Computation::Return(held)) = core.computation(read)
    else {
        panic!("`back(ua(e))` returns a path");
    };
    let Some(&Value::Returned(formed)) = core.value(held)
    else {
        panic!("the path is held as the transport that formed it");
    };
    let Some(&Computation::PathTransport {
        motive,
        path: along,
        value,
    }) = core.computation(formed)
    else {
        panic!("the held path is a transport");
    };
    assert!(
        matches!(core.value(along), Some(&Value::Univalence(..))),
        "it moves along the univalence"
    );
    let start = core.value_here(code);
    assert_eq!(
        equal_certificate_syntax(&core, value, start),
        CertificateEquality::Equal,
        "from `here` at the fixed endpoint"
    );
    let Some(&ValueType::Path { left, right, .. }) = core.value_type(motive)
    else {
        panic!("in a path family");
    };
    assert!(
        matches!(core.value(left), Some(&Value::Variable { index, .. }) if u32::from(index) == 0_u32),
        "whose left endpoint moves"
    );
    assert_eq!(
        equal_certificate_syntax(&core, right, code),
        CertificateEquality::Equal,
        "and whose right endpoint is fixed"
    );
}

#[test]
fn transport_along_then_moves_along_both_paths_in_order()
{
    // The first path sends every point to `falsity` and the second negates:
    // in order `truth` arrives back at `truth`, where the other order would
    // leave it at `falsity`.
    let mut core = CoreArena::new();
    let first = boolean_univalence(&mut core, [Map::False, Map::Same, Map::Same]);
    let second = boolean_univalence(&mut core, [Map::Not, Map::Same, Map::Same]);
    let (universe, code, decode) = universe_parts(&mut core);
    let composite = then(&mut core, universe, code, first, second);
    let composite = core.value_returned(composite);
    let [truth, falsity] = booleans(&mut core);
    let transported = core.computation_path_transport(decode, composite, truth);
    let [kept, moved] = [truth, falsity].map(|value| core.computation_return(value));
    assert_eq!(
        normalises_to(&mut core, transported, kept),
        CertificateEquality::Equal,
        "along `p then q` the operand moves along `p`, then along `q`"
    );
    assert_eq!(
        normalises_to(&mut core, transported, moved),
        CertificateEquality::Different
    );
}

#[test]
fn transport_along_then_moves_a_stuck_first_leg_on()
{
    // A first path no rule reduces: its transport sticks, and the second
    // path's forward map applies to it, held as the value it stands for.
    let mut core = CoreArena::new();
    let first = stuck(&mut core, ConstantIndex::from(0_usize));
    let second = boolean_univalence(&mut core, [Map::Not, Map::Same, Map::Same]);
    let (universe, code, decode) = universe_parts(&mut core);
    let composite = then(&mut core, universe, code, first, second);
    let composite = core.value_returned(composite);
    let [truth, falsity] = booleans(&mut core);
    let transported = core.computation_path_transport(decode, composite, truth);
    let held = core.computation_path_transport(decode, first, truth);
    let held = core.value_returned(held);
    let negated = [falsity, truth].map(|value| core.computation_return(value));
    let expected = core.computation_case(held, &negated);
    assert_eq!(
        normalises_to(&mut core, transported, expected),
        CertificateEquality::Equal,
        "the second path's map applies to the first path's stuck transport"
    );
}

#[test]
fn a_compound_endpoint_stands_for_what_it_returns()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let returned = core.computation_return(five);
    let compound = core.value_returned(returned);
    let reflexive = core.value_here(compound);
    let read = core.computation_return(reflexive);
    let at_five = core.value_here(five);
    let expected = core.computation_return(at_five);
    assert_eq!(
        normalises_to(&mut core, read, expected),
        CertificateEquality::Equal,
        "a compound endpoint that returns is the value it returns"
    );

    let head = stuck(&mut core, ConstantIndex::from(0_usize));
    let forced = core.computation_force(head);
    let blocked = core.value_returned(forced);
    let blocked = core.computation_return(blocked);
    assert_eq!(
        normalises_to(&mut core, blocked, blocked),
        CertificateEquality::Equal,
        "a compound endpoint that does not return is kept, not erased"
    );
}

#[test]
fn a_compound_endpoint_runs_through_a_definition()
{
    // def id = thunk { \x. return x } ; the endpoint `id("five")`.
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let returned = core.computation_return(bound);
    let lambda = core.computation_lambda(returned);
    let body = core.value_thunk(lambda);
    let identity = core.value_constant(ConstantIndex::from(0_usize));
    let forced = core.computation_force(identity);
    let applied = core.computation_application(forced, five);
    let compound = core.value_returned(applied);
    let mut chain = gandr_core_term::DefinitionChain::new();
    chain
        .define(
            ConstantIndex::from(0_usize),
            gandr_kernel_term::GlobalIndex::from(0_u32),
            gandr_core_term::Transparency::Manifest,
            &[],
        )
        .expect("one definition enters an empty chain");
    let Ok(chain) = LoweredChain::lower(chain, |_entry| Ok::<_, core::convert::Infallible>(body));
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let [endpoint, point] = [compound, five].map(|value| {
        eval_value(&core, &mut domain, definitions, ample(), value).expect("closed values evaluate")
    });
    let verdict = decide::<NullSink, NullMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::values(endpoint, point),
        &mut NullSink,
    )
    .expect("the machine answers")
    .verdict();
    assert_eq!(
        verdict,
        MachineVerdict::Convertible,
        "the endpoint runs through the definition to the value it returns"
    );
    let empty = LoweredChain::new();
    let rigid = Definitions::new(&empty, &environment, environment.root());
    let mut domain = DomainArena::new();
    let [endpoint, point] = [compound, five].map(|value| {
        eval_value(&core, &mut domain, rigid, ample(), value).expect("closed values evaluate")
    });
    let verdict = decide::<NullSink, NullMemo>(
        &core,
        &mut domain,
        rigid,
        MachineSettings::default(),
        Problem::values(endpoint, point),
        &mut NullSink,
    )
    .expect("the machine answers")
    .verdict();
    assert_ne!(
        verdict,
        MachineVerdict::Convertible,
        "with the definition rigid the endpoint is stuck, not the value"
    );
}

#[test]
fn reflexivities_convert_by_their_points()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let again = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let one = core.value_here(five);
    let other = core.value_here(again);
    let apart = core.value_here(six);
    let mut domain = DomainArena::new();
    let [one, other, apart] = evaluated(&core, &mut domain, [one, other, apart]);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut decided = |left, right| {
        decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(left, right),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict()
    };
    assert_eq!(decided(one, other), MachineVerdict::Convertible);
    assert_eq!(decided(one, apart), MachineVerdict::NotConvertible);
}

#[test]
fn reflexivities_convert_by_points_a_definition_relates_345()
{
    // def five_is = "five" ; `here(five_is)` against `here("five")`.
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let defined = core.value_constant(ConstantIndex::from(0_usize));
    let declared = core.value_here(defined);
    let written = core.value_here(five);
    let apart = core.value_here(six);
    let mut chain = gandr_core_term::DefinitionChain::new();
    chain
        .define(
            ConstantIndex::from(0_usize),
            gandr_kernel_term::GlobalIndex::from(0_u32),
            gandr_core_term::Transparency::Manifest,
            &[],
        )
        .expect("one definition enters an empty chain");
    let Ok(chain) = LoweredChain::lower(chain, |_entry| Ok::<_, core::convert::Infallible>(five));
    let environment = DefinitionalEnvironment::new();
    let empty = LoweredChain::new();
    for (definitions, related) in [
        (
            Definitions::new(&chain, &environment, environment.root()),
            MachineVerdict::Convertible,
        ),
        (
            Definitions::new(&empty, &environment, environment.root()),
            MachineVerdict::NotConvertible,
        ),
    ] {
        let mut domain = DomainArena::new();
        let [declared, written, apart] = [declared, written, apart].map(|value| {
            eval_value(&core, &mut domain, definitions, ample(), value)
                .expect("closed values evaluate")
        });
        let mut decided = |left, right| {
            decide::<NullSink, NullMemo>(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                Problem::values(left, right),
                &mut NullSink,
            )
            .expect("the machine answers")
            .verdict()
        };
        assert_eq!(
            decided(declared, written),
            related,
            "the points relate exactly when the definition unfolds"
        );
        assert_eq!(decided(declared, apart), MachineVerdict::NotConvertible);
    }
}

#[test]
fn stuck_transports_compare_by_motive_and_operand()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let (here, there) = (core.value_here(five), core.value_here(six));
    let motive = diagonal(&mut core);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let transported = core.computation_path_transport(motive, path, here);
    let elsewhere = core.computation_path_transport(motive, path, there);
    // `y. Path(Text, y, five)` also reads its binder and is no singleton.
    let carrier = text_type(&mut core);
    let moving = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let fixed = core.value_type_path(carrier, moving, five);
    let remotivated = core.computation_path_transport(fixed, path, here);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mut run = |term| {
        eval_computation(&core, &mut domain, definitions, ample(), term)
            .expect("closed transports evaluate")
    };
    let (one, other, apart, remotivated) = (
        run(transported),
        run(transported),
        run(elsewhere),
        run(remotivated),
    );
    let mut decided = |left, right| {
        decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::computations(left, right),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict()
    };
    assert_eq!(decided(one, other), MachineVerdict::Convertible);
    assert_eq!(decided(one, apart), MachineVerdict::NotConvertible);
    assert_eq!(decided(one, remotivated), MachineVerdict::NotConvertible);
}

#[test]
fn stuck_transports_under_one_motive_over_captures_it_does_not_read_settle_alike()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let here = core.value_here(five);
    let motive = diagonal(&mut core);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    // `λa. λb. transport(y. Path(Text, y, y), p, here(5))`, entered at two
    // argument orders: each motive closes over `[a, b]`, which its body never
    // reads, the way a definition's family does at two of its calls.
    let transported = core.computation_path_transport(motive, path, here);
    let inner = core.computation_lambda(transported);
    let body = core.computation_lambda(inner);
    let mut called = |first, second| {
        let once = core.computation_application(body, first);
        core.computation_application(once, second)
    };
    let (forward, swapped) = (called(five, six), called(six, five));
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mut run = |term| {
        eval_computation(&core, &mut domain, definitions, ample(), term)
            .expect("closed transports evaluate")
    };
    let (one, other) = (run(forward), run(swapped));
    assert_eq!(
        crate::conv::convert_computations(&core, &domain, one, other),
        Ok(crate::conv::Settlement::StructurallyEqual),
        "the captures the motive does not read leave the two one family"
    );
}

#[test]
fn then_associates_at_reflexivity()
{
    let mut core = CoreArena::new();
    let carrier = text_type(&mut core);
    let five = literal(&mut core, Word::Five);
    let here = core.value_here(five);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    // Every operand is closed, so the bound composite needs no shift.
    // (here · here) · here
    let inner = then(&mut core, carrier, five, here, here);
    let outer = then(&mut core, carrier, five, bound, here);
    let left = core.computation_bind(inner, outer);
    // here · (here · here)
    let inner = then(&mut core, carrier, five, here, here);
    let outer = then(&mut core, carrier, five, here, bound);
    let right = core.computation_bind(inner, outer);
    let expected = core.computation_return(here);
    assert_eq!(
        normalises_to(&mut core, left, expected),
        CertificateEquality::Equal
    );
    assert_eq!(
        normalises_to(&mut core, right, expected),
        CertificateEquality::Equal
    );
}

#[test]
fn then_is_unital_at_a_stuck_path()
{
    let mut core = CoreArena::new();
    let carrier = text_type(&mut core);
    let five = literal(&mut core, Word::Five);
    let path = stuck(&mut core, ConstantIndex::from(0_usize));
    let here = core.value_here(five);
    let composed = then(&mut core, carrier, five, path, here);
    let expected = core.computation_return(path);
    assert_eq!(
        normalises_to(&mut core, composed, expected),
        CertificateEquality::Equal,
        "composing with reflexivity on the right is the path itself"
    );
    let reversed = then(&mut core, carrier, five, here, path);
    assert_eq!(
        normalises_to(&mut core, reversed, expected),
        CertificateEquality::Equal,
        "composing with reflexivity on the left is the singleton's transport, the path itself"
    );
}

#[test]
fn back_inverts_at_reflexivity()
{
    let mut core = CoreArena::new();
    let carrier = text_type(&mut core);
    let five = literal(&mut core, Word::Five);
    let here = core.value_here(five);
    let inverted = back(&mut core, carrier, five, here);
    let expected = core.computation_return(here);
    assert_eq!(
        normalises_to(&mut core, inverted, expected),
        CertificateEquality::Equal
    );

    // back(back(here)) and here · back(here) are reflexivity again; every
    // operand is closed, so the bound composite needs no shift.
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let first = back(&mut core, carrier, five, here);
    let twice = back(&mut core, carrier, five, bound);
    let twice = core.computation_bind(first, twice);
    assert_eq!(
        normalises_to(&mut core, twice, expected),
        CertificateEquality::Equal
    );
    let first = back(&mut core, carrier, five, here);
    let cancelled = then(&mut core, carrier, five, here, bound);
    let cancelled = core.computation_bind(first, cancelled);
    assert_eq!(
        normalises_to(&mut core, cancelled, expected),
        CertificateEquality::Equal
    );
}

#[test]
fn cong_respects_composition_at_reflexivity()
{
    let mut core = CoreArena::new();
    let carrier = text_type(&mut core);
    let pair = core.value_type_product(&[carrier, carrier]);
    let five = literal(&mut core, Word::Five);
    // f = thunk (λx. return (x, x))
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let doubled = core.value_tuple(&[bound, bound]);
    let body = core.computation_return(doubled);
    let lambda = core.computation_lambda(body);
    let function = core.value_thunk(lambda);
    let forced = core.computation_force(function);
    let applied = core.computation_application(forced, five);
    let image = core.value_returned(applied);
    let here = core.value_here(five);

    // Every operand is closed, so the bound composites need no shift.
    // cong(f, here · here)
    let composed = then(&mut core, carrier, five, here, here);
    let mapped = cong(&mut core, pair, function, image, bound);
    let left = core.computation_bind(composed, mapped);
    // cong(f, here) · cong(f, here)
    let first = cong(&mut core, pair, function, image, here);
    let second = cong(&mut core, pair, function, image, here);
    let outer = core.value_variable(gandr_core_term::Zone::Intuitionistic, 1_u32.into());
    let joined = then(&mut core, pair, image, outer, bound);
    let joined = core.computation_bind(second, joined);
    let right = core.computation_bind(first, joined);
    let both = core.value_tuple(&[five, five]);
    let at_image = core.value_here(both);
    let expected = core.computation_return(at_image);
    assert_eq!(
        normalises_to(&mut core, left, expected),
        CertificateEquality::Equal
    );
    assert_eq!(
        normalises_to(&mut core, right, expected),
        CertificateEquality::Equal
    );
}

#[test]
fn every_carrier_selects_its_clause()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let text = text_type(&mut core);
    let pair = core.value_type_product(&[text, text]);
    let sum = core.value_type_sum(&[unit, text]);
    let list = core.value_type_list(text);
    let returner = core.comp_type_returner(text);
    let arrow = core.comp_type_arrow(text, returner);
    let function = core.value_type_thunk(arrow);
    let suspended = core.value_type_thunk(returner);
    let universe = core.value_type_universe(
        gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let atom = core.value_type_abstract(ConstantIndex::from(0_usize));
    let code = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let decoded = core.value_type_element(code, Level::zero());
    let record = core.value_type_record(alloc::collections::BTreeMap::new());
    for (carrier, expected) in [
        (unit, Clause::Unit),
        (text, Clause::Discrete),
        (pair, Clause::Product),
        (sum, Clause::Sum),
        (list, Clause::List),
        (function, Clause::Function),
        (suspended, Clause::Unclassified),
        (universe, Clause::Universe),
        (atom, Clause::Open),
        (decoded, Clause::Open),
        (record, Clause::Unclassified),
    ] {
        assert_eq!(clause(&core, carrier), Ok(expected), "{carrier:?}");
    }
}

#[test]
fn unit_and_discrete_carriers_unfold_by_their_endpoints()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let text = text_type(&mut core);
    let empty = core.value_unit();
    let five = literal(&mut core, Word::Five);
    let again = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let head = stuck(&mut core, ConstantIndex::from(0_usize));
    let mut domain = DomainArena::new();
    let [empty, five, again, six, head] =
        evaluated(&core, &mut domain, [empty, five, again, six, head]);
    assert_eq!(fibre(&core, &domain, unit, empty, empty), Ok(Fibre::Unit));
    assert_eq!(fibre(&core, &domain, text, five, again), Ok(Fibre::Unit));
    assert_eq!(fibre(&core, &domain, text, five, six), Ok(Fibre::Empty));
    assert_eq!(fibre(&core, &domain, text, five, head), Ok(Fibre::Discrete));
}

#[test]
fn different_injections_have_no_path()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let text = text_type(&mut core);
    let sum = core.value_type_sum(&[unit, text]);
    let empty = core.value_unit();
    let five = literal(&mut core, Word::Five);
    let left = core.value_injection(Side::Left.into(), empty);
    let right = core.value_injection(Side::Right.into(), five);
    let mut domain = DomainArena::new();
    let [left, right] = evaluated(&core, &mut domain, [left, right]);
    assert_eq!(fibre(&core, &domain, sum, left, right), Ok(Fibre::Empty));
    assert_eq!(fibre(&core, &domain, sum, right, left), Ok(Fibre::Empty));
}

#[test]
fn matching_injections_recurse_into_the_payload()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let text = text_type(&mut core);
    let sum = core.value_type_sum(&[unit, text]);
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let one = core.value_injection(Side::Right.into(), five);
    let other = core.value_injection(Side::Right.into(), six);
    let head = stuck(&mut core, ConstantIndex::from(0_usize));
    let mut domain = DomainArena::new();
    let [one, other, five, six, head] =
        evaluated(&core, &mut domain, [one, other, five, six, head]);
    let Ok(Fibre::Payload(coordinate)) = fibre(&core, &domain, sum, one, other)
    else {
        panic!("matching injections recurse");
    };
    assert_eq!(coordinate.carrier(), text);
    assert_eq!(
        [coordinate.left(), coordinate.right()].map(|id| domain.value(id).copied()),
        [five, six].map(|id| domain.value(id).copied())
    );
    assert_eq!(fibre(&core, &domain, sum, one, head), Ok(Fibre::Suspended));
}

#[test]
fn product_paths_are_componentwise()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let text = text_type(&mut core);
    let pair = core.value_type_product(&[text, unit]);
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let empty = core.value_unit();
    let one = core.value_tuple(&[five, empty]);
    let other = core.value_tuple(&[six, empty]);
    let mut domain = DomainArena::new();
    let [one, other] = evaluated(&core, &mut domain, [one, other]);
    let Ok(Fibre::Components(coordinates)) = fibre(&core, &domain, pair, one, other)
    else {
        panic!("tuples are componentwise");
    };
    let carriers: Vec<ValueTypeId> = coordinates.iter().map(Coordinate::carrier).collect();
    assert_eq!(carriers, [text, unit]);
    let first = coordinates.first().expect("two coordinates");
    let Some(&crate::domain::DomainValue::Literal { literal, .. }) = domain.value(first.right())
    else {
        panic!("the first coordinate relates the texts");
    };
    assert_eq!(core.value(literal), core.value(six));
}

#[test]
fn a_product_endpoint_of_another_width_is_refused_on_either_side()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let pair = core.value_type_product(&[unit, unit]);
    let empty = core.value_unit();
    let wide = core.value_tuple(&[empty, empty]);
    let narrow = core.value_tuple(&[empty]);
    let mut domain = DomainArena::new();
    let [wide, narrow] = evaluated(&core, &mut domain, [wide, narrow]);
    for (left, right) in [(wide, narrow), (narrow, wide)] {
        assert_eq!(
            fibre(&core, &domain, pair, left, right),
            Err(super::IdentityFault::Domain(crate::DomainFault::Dangling))
        );
    }
}

#[test]
fn list_paths_follow_the_constructors()
{
    let mut core = CoreArena::new();
    let text = text_type(&mut core);
    let list = core.value_type_list(text);
    let five = literal(&mut core, Word::Five);
    let nil = core.value_list_nil();
    let cell = core.value_list_cons(five, nil);
    let mut domain = DomainArena::new();
    let [nil, cell] = evaluated(&core, &mut domain, [nil, cell]);
    assert_eq!(fibre(&core, &domain, list, nil, nil), Ok(Fibre::Unit));
    assert_eq!(fibre(&core, &domain, list, nil, cell), Ok(Fibre::Empty));
    let Ok(Fibre::Components(coordinates)) = fibre(&core, &domain, list, cell, cell)
    else {
        panic!("two cells relate head and tail");
    };
    let carriers: Vec<ValueTypeId> = coordinates.iter().map(Coordinate::carrier).collect();
    assert_eq!(carriers, [text, list]);
}

#[test]
fn function_paths_relate_inputs_to_results()
{
    let mut core = CoreArena::new();
    let text = text_type(&mut core);
    let unit = core.value_type_unit();
    let returner = core.comp_type_returner(unit);
    let arrow = core.comp_type_arrow(text, returner);
    let function = core.value_type_thunk(arrow);
    let head = stuck(&mut core, ConstantIndex::from(0_usize));
    let mut domain = DomainArena::new();
    let [head] = evaluated(&core, &mut domain, [head]);
    assert_eq!(
        fibre(&core, &domain, function, head, head),
        Ok(Fibre::Related {
            domain: text,
            codomain: returner,
        })
    );
}

#[test]
fn open_carriers_unfold_to_nothing()
{
    let mut core = CoreArena::new();
    let atom = core.value_type_abstract(ConstantIndex::from(0_usize));
    let head = stuck(&mut core, ConstantIndex::from(1_usize));
    let mut domain = DomainArena::new();
    let [head] = evaluated(&core, &mut domain, [head]);
    assert_eq!(fibre(&core, &domain, atom, head, head), Ok(Fibre::Open));
}

/// `thunk (λx. return o)`, `o` built over the bound variable by `body`.
///
/// # Specification
/// trivial.
fn translator(
    core: &mut CoreArena,
    body: fn(&mut CoreArena, ValueId) -> ValueId,
) -> ValueId
{
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let built = body(core, bound);
    let returned = core.computation_return(built);
    let lambda = core.computation_lambda(returned);
    core.value_thunk(lambda)
}

/// `x ↦ (x, unit)`.
///
/// # Specification
/// trivial.
fn paired(
    core: &mut CoreArena,
    bound: ValueId,
) -> ValueId
{
    let unit = core.value_unit();
    core.value_tuple(&[bound, unit])
}

/// `x ↦ inl(x)`.
///
/// # Specification
/// trivial.
fn injected_left(
    core: &mut CoreArena,
    bound: ValueId,
) -> ValueId
{
    core.value_injection(Side::Left.into(), bound)
}

/// `x ↦ inr(x)`.
///
/// # Specification
/// trivial.
fn injected_right(
    core: &mut CoreArena,
    bound: ValueId,
) -> ValueId
{
    core.value_injection(Side::Right.into(), bound)
}

/// The motive `y. El y`: the decode of the moving code.
///
/// # Specification
/// trivial.
fn decoded(core: &mut CoreArena) -> ValueTypeId
{
    let code = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    core.value_type_element(code, Level::zero())
}

#[test]
fn flows_read_back_and_compare_by_their_parts()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let again = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let pairing = translator(&mut core, paired);
    let injecting = translator(&mut core, injected_left);
    let kept = core.value_stay(five);
    let kept_again = core.value_stay(again);
    let kept_apart = core.value_stay(six);
    let forward = core.value_forward(pairing);
    let other = core.value_forward(injecting);
    let composite = core.value_then(forward, other);
    let composite_again = core.value_then(forward, other);
    let reversed = core.value_then(other, forward);
    let function = core.value_function_flow(forward, other);
    let swapped = core.value_function_flow(other, forward);
    for flow in [kept, forward, composite, function] {
        let returned = core.computation_return(flow);
        assert_eq!(
            normalises_to(&mut core, returned, returned),
            CertificateEquality::Equal,
            "a flow reads back as its former over its parts"
        );
    }
    let mut domain = DomainArena::new();
    let [
        kept,
        kept_again,
        kept_apart,
        forward,
        other,
        composite,
        composite_again,
        reversed,
        function,
        swapped,
    ] = evaluated(&core, &mut domain, [
        kept,
        kept_again,
        kept_apart,
        forward,
        other,
        composite,
        composite_again,
        reversed,
        function,
        swapped,
    ]);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut decided = |left, right| {
        decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(left, right),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict()
    };
    assert_eq!(decided(kept, kept_again), MachineVerdict::Convertible);
    assert_eq!(decided(kept, kept_apart), MachineVerdict::NotConvertible);
    assert_eq!(decided(forward, other), MachineVerdict::NotConvertible);
    assert_eq!(decided(forward, kept), MachineVerdict::NotConvertible);
    assert_eq!(
        decided(composite, composite_again),
        MachineVerdict::Convertible
    );
    assert_eq!(decided(composite, reversed), MachineVerdict::NotConvertible);
    assert_eq!(decided(function, swapped), MachineVerdict::NotConvertible);
}

#[test]
fn rides_compute_by_the_kernels_rows()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let unit = core.value_unit();
    let text = text_type(&mut core);
    let unit_type = core.value_type_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let injecting = translator(&mut core, injected_left);
    let forward = core.value_forward(pairing);
    let other = core.value_forward(injecting);
    let flow = stuck(&mut core, ConstantIndex::from(0_usize));
    let code = core.value_quote(text);
    let kept = core.value_stay(code);

    let rode = core.computation_ride(identity, kept, five);
    let expected = core.computation_return(five);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "stay returns the value"
    );

    let rode = core.computation_ride(text, flow, five);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a motive that ignores its binder returns the value, even along a stuck flow"
    );

    let rode = core.computation_ride(identity, forward, five);
    let image = core.value_tuple(&[five, unit]);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a forward flow at the decode applies its translator"
    );

    let composite = core.value_then(forward, other);
    let rode = core.computation_ride(identity, composite, five);
    let image = core.value_tuple(&[five, unit]);
    let image = core.value_injection(Side::Left.into(), image);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a composite rides its first leg, then its second"
    );

    let product = core.value_type_product(&[identity, text]);
    let pair = core.value_tuple(&[five, six]);
    let rode = core.computation_ride(product, other, pair);
    let moved = core.value_injection(Side::Left.into(), five);
    let image = core.value_tuple(&[moved, six]);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a product motive rides componentwise"
    );

    let sum = core.value_type_sum(&[identity, unit_type]);
    let injected = core.value_injection(Side::Left.into(), five);
    let rode = core.computation_ride(sum, other, injected);
    let inner = core.value_injection(Side::Left.into(), five);
    let image = core.value_injection(Side::Left.into(), inner);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a sum motive rides the injected payload"
    );

    let list = core.value_type_list(identity);
    let nil = core.value_list_nil();
    let cell = core.value_list_cons(five, nil);
    let rode = core.computation_ride(list, other, cell);
    let moved = core.value_injection(Side::Left.into(), five);
    let image = core.value_list_cons(moved, nil);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a list motive rides every cell"
    );

    let moving = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let singleton = core.value_type_flow(text, five, moving);
    let start = core.value_stay(five);
    let rode = core.computation_ride(singleton, flow, start);
    let expected = core.computation_return(flow);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "stay ridden in the singleton is the flow itself"
    );
    let rode = core.computation_ride(singleton, flow, forward);
    let joined = core.value_then(forward, flow);
    let expected = core.computation_return(joined);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "any other value ridden in the singleton composes with the flow"
    );
    let diagonal = core.value_type_flow(text, moving, moving);
    let rode = core.computation_ride(diagonal, flow, start);
    assert_eq!(
        normalises_to(&mut core, rode, rode),
        CertificateEquality::Equal,
        "a flow family whose source moves too is no singleton, and the ride stays stuck"
    );

    let rode = core.computation_ride(identity, flow, five);
    assert_eq!(
        normalises_to(&mut core, rode, rode),
        CertificateEquality::Equal,
        "a ride along a stuck flow at the decode reads back as itself"
    );
}

#[test]
fn a_function_flow_rides_in_variance_order()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let unit = core.value_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let lefting = translator(&mut core, injected_left);
    let righting = translator(&mut core, injected_right);
    let domain_flow = core.value_forward(pairing);
    let codomain_flow = core.value_forward(righting);
    let applied = |core: &mut CoreArena, flow: ValueId| {
        let rode = core.computation_ride(identity, flow, lefting);
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let forced = core.computation_force(bound);
        let applied = core.computation_application(forced, five);
        core.computation_bind(rode, applied)
    };
    let function = core.value_function_flow(domain_flow, codomain_flow);
    let ran = applied(&mut core, function);
    let argument = core.value_tuple(&[five, unit]);
    let result = core.value_injection(Side::Left.into(), argument);
    let image = core.value_injection(Side::Right.into(), result);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, ran, expected),
        CertificateEquality::Equal,
        "the argument rides the domain flow, the function runs, the result rides the codomain flow"
    );
    let swapped = core.value_function_flow(codomain_flow, domain_flow);
    let ran = applied(&mut core, swapped);
    assert_eq!(
        normalises_to(&mut core, ran, expected),
        CertificateEquality::Different,
        "swapping the boundaries is another function"
    );
}

#[test]
fn a_flow_product_rides_a_pair_componentwise()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let unit = core.value_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let lefting = translator(&mut core, injected_left);
    let first = core.value_forward(pairing);
    let second = core.value_forward(lefting);
    let pair = core.value_tuple(&[five, six]);
    let product = core.value_flow_product(first, second);
    let rode = core.computation_ride(identity, product, pair);
    let left = core.value_tuple(&[five, unit]);
    let right = core.value_injection(Side::Left.into(), six);
    let image = core.value_tuple(&[left, right]);
    let expected = core.computation_return(image);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "each component rides its own flow at the decode"
    );
    let swapped = core.value_flow_product(second, first);
    let rode = core.computation_ride(identity, swapped, pair);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Different,
        "the first flow moves the left component"
    );
    let flow = stuck(&mut core, ConstantIndex::from(0_usize));
    let open = core.value_flow_product(flow, second);
    let rode = core.computation_ride(identity, open, pair);
    let moved = core.value_injection(Side::Left.into(), six);
    let held = core.computation_ride(identity, flow, five);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let both = core.value_tuple(&[bound, moved]);
    let returned = core.computation_return(both);
    let expected = core.computation_bind(held, returned);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a left component stuck on its flow holds the right one under its bind"
    );
    let standing = core.value_returned(held);
    let standing = core.value_tuple(&[standing, moved]);
    let standing = core.computation_return(standing);
    assert_eq!(
        normalises_to(&mut core, rode, standing),
        CertificateEquality::Different,
        "the stuck component does not stand for what it returns"
    );
}

#[test]
fn a_product_motive_binds_each_component_before_the_next()
{
    let mut core = CoreArena::new();
    let [five, six, seven] =
        [Word::Five, Word::Six, Word::Seven].map(|word| literal(&mut core, word));
    let unit = core.value_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let forward = core.value_forward(pairing);
    let motive = core.value_type_product(&[identity, identity, identity]);
    let triple = core.value_tuple(&[five, six, seven]);
    let rode = core.computation_ride(motive, forward, triple);
    let image = [five, six, seven].map(|word| core.value_tuple(&[word, unit]));
    let moved = core.value_tuple(&image);
    let expected = core.computation_return(moved);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "three components ride in order and return in source order"
    );
    let [first, second, third] = image;
    let reversed = core.value_tuple(&[third, second, first]);
    let reversed = core.computation_return(reversed);
    assert_eq!(
        normalises_to(&mut core, rode, reversed),
        CertificateEquality::Different,
        "the components are read off their binds in source order"
    );
}

#[test]
fn a_stuck_part_holds_the_parts_after_it()
{
    let mut core = CoreArena::new();
    let five = literal(&mut core, Word::Five);
    let six = literal(&mut core, Word::Six);
    let text = text_type(&mut core);
    let unit_type = core.value_type_unit();
    let identity = decoded(&mut core);
    let flow = stuck(&mut core, ConstantIndex::from(0_usize));
    let held = core.computation_ride(identity, flow, five);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());

    let product = core.value_type_product(&[identity, text]);
    let pair = core.value_tuple(&[five, six]);
    let rode = core.computation_ride(product, flow, pair);
    let tuple = core.value_tuple(&[bound, six]);
    let tuple = core.computation_return(tuple);
    let expected = core.computation_bind(held, tuple);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a product motive binds its stuck first component before the second"
    );

    let sum = core.value_type_sum(&[identity, unit_type]);
    let injected = core.value_injection(Side::Left.into(), five);
    let rode = core.computation_ride(sum, flow, injected);
    let injection = core.value_injection(Side::Left.into(), bound);
    let injection = core.computation_return(injection);
    let expected = core.computation_bind(held, injection);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a sum motive binds its stuck payload into the injection"
    );

    let list = core.value_type_list(identity);
    let nil = core.value_list_nil();
    let cell = core.value_list_cons(five, nil);
    let rode = core.computation_ride(list, flow, cell);
    let rebuilt = core.value_list_cons(bound, nil);
    let rebuilt = core.computation_return(rebuilt);
    let expected = core.computation_bind(held, rebuilt);
    assert_eq!(
        normalises_to(&mut core, rode, expected),
        CertificateEquality::Equal,
        "a list motive binds its stuck head before its tail"
    );
    let standing = core.value_returned(held);
    let standing = core.value_list_cons(standing, nil);
    let standing = core.computation_return(standing);
    assert_eq!(
        normalises_to(&mut core, rode, standing),
        CertificateEquality::Different,
        "the stuck head does not stand for what it returns"
    );
}
