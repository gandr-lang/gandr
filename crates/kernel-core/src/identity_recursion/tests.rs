//! Semantic witnesses for the closed-code identity and relation experiment.

use alloc::string::String;

use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::CaseIndex;
use super::Domain;
use super::Fiber;
use super::Index;
use super::Inhabitation;
use super::Mode;
use super::Relation;
use super::RelationError;
use super::Transport;
use super::check_value;
use super::interpret;
use crate::check::check_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::error::KernelError;
use crate::path_universe::Path;
use crate::path_universe::Paths;
use crate::path_universe::RoundTrips;
use crate::replay::ReplayBudget;

/// A scalar fixture with two observably different canonical inhabitants.
struct Scalars
{
    /// The string base type.
    ty: ValueTypeId,
    /// Its code.
    code: ValueId,
    /// The first literal.
    first: ValueId,
    /// The second literal.
    second: ValueId,
}

/// Construct canonical strings, without reading the relation implementation.
///
/// # Specification
/// trivial.
fn scalars(arena: &mut TermArena) -> Scalars
{
    let ty = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(ty);
    let first = arena.value_literal(Literal::Text(StringLiteral::new(String::from("first"))));
    let second = arena.value_literal(Literal::Text(StringLiteral::new(String::from("second"))));
    Scalars {
        ty,
        code,
        first,
        second,
    }
}

/// The shared consumer of the code fold, without any per-code branch.
///
/// # Specification
/// trivial.
fn relation(
    arena: &TermArena,
    mode: Mode,
    code: ValueId,
) -> Relation
{
    interpret(arena, mode, Domain::Elements(code))
        .expect("code forms")
        .elements()
        .expect("element relation")
}

/// Compare a computed relation fibre against an independently written native
/// type.
///
/// # Specification
/// trivial.
fn assert_fiber(
    arena: &mut TermArena,
    relation: &Relation,
    left: ValueId,
    right: ValueId,
    expected: ValueTypeId,
)
{
    let fiber = relation
        .fiber(arena, &[], left, right)
        .expect("typed indices");
    let actual = fiber.native(arena).expect("canonical fibre computes");
    assert_eq!(
        convertible_value_types(arena, expected, actual),
        Convertibility::Convertible
    );
}

#[test]
fn both_modes_compute_all_element_clauses()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let empty = arena.value_type_empty();
    let unit_code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let scalars = scalars(&mut arena);
    let sum = arena.value_type_sum(scalars.ty, unit_type);
    let sum_code = arena.value_quote(sum);
    let left = arena.value_injection(Side::Left, scalars.first);
    let unequal_left = arena.value_injection(Side::Left, scalars.second);
    let right = arena.value_injection(Side::Right, unit);
    let product = arena.value_type_product(sum, scalars.ty);
    let product_code = arena.value_quote(product);
    let pair = arena.value_pair(left, scalars.first);
    let changed_first = arena.value_pair(right, scalars.first);
    let changed_second = arena.value_pair(left, scalars.second);
    let units = arena.value_type_product(unit_type, unit_type);
    let empty_first = arena.value_type_product(empty, unit_type);
    let empty_second = arena.value_type_product(unit_type, empty);
    for mode in [Mode::Identity, Mode::Bridge] {
        for (code, a, b, expected) in [
            (unit_code, unit, unit, unit_type),
            (scalars.code, scalars.first, scalars.first, unit_type),
            (scalars.code, scalars.first, scalars.second, empty),
            (sum_code, left, left, unit_type),
            (sum_code, right, right, unit_type),
            (sum_code, left, unequal_left, empty),
            (sum_code, left, right, empty),
            (sum_code, right, left, empty),
            (product_code, pair, pair, units),
            (product_code, pair, changed_first, empty_first),
            (product_code, pair, changed_second, empty_second),
        ] {
            let relation = relation(&arena, mode, code);
            assert_fiber(&mut arena, &relation, a, b, expected);
        }
    }
}

#[test]
fn neutral_fibres_do_not_decide_equality()
{
    let mut arena = TermArena::new();
    let scalars = scalars(&mut arena);
    let x = arena.value_variable(DeBruijnIndex::from(1_u32));
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    let product = arena.value_type_product(scalars.ty, scalars.ty);
    let product_code = arena.value_quote(product);
    let sum = arena.value_type_sum(scalars.ty, scalars.ty);
    let sum_code = arena.value_quote(sum);
    for mode in [Mode::Identity, Mode::Bridge] {
        let base = relation(&arena, mode, scalars.code);
        let fiber = base
            .fiber(&mut arena, &[scalars.ty, scalars.ty], x, y)
            .expect("open relation");
        assert!(matches!(fiber.get(fiber.root()), Ok(Fiber::Discrete(..))));
        assert!(matches!(
            fiber.native(&mut arena),
            Err(RelationError::NeutralFiber)
        ));
        let same = base
            .fiber(&mut arena, &[scalars.ty], y, y)
            .expect("diagonal");
        assert_eq!(same.get(same.root()).expect("root"), Fiber::Unit);
        let bad_context = arena.value_type_unit();
        assert!(matches!(
            base.fiber(&mut arena, &[bad_context], y, y),
            Err(RelationError::Typing(_))
        ));
        let pairs = relation(&arena, mode, product_code);
        let fiber = pairs
            .fiber(&mut arena, &[product, product], x, y)
            .expect("neutral products unfold");
        let Fiber::Product(first, second) = fiber.get(fiber.root()).expect("root")
        else {
            panic!("componentwise relation");
        };
        let Fiber::Discrete(a, b) = fiber.get(first).expect("first")
        else {
            panic!("first base fibre");
        };
        assert!(matches!(fiber.get_index(a), Ok(Index::First(_))));
        assert!(matches!(fiber.get_index(b), Ok(Index::First(_))));
        let Fiber::Discrete(a, b) = fiber.get(second).expect("second")
        else {
            panic!("second base fibre");
        };
        assert!(matches!(fiber.get_index(a), Ok(Index::Second(_))));
        assert!(matches!(fiber.get_index(b), Ok(Index::Second(_))));
        let sums = relation(&arena, mode, sum_code);
        let fiber = sums.fiber(&mut arena, &[sum], y, y).expect("neutral sum");
        assert!(matches!(fiber.get(fiber.root()), Ok(Fiber::Suspended(..))));
    }
}

#[test]
fn reflexivity_and_transport_compute()
{
    let mut arena = TermArena::new();
    let scalars = scalars(&mut arena);
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let unit_code = arena.value_quote(unit_type);
    let sum = arena.value_type_sum(scalars.ty, unit_type);
    let sum_code = arena.value_quote(sum);
    let injection = arena.value_injection(Side::Left, scalars.first);
    let product = arena.value_type_product(sum, scalars.ty);
    let product_code = arena.value_quote(product);
    let pair = arena.value_pair(injection, scalars.second);
    for (code, value) in [
        (unit_code, unit),
        (scalars.code, scalars.first),
        (sum_code, injection),
        (product_code, pair),
    ] {
        let relation = relation(&arena, Mode::Identity, code);
        let identity = relation
            .reflexivity(&mut arena, &[], value)
            .expect("derived diagonal");
        let actual = relation
            .transport(&mut arena, &[], identity, scalars.ty, scalars.second)
            .expect("transport");
        assert_eq!(actual, Transport::Return(scalars.second));
        assert!(matches!(
            relation.transport(&mut arena, &[], identity, scalars.ty, unit),
            Err(RelationError::Typing(_))
        ));
    }
    let x = arena.value_variable(DeBruijnIndex::from(0_u32));
    for (ty, code) in [
        (scalars.ty, scalars.code),
        (sum, sum_code),
        (product, product_code),
    ] {
        let relation = relation(&arena, Mode::Identity, code);
        let identity = relation
            .reflexivity(&mut arena, &[ty], x)
            .expect("open diagonal");
        assert_eq!(
            relation
                .transport(&mut arena, &[ty], identity, ty, x)
                .expect("open transport"),
            Transport::Return(x)
        );
    }
    let units = relation(&arena, Mode::Identity, unit_code);
    let y = arena.value_variable(DeBruijnIndex::from(1_u32));
    let proof = units
        .witness(&mut arena, &[unit_type, unit_type], x, y, unit)
        .expect("total Unit relation");
    assert!(
        matches!(units.transport(&mut arena, &[unit_type, unit_type], proof, scalars.ty, scalars.first), Ok(Transport::Neutral { value, .. }) if value == scalars.first)
    );
}

#[test]
fn product_transport_composes_componentwise()
{
    let mut arena = TermArena::new();
    let scalars = scalars(&mut arena);
    let pair_type = arena.value_type_product(scalars.ty, scalars.ty);
    let code = arena.value_quote(pair_type);
    let x = arena.value_variable(DeBruijnIndex::from(1_u32));
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    let pair = arena.value_pair(x, y);
    let relation = relation(&arena, Mode::Identity, code);
    let first = relation
        .reflexivity(&mut arena, &[scalars.ty, scalars.ty], pair)
        .expect("first identity");
    let second = relation
        .reflexivity(&mut arena, &[scalars.ty, scalars.ty], pair)
        .expect("second identity");
    let composite = relation
        .compose(&mut arena, &[scalars.ty, scalars.ty], first, second)
        .expect("both coordinates compose");
    assert_eq!(
        relation
            .transport(
                &mut arena,
                &[scalars.ty, scalars.ty],
                composite,
                pair_type,
                pair
            )
            .expect("composite transport"),
        Transport::Return(pair)
    );
    let changed = arena.value_pair(y, x);
    let other = relation
        .reflexivity(&mut arena, &[scalars.ty, scalars.ty], changed)
        .expect("other diagonal");
    assert!(matches!(
        relation.compose(&mut arena, &[scalars.ty, scalars.ty], first, other),
        Err(RelationError::Boundary)
    ));
    let fiber = relation
        .fiber(&mut arena, &[scalars.ty, scalars.ty], pair, pair)
        .expect("independent fibre");
    let expected = arena.value_type_unit();
    let expected = arena.value_type_product(expected, expected);
    let native = fiber.native(&mut arena).expect("computed product fibre");
    assert_eq!(
        convertible_value_types(&arena, expected, native),
        Convertibility::Convertible
    );
    let unit_type = arena.value_type_unit();
    let pair_type = arena.value_type_product(unit_type, unit_type);
    let code = arena.value_quote(pair_type);
    let family = interpret(&arena, Mode::Identity, Domain::Elements(code))
        .expect("product interpretation")
        .elements()
        .expect("element relation");
    let x = arena.value_variable(DeBruijnIndex::from(2_u32));
    let y = arena.value_variable(DeBruijnIndex::from(1_u32));
    let z = arena.value_variable(DeBruijnIndex::from(0_u32));
    let left = arena.value_pair(x, x);
    let middle = arena.value_pair(y, y);
    let right = arena.value_pair(z, z);
    let unit = arena.value_unit();
    let proof = arena.value_pair(unit, unit);
    let context = [unit_type, unit_type, unit_type];
    let first = family
        .witness(&mut arena, &context, left, middle, proof)
        .expect("first non-diagonal product identity");
    let second = family
        .witness(&mut arena, &context, middle, right, proof)
        .expect("second non-diagonal product identity");
    let composite = family
        .compose(&mut arena, &context, first, second)
        .expect("componentwise non-diagonal composition");
    let back = family
        .witness(&mut arena, &context, right, left, proof)
        .expect("return identity");
    let loop_identity = family
        .compose(&mut arena, &context, composite, back)
        .expect("composite retains the right endpoint");
    assert_eq!(
        family
            .transport(&mut arena, &context, loop_identity, unit_type, unit)
            .expect("closed loop retains the left endpoint"),
        Transport::Return(unit)
    );
    assert!(matches!(
        family.compose(&mut arena, &context, first, composite),
        Err(RelationError::Boundary)
    ));
}

#[test]
fn identity_evidence_refuses_false_fibres()
{
    let mut arena = TermArena::new();
    let scalars = scalars(&mut arena);
    let relation = relation(&arena, Mode::Identity, scalars.code);
    let unit = arena.value_unit();
    assert!(matches!(
        relation.witness(&mut arena, &[], scalars.first, scalars.second, unit),
        Err(RelationError::Typing(_))
    ));
    let identity = relation
        .reflexivity(&mut arena, &[], scalars.first)
        .expect("first diagonal");
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(unit_type);
    let other = super::tests::relation(&arena, Mode::Identity, code);
    assert!(matches!(
        other.transport(&mut arena, &[], identity, unit_type, unit),
        Err(RelationError::Boundary)
    ));
    let pair_type = arena.value_type_product(scalars.ty, scalars.ty);
    let code = arena.value_quote(pair_type);
    let product = super::tests::relation(&arena, Mode::Identity, code);
    let left = arena.value_pair(scalars.first, scalars.first);
    let right = arena.value_pair(scalars.first, scalars.second);
    let proof = arena.value_pair(unit, unit);
    assert!(matches!(
        product.witness(&mut arena, &[], left, right, proof),
        Err(RelationError::Typing(_))
    ));
}

#[test]
fn universe_bridge_is_an_indexed_relation()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let boolean = arena.value_type_sum(unit_type, unit_type);
    let boolean_code = arena.value_quote(boolean);
    let unit = arena.value_unit();
    let left = arena.value_injection(Side::Left, unit);
    let right = arena.value_injection(Side::Right, unit);
    let empty = arena.value_type_empty();
    let classifier = interpret(&arena, Mode::Bridge, Domain::Codes).expect("universe clause");
    let yes = Relation::constant(&arena, unit_code, unit_code, Inhabitation::Unit)
        .expect("inhabited fibre");
    let no =
        Relation::constant(&arena, unit_code, unit_code, Inhabitation::Empty).expect("empty fibre");
    let relation =
        Relation::cases(&mut arena, CaseIndex::Right, yes, no).expect("code-indexed relation");
    classifier
        .bridge(&arena, unit_code, boolean_code, &relation)
        .expect("Br_U Unit Bool");
    assert_fiber(&mut arena, &relation, unit, left, unit_type);
    assert_fiber(&mut arena, &relation, unit, right, empty);
    assert!(matches!(
        classifier.bridge(&arena, unit_code, unit_code, &relation),
        Err(RelationError::Boundary)
    ));
    assert!(matches!(
        relation.reflexivity(&mut arena, &[], unit),
        Err(RelationError::NonFibrant)
    ));
    let yes =
        Relation::constant(&arena, unit_code, unit_code, Inhabitation::Unit).expect("left family");
    let no = Relation::constant(&arena, unit_code, unit_code, Inhabitation::Empty)
        .expect("right family");
    let relation = Relation::cases(&mut arena, CaseIndex::Left, yes, no).expect("mirror relation");
    classifier
        .bridge(&arena, boolean_code, unit_code, &relation)
        .expect("Br_U Bool Unit");
    assert_fiber(&mut arena, &relation, left, unit, unit_type);
    assert_fiber(&mut arena, &relation, right, unit, empty);
}

#[test]
fn universe_identity_consumes_path_formation()
{
    let mut arena = TermArena::new();
    let ty = arena.value_type_unit();
    let code = arena.value_quote(ty);
    let unit = arena.value_unit();
    let mut paths = Paths::new();
    let refl = paths.push(Path::Refl(code)).expect("path syntax");
    let identity =
        interpret(&arena, Mode::Identity, Domain::Codes).expect("identity universe clause");
    let formed = identity
        .path(&mut arena, &paths, refl, ReplayBudget::from(1000_u64))
        .expect("existing path formation");
    assert_eq!(formed.source, ty);
    assert_eq!(formed.target, ty);
    let bad = paths
        .push(Path::Equiv {
            source: code,
            target: code,
            forward: unit,
            backward: unit,
            round_trips: RoundTrips::default(),
        })
        .expect("raw evidence");
    assert!(matches!(
        identity.path(&mut arena, &paths, bad, ReplayBudget::from(1000_u64)),
        Err(RelationError::Path(_))
    ));
    assert!(matches!(
        identity.elements(),
        Err(RelationError::Classifier)
    ));
}

#[test]
fn abstract_is_an_interface_obstruction()
{
    let mut arena = TermArena::new();
    let atom = arena.value_type_abstract(gandr_kernel_term::ConstantIndex::from(0_usize));
    let code = arena.value_quote(atom);
    let unit = arena.value_type_unit();
    let composite = arena.value_type_product(unit, atom);
    let composite = arena.value_quote(composite);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    for mode in [Mode::Identity, Mode::Bridge] {
        for code in [code, composite] {
            assert!(
                matches!(interpret(&arena, mode, Domain::Elements(code)), Err(RelationError::AbstractInterface(found)) if found == atom)
            );
        }
        assert!(
            matches!(interpret(&arena, mode, Domain::Elements(variable)), Err(RelationError::UnsupportedCode(found)) if found == variable)
        );
    }
}

#[test]
fn empty_elimination_is_native_and_has_no_introduction()
{
    let mut arena = TermArena::new();
    let empty = arena.value_type_empty();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let x = arena.value_variable(DeBruijnIndex::from(0_u32));
    let absurd = arena.computation_absurd(x);

    let body = arena.computation_lambda(absurd);
    let body = arena.value_thunk(body);
    let returns = arena.comp_type_returner(unit_type);
    let arrow = arena.comp_type_arrow(empty, returns);
    let ty = arena.value_type_thunk(arrow);
    check_closed_value(&mut arena, body, ty).expect("Empty -> F Unit");
    let wrong_arrow = arena.comp_type_arrow(unit_type, returns);
    let wrong_type = arena.value_type_thunk(wrong_arrow);
    assert!(matches!(
        check_closed_value(&mut arena, body, wrong_type),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    assert!(matches!(
        check_closed_value(&mut arena, unit, empty),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    let quote = arena.value_quote(empty);
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    check_value(&mut arena, &[], quote, universe).expect("empty type forms at zero");
    assert_eq!(arena.value_type(empty), Some(&ValueType::Empty));
    assert!(
        matches!(interpret(&arena, Mode::Identity, Domain::Elements(quote)), Err(RelationError::UnsupportedType(found)) if found == empty)
    );
    let builder = gandr_kernel_term::DeclarationBuilder::new(&mut arena);
    let declaration = builder.def(gandr_kernel_term::LevelSignature::monomorphic(), ty, body);
    let sequence = [gandr_kernel_term::MarkedDeclaration::new(
        gandr_kernel_term::AdmissionMark::Checked,
        declaration,
    )];
    let bytes = gandr_kernel_term::encode(&arena, &sequence);
    let decoded =
        gandr_kernel_term::decode(bytes.as_image()).expect("native empty syntax round trip");
    let mut decoded_arena = decoded.arena().clone();
    let declaration = decoded
        .declarations()
        .first()
        .expect("declaration")
        .declaration();
    let gandr_kernel_term::DeclarationContent::Def { declared, body } = *declaration.content()
    else {
        panic!("definition retained");
    };
    check_closed_value(&mut decoded_arena, body, declared)
        .expect("decoded empty elimination checks");
}
