//! Native declaration schemas remain complete across persistence and reuse.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::DeclarationContent;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_checker::ua::StratumDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_core_checker::ua::tabulate;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::Answer;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::Program;
use gandr_core_incremental::Refusal;
use gandr_core_incremental::Typing;
use gandr_core_incremental::check_program;
use gandr_core_incremental::decode_checkpoints;
use gandr_core_incremental::encode_checkpoints;
use gandr_core_incremental::resume_from;
use gandr_core_term::Component;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::ua::Description;
use gandr_core_term::ua::Generator;
use gandr_core_term::ua::Sides;
use gandr_core_term::ua::Stratum;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_theory_levitation::Name;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Table;
use quenchant_shape::shape::Maybe;

/// Whether the constructor retains its record field.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Schema
{
    /// One record field.
    Record,
    /// The same nominal kind, with a nullary constructor instead.
    Nullary,
}

/// Build an unchanged reader of a changeable nominal constructor table.
///
/// # Specification
/// - ensures: the first declaration retains one parameter and one constructor;
///   its field arity follows the selected schema.
/// - panics: only if the ordered fixture is rejected by the program container.
///
/// # Adequacy
/// - hypothesis: L3 — changing the field table while preserving the kind must
///   invalidate a previously successful introduction, including after decoding.
/// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
#[spec(ensures: |ret| ret.items().first().is_some_and(|item| matches!(item.declaration().content(), DeclarationContent::Data(signature) if signature.parameters().len() == 1 && signature.constructors().len() == 1 && signature.constructors().first().is_some_and(|fields| fields.len() == usize::from(schema == Schema::Record)))))]
fn program(schema: Schema) -> Program
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let record_type = arena.value_type_record(BTreeMap::from([
        (FieldLabel::from(String::from("x")), unit_type),
        (FieldLabel::from(String::from("y")), unit_type),
    ]));
    let fields = match schema {
        Schema::Record => vec![record_type],
        Schema::Nullary => vec![],
    };
    let data = Declaration::data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![unit_type], vec![fields], kind).into(),
        OriginToken::from(0_usize),
    );
    let datatype = arena.value_type_data(ConstantIndex::from(0_usize), vec![unit]);
    let record = arena.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("x")), unit),
        (FieldLabel::from(String::from("y")), unit),
    ]));
    let constructor =
        arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![record]);
    let value = Declaration::new(
        ConstantIndex::from(1_usize),
        Maybe::Present(datatype),
        Maybe::Present(constructor),
        OriginToken::from(1_usize),
    );
    let result = arena.comp_type_returner(unit_type);
    let suspended = arena.value_type_thunk(result);
    let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let projection =
        arena.computation_record_projection(field, FieldLabel::from(String::from("x")));
    let branch = arena.computation_lambda(projection);
    let scrutinee = arena.value_constant(ConstantIndex::from(1_usize));
    let case = arena.computation_data_case(scrutinee, result, vec![branch]);
    let body = arena.value_thunk(case);
    let eliminate = Declaration::new(
        ConstantIndex::from(2_usize),
        Maybe::Present(suspended),
        Maybe::Present(body),
        OriginToken::from(2_usize),
    );
    let missing = arena.computation_record_projection(record, FieldLabel::from(String::from("z")));
    let missing = arena.value_thunk(missing);
    let absent = Declaration::new(
        ConstantIndex::from(3_usize),
        Maybe::Present(suspended),
        Maybe::Present(missing),
        OriginToken::from(3_usize),
    );
    // The same identity answers the native-table query but not a value query.
    let not_a_value = arena.value_constant(ConstantIndex::from(0_usize));
    let misuse = Declaration::new(
        ConstantIndex::from(4_usize),
        Maybe::Present(datatype),
        Maybe::Present(not_a_value),
        OriginToken::from(4_usize),
    );
    let pair = arena.value_tuple(&[unit, record]);
    let first = arena.computation_tuple_projection(pair, Component::from(0_usize));
    let first = arena.value_thunk(first);
    let tuple_projection = Declaration::new(
        ConstantIndex::from(5_usize),
        Maybe::Present(suspended),
        Maybe::Present(first),
        OriginToken::from(5_usize),
    );
    let past = arena.computation_tuple_projection(pair, Component::from(2_usize));
    let past = arena.value_thunk(past);
    let absent_component = Declaration::new(
        ConstantIndex::from(6_usize),
        Maybe::Present(suspended),
        Maybe::Present(past),
        OriginToken::from(6_usize),
    );
    Program::new(arena, vec![
        Item::new(ItemKey::from("Box"), data),
        Item::new(ItemKey::from("value"), value),
        Item::new(ItemKey::from("project"), eliminate),
        Item::new(ItemKey::from("absent"), absent),
        Item::new(ItemKey::from("not_a_value"), misuse),
        Item::new(ItemKey::from("first"), tuple_projection),
        Item::new(ItemKey::from("past"), absent_component),
    ])
    .expect("fixture positions ascend")
}

#[test]
fn native_checkpoint_round_trip_and_signature_invalidation()
{
    let original = check_program(&mut program(Schema::Record), CheckBudget::DEFAULT)
        .expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    assert_eq!(checkpoints.items()[0].typing(), &Typing::Data);
    assert!(matches!(
        checkpoints.items()[1].typing(),
        Typing::Checked { .. }
    ));
    assert!(matches!(
        checkpoints.items()[2].typing(),
        Typing::Checked { .. }
    ));
    assert!(matches!(
        checkpoints.items()[3].typing(),
        Typing::Refused(Refusal::AbsentRecordField(_))
    ));
    assert!(matches!(
        checkpoints.items()[4].typing(),
        Typing::Refused(Refusal::UnknownConstant { .. })
    ));
    assert!(matches!(
        checkpoints.items()[5].typing(),
        Typing::Checked { .. }
    ));
    assert!(matches!(
        checkpoints.items()[6].typing(),
        Typing::Refused(Refusal::AbsentTupleComponent(_))
    ));
    let dual = checkpoints.items()[4].support();
    assert_eq!(
        dual.len(),
        2,
        "native presence and value absence must not coalesce"
    );
    assert_eq!(dual[0].reference(), dual[1].reference());
    assert!(matches!(dual[0].answer(), Answer::Untyped));
    assert!(matches!(dual[1].answer(), Answer::Data(Some(_))));

    let encoded = encode_checkpoints(checkpoints).expect("native content and support persist");
    let restored = decode_checkpoints(&encoded).expect("the native schema decodes");
    assert_eq!(&restored, checkpoints);
    let unchanged = resume_from(&restored, &mut program(Schema::Record))
        .expect("restored native declarations can be adopted");
    assert_eq!(unchanged.checkpoints(), checkpoints);
    assert!(
        unchanged
            .adoptions()
            .iter()
            .all(|adoption| *adoption == Adoption::Adopted)
    );

    let changed = resume_from(&restored, &mut program(Schema::Nullary))
        .expect("the changed signature is checked");
    let fresh = check_program(&mut program(Schema::Nullary), CheckBudget::DEFAULT)
        .expect("fresh checking succeeds");
    assert_eq!(changed.checkpoints(), fresh.checkpoints());
    assert!(matches!(
        changed.checkpoints().items()[1].typing(),
        Typing::Refused(Refusal::ConstructorArity(_))
    ));
    assert_eq!(changed.adoptions()[1], Adoption::Judged);
    let refused = encode_checkpoints(changed.checkpoints()).expect("native refusals persist");
    assert_eq!(
        decode_checkpoints(&refused).expect("native refusals decode"),
        *changed.checkpoints()
    );
}

/// The magma's description: `mul : 2 → 1`, then `one : 0 → 1`.
///
/// # Specification
/// trivial.
fn magma() -> Description
{
    let generator = |label: &str, inputs: usize| Generator {
        label: FieldLabel::from(String::from(label)),
        profile: Profile {
            inputs: PortCount::from(inputs),
            outputs: PortCount::from(1_usize),
        },
    };
    Description {
        name: Name::from("Magma"),
        generators: Box::from([generator("mul", 2), generator("one", 0)]),
    }
}

/// Three statements of univalence between the magma and itself: the swap of
/// its binary generator at degree one, the same at a degree no shape of the
/// catalogue reaches, and a backward table that does not invert the forward
/// one.
///
/// # Specification
/// - ensures: three unsigned declarations, each a `ua` statement.
/// - panics: only if the ordered fixture is rejected by the program container.
///
/// # Adequacy
/// - hypothesis: L3 — an accepted statement and two refused ones persist and
///   resume as a fresh check gives them.
/// - witness: `tests::native_formers::a_univalence_statement_round_trips_with_its_descriptions`
#[spec(ensures: |ret| ret.items().len() == 3)]
fn univalence() -> Program
{
    let mut arena = CoreArena::new();
    let [swap, same, keep] = [&[1_usize, 0][..], &[0, 1], &[0]].map(|images| {
        tabulate(
            &mut arena,
            &Table::new(images.iter().copied().map(ElementIndex::from).collect()),
        )
    });
    let sides = Arc::new(Sides {
        source: magma(),
        target: magma(),
    });
    let mut statement = |degree: usize, backward: ValueId| {
        let [forward, backward] = [swap, backward].map(|binary| {
            arena.value_record(BTreeMap::from([
                (FieldLabel::from(String::from("mul")), binary),
                (FieldLabel::from(String::from("one")), keep),
            ]))
        });
        arena.value_ua(
            Stratum {
                degree: Degree::from(degree),
                bound: ShapeSize::from(4_usize),
            },
            Arc::clone(&sides),
            forward,
            backward,
        )
    };
    let statements = [statement(1, swap), statement(5, swap), statement(1, same)];
    let items = ["opposite", "above", "lopsided"]
        .into_iter()
        .zip(statements)
        .enumerate()
        .map(|(position, (key, body))| {
            Item::new(
                ItemKey::from(key),
                Declaration::new(
                    ConstantIndex::from(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                    OriginToken::from(position),
                ),
            )
        })
        .collect();
    Program::new(arena, items).expect("fixture positions ascend")
}

#[test]
fn a_univalence_statement_round_trips_with_its_descriptions()
{
    let original =
        check_program(&mut univalence(), CheckBudget::DEFAULT).expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    assert!(
        matches!(checkpoints.items()[0].typing(), Typing::Synthesised { .. }),
        "the swap derives its path"
    );
    assert!(matches!(
        checkpoints.items()[1].typing(),
        Typing::Refused(Refusal::UaUncertified {
            stratum: StratumDefect::Degree { degree },
            ..
        }) if *degree == Degree::from(5_usize)
    ));
    assert!(matches!(
        checkpoints.items()[2].typing(),
        Typing::Refused(Refusal::UaInequivalent {
            defect: UaDefect::NotInverse { .. },
            ..
        })
    ));
    let encoded = encode_checkpoints(checkpoints).expect("the statements persist");
    let restored = decode_checkpoints(&encoded).expect("the statements decode");
    assert_eq!(
        &restored, checkpoints,
        "the stratum, both descriptions and every refusal survive the codec"
    );
    let resumed =
        resume_from(&restored, &mut univalence()).expect("restored statements can be resumed");
    assert_eq!(resumed.checkpoints(), checkpoints);
    assert_eq!(
        resumed.adoptions(),
        [Adoption::Judged, Adoption::Adopted, Adoption::Adopted],
        "an accepted statement is judged again for its derived path; a refused one is adopted"
    );
}

/// Two products of reflexivity at the unit written apart — `here` twice, and
/// `here` beside the native reflexivity — and a path identifying them under
/// the item key `last`.
///
/// # Specification
/// - ensures: three signed declarations; the two products agree only once each
///   is elaborated to its native path.
/// - panics: only if the ordered fixture is rejected by the program container.
///
/// # Adequacy
/// - hypothesis: L3 — the identification checks freshly and after the products
///   resume, and is judged again under a new key.
/// - witness: `tests::native_formers::a_path_product_resumes_to_its_native_path`
#[spec(ensures: |ret| ret.items().len() == 3)]
fn products(last: ItemKey) -> Program
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let code = arena.value_quote(unit);
    let here = arena.value_here(code);
    let native = arena.value_path_refl(code);
    let written = arena.value_path_product(here, here);
    let mixed = arena.value_path_product(here, native);
    let pair = arena.value_type_product(&[unit, unit]);
    let pair = arena.value_quote(pair);
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let identity = arena.value_type_path(universe, pair, pair);
    let first = arena.value_constant(ConstantIndex::from(0_usize));
    let second = arena.value_constant(ConstantIndex::from(1_usize));
    let same = arena.value_type_path(identity, first, second);
    let reflexive = arena.value_here(first);
    let items = [
        (ItemKey::from("by_hand"), identity, written),
        (ItemKey::from("mixed"), identity, mixed),
        (last, same, reflexive),
    ]
    .into_iter()
    .enumerate()
    .map(|(position, (key, declared, body))| {
        Item::new(
            key,
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Present(declared),
                Maybe::Present(body),
                OriginToken::from(position),
            ),
        )
    })
    .collect();
    Program::new(arena, items).expect("fixture positions ascend")
}

#[test]
fn a_path_product_resumes_to_its_native_path()
{
    let original = check_program(&mut products(ItemKey::from("same")), CheckBudget::DEFAULT)
        .expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    assert!(
        checkpoints
            .items()
            .iter()
            .all(|item| matches!(item.typing(), Typing::Checked { .. })),
        "the products agree once elaborated: {checkpoints:?}"
    );
    let renamed = resume_from(checkpoints, &mut products(ItemKey::from("again")))
        .expect("the products resume under a renamed identification");
    let fresh = check_program(&mut products(ItemKey::from("again")), CheckBudget::DEFAULT)
        .expect("fresh checking succeeds");
    assert_eq!(
        renamed.checkpoints(),
        fresh.checkpoints(),
        "a judgement after resumed products reads their native paths, as a fresh check does"
    );
    assert_eq!(
        renamed.adoptions(),
        [Adoption::Judged, Adoption::Judged, Adoption::Judged],
        "a product is judged again for its native path; the renamed item has no checkpoint"
    );
}
