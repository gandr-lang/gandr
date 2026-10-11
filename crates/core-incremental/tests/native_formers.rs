//! Native declaration schemas remain complete across persistence and reuse.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::DeclarationContent;
use gandr_core_checker::OriginToken;
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
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
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
        | Schema::Record => vec![record_type],
        | Schema::Nullary => vec![],
    };
    let data = Declaration::data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![unit_type], vec![fields], kind),
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
    Program::new(arena, vec![
        Item::new(ItemKey::from("Box"), data),
        Item::new(ItemKey::from("value"), value),
        Item::new(ItemKey::from("project"), eliminate),
        Item::new(ItemKey::from("absent"), absent),
        Item::new(ItemKey::from("not_a_value"), misuse),
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
