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
    let case = arena.computation_data_case(
        scrutinee,
        result,
        vec![branch],
        [1_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
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

/// Whether the interfaced atom's interface states its law.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Law
{
    /// The law `((), ())` is stated.
    Stated,
    /// The interface states the relation and reflexivity alone.
    Unstated,
}

/// An atom over `Unit` related by `Unit` and reflexive by `()`, its law
/// `((), ())` declared and stated when `law` says so; two points inside its
/// seal; past it the relation's evidence `()` between them, and a bystander.
///
/// # Specification
/// - requires: nothing.
/// - ensures: eight items at ascending positions, the atom fourth.
/// - panics: the positions do not ascend.
///
/// # Adequacy
/// - hypothesis: L3 — an unedited interface is adopted with its readers, and
///   dropping its law re-judges the atom and every reader of it.
/// - witness: `tests::native_formers::an_atom_interface_persists_and_an_edit_to_it_reaches_every_reader`
#[spec(ensures: |ret| ret.items().len() == 8)]
fn interfaced_atom(law: Law) -> Program
{
    use gandr_core_checker::AbstractType;
    use gandr_core_checker::AtomInterface;
    use gandr_core_checker::ComponentOrdinal;
    use gandr_core_checker::SealSite;
    use gandr_core_checker::SealingSite;
    use gandr_kernel_term::SealExtent;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let one = arena.value_unit();
    let var = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let thunk = |arena: &mut CoreArena, result: ValueId, binders: u8| {
        let mut body = arena.computation_return(result);
        for _ in 0_u8 .. binders {
            body = arena.computation_lambda(body);
        }
        arena.value_thunk(body)
    };
    let relation = arena.value_constant(ConstantIndex::from(0_usize));
    let reflexivity = arena.value_constant(ConstantIndex::from(1_usize));
    // `El(⟨relation left right⟩)`.
    let related = |arena: &mut CoreArena, left: ValueId, right: ValueId| {
        let forced = arena.computation_force(relation);
        let applied = arena.computation_application(forced, left);
        let applied = arena.computation_application(applied, right);
        let code = arena.value_returned(applied);
        arena.value_type_element(code, Level::zero())
    };
    // `relation : U(Unit → Unit → F U₀) = λ λ return ⌜Unit⌝`.
    let codes = arena.comp_type_returner(small);
    let inner = arena.comp_type_arrow(unit, codes);
    let outer = arena.comp_type_arrow(unit, inner);
    let relations = arena.value_type_thunk(outer);
    let unit_code = arena.value_quote(unit);
    let relation_body = thunk(&mut arena, unit_code, 2);
    // `reflexivity : U(Π (x : Unit). F El(⟨relation x x⟩)) = λ return ()`.
    let element = var(&mut arena, 0);
    let diagonal = related(&mut arena, element, element);
    let witnessed = arena.comp_type_returner(diagonal);
    let reflexive = arena.comp_type_pi(unit, witnessed);
    let reflexive = arena.value_type_thunk(reflexive);
    let reflexivity_body = thunk(&mut arena, one, 1);
    // `law : U(Π (a b : Unit). Π (r : El(⟨relation a b⟩)). F Path(Σ (y :
    // Unit). El(⟨relation a y⟩), (b, r), (a, ⟨reflexivity a⟩))) = λ λ λ
    // return ((), ())`.
    let (start, end) = (var(&mut arena, 3), var(&mut arena, 0));
    let singleton = related(&mut arena, start, end);
    let pairs = arena.value_type_sigma(unit, singleton);
    let (start, other, evidence) = (var(&mut arena, 2), var(&mut arena, 1), var(&mut arena, 0));
    let source = arena.value_tuple(&[other, evidence]);
    let forced = arena.computation_force(reflexivity);
    let reflexive_start = arena.computation_application(forced, start);
    let reflexive_start = arena.value_returned(reflexive_start);
    let centre = arena.value_tuple(&[start, reflexive_start]);
    let contracted = arena.value_type_path(pairs, source, centre);
    let returns = arena.comp_type_returner(contracted);
    let (start, other) = (var(&mut arena, 1), var(&mut arena, 0));
    let between = related(&mut arena, start, other);
    let over_evidence = arena.comp_type_pi(between, returns);
    let over_other = arena.comp_type_pi(unit, over_evidence);
    let over_start = arena.comp_type_pi(unit, over_other);
    let lawful = arena.value_type_thunk(over_start);
    let contraction = arena.value_tuple(&[one, one]);
    let law_body = thunk(&mut arena, contraction, 3);
    let interface = AtomInterface::new(relation, reflexivity);
    let interface = match law {
        Law::Stated => interface.lawful(arena.value_constant(ConstantIndex::from(2_usize))),
        Law::Unstated => interface,
    };
    let atom = arena.value_type_abstract(ConstantIndex::from(3_usize));
    let (first, second) = (
        arena.value_constant(ConstantIndex::from(4_usize)),
        arena.value_constant(ConstantIndex::from(5_usize)),
    );
    let identity = arena.value_type_path(atom, first, second);
    let value = |position: usize, declared, body| {
        Declaration::new(
            ConstantIndex::from(position),
            Maybe::Present(declared),
            Maybe::Present(body),
            OriginToken::from(position),
        )
    };
    Program::new(arena, vec![
        Item::new(ItemKey::from("related"), value(0, relations, relation_body)),
        Item::new(
            ItemKey::from("reflexive"),
            value(1, reflexive, reflexivity_body),
        ),
        Item::new(ItemKey::from("law"), value(2, lawful, law_body)),
        Item::new(
            ItemKey::from("Point.T"),
            Declaration::abstract_type(
                ConstantIndex::from(3_usize),
                AbstractType::new(
                    small,
                    unit,
                    SealExtent::from(2_usize),
                    SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize)),
                )
                .interfaced(interface),
                OriginToken::from(3_usize),
            ),
        ),
        Item::new(ItemKey::from("Point.first"), value(4, atom, one)),
        Item::new(ItemKey::from("Point.second"), value(5, atom, one)),
        Item::new(ItemKey::from("client"), value(6, identity, one)),
        Item::new(ItemKey::from("bystander"), value(7, unit, one)),
    ])
    .expect("fixture positions ascend")
}

#[test]
fn an_atom_interface_persists_and_an_edit_to_it_reaches_every_reader()
{
    let original = check_program(&mut interfaced_atom(Law::Stated), CheckBudget::DEFAULT)
        .expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    let typings: Vec<&Typing> = checkpoints
        .items()
        .iter()
        .map(gandr_core_incremental::ItemCheckpoint::typing)
        .collect();
    assert!(
        matches!(typings.as_slice(), [
            Typing::Checked { .. },
            Typing::Checked { .. },
            Typing::Checked { .. },
            Typing::Data,
            Typing::Checked { .. },
            Typing::Checked { .. },
            Typing::Checked { .. },
            Typing::Checked { .. },
        ]),
        "the interface checks and the relation's evidence is an identity: {typings:?}"
    );
    let encoded = encode_checkpoints(checkpoints).expect("an interfaced atom persists");
    let restored = decode_checkpoints(&encoded).expect("its interface decodes");
    assert_eq!(&restored, checkpoints);
    let unchanged = resume_from(&restored, &mut interfaced_atom(Law::Stated))
        .expect("the restored atom can be adopted");
    assert!(
        unchanged
            .adoptions()
            .iter()
            .all(|adoption| *adoption == Adoption::Adopted),
        "unedited, the atom is adopted with its readers"
    );
    let changed = resume_from(&restored, &mut interfaced_atom(Law::Unstated))
        .expect("the edited interface is checked");
    let fresh = check_program(&mut interfaced_atom(Law::Unstated), CheckBudget::DEFAULT)
        .expect("fresh checking succeeds");
    assert_eq!(
        changed.checkpoints(),
        fresh.checkpoints(),
        "incremental equals batch"
    );
    assert_eq!(
        changed.adoptions(),
        [
            Adoption::Adopted,
            Adoption::Adopted,
            Adoption::Adopted,
            Adoption::Judged,
            Adoption::Judged,
            Adoption::Judged,
            Adoption::Judged,
            Adoption::Adopted,
        ],
        "dropping the law reaches the atom and its readers, not its members or the bystander"
    );
    assert!(
        matches!(
            changed.checkpoints().items()[6].typing(),
            Typing::Refused(_)
        ),
        "without its law the relation's evidence is no identity"
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

/// The swap of the booleans, the equivalence it is with itself, and under the
/// item key `last` a product of reflexivity at the unit beside that
/// equivalence, read through its constant.
///
/// # Specification
/// - ensures: three signed declarations; the product reads the equivalence's
///   decision through the constant that names it.
/// - panics: only if the ordered fixture is rejected by the program container.
///
/// # Adequacy
/// - hypothesis: L3 — the product checks freshly and, judged again under a new
///   key, after the equivalence resumes.
/// - witness: `tests::native_formers::an_adopted_equivalence_keeps_its_decision_for_a_later_product_1752`
#[spec(ensures: |ret| ret.items().len() == 3)]
fn equivalences(last: ItemKey) -> Program
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit, unit]);
    let returner = arena.comp_type_returner(boolean);
    let arrow = arena.comp_type_arrow(boolean, returner);
    let translator = arena.value_type_thunk(arrow);
    let swap = tabulate(
        &mut arena,
        &Table::new([1_usize, 0].into_iter().map(ElementIndex::from).collect()),
    );
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let identity = |arena: &mut CoreArena, code| {
        let code = arena.value_quote(code);
        arena.value_type_path(universe, code, code)
    };
    let flipping = identity(&mut arena, boolean);
    let pair = arena.value_type_product(&[unit, boolean]);
    let pairing = identity(&mut arena, pair);
    let swapped = arena.value_constant(ConstantIndex::from(0_usize));
    let equivalence = arena.value_equiv(swapped, swapped);
    let unit_code = arena.value_quote(unit);
    let here = arena.value_here(unit_code);
    let named = arena.value_constant(ConstantIndex::from(1_usize));
    let paired = arena.value_path_product(here, named);
    let items = [
        (ItemKey::from("swap"), translator, swap),
        (ItemKey::from("flipped"), flipping, equivalence),
        (last, pairing, paired),
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
fn an_adopted_equivalence_keeps_its_decision_for_a_later_product_1752()
{
    let original = check_program(
        &mut equivalences(ItemKey::from("paired")),
        CheckBudget::DEFAULT,
    )
    .expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    assert!(
        checkpoints
            .items()
            .iter()
            .all(|item| matches!(item.typing(), Typing::Checked { .. })),
        "the swap, its equivalence and the product check: {checkpoints:?}"
    );
    let renamed = resume_from(checkpoints, &mut equivalences(ItemKey::from("again")))
        .expect("the equivalence resumes under a renamed product");
    let fresh = check_program(
        &mut equivalences(ItemKey::from("again")),
        CheckBudget::DEFAULT,
    )
    .expect("fresh checking succeeds");
    assert_eq!(
        renamed.checkpoints(),
        fresh.checkpoints(),
        "a product after a resumed equivalence reads its decision, as a fresh check does"
    );
    assert_eq!(
        renamed.adoptions(),
        [Adoption::Adopted, Adoption::Judged, Adoption::Judged],
        "an equivalence is judged again for its decision; the renamed item has no checkpoint"
    );
}

/// The order a stream declares its observations in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Observed
{
    /// `head` before `tail`.
    HeadFirst,
    /// `tail` before `head`.
    TailFirst,
}

/// A stream, the stream of units, a reader of its second element through its
/// observations, and a bystander.
///
/// # Specification
/// - ensures: the first item declares the stream, its observations in the order
///   `observed` names.
/// - panics: only if the ordered fixture is rejected by the program container.
///
/// # Adequacy
/// - hypothesis: L3 — the reader names no codata type in its own content, so
///   only its consultation of the stream's signature can make it judged again.
/// - witness: `tests::native_formers::a_codata_reader_is_judged_afresh`
#[spec(ensures: |ret| ret.items().len() == 4)]
fn streams(observed: Observed) -> Program
{
    let mut arena = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    let parameter_kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(parameter, Level::zero());
    let head = arena.comp_type_returner(element);
    let tail = arena.comp_type_codata(family, vec![parameter]);
    let observations = match observed {
        Observed::HeadFirst => vec![head, tail],
        Observed::TailFirst => vec![tail, head],
    };
    let stream = Declaration::codata(
        family,
        Arc::new(gandr_core_term::CodataSignature::new(
            vec![parameter_kind],
            observations,
            kind,
        )),
        OriginToken::from(0_usize),
    );
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let units = arena.comp_type_codata(family, vec![unit_code]);
    let units = arena.value_type_thunk(units);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let own = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(own);
    let pair = arena.computation_with(&[returned, forced]);
    let fixpoint = arena.computation_fixpoint(pair, gandr_kernel_term::FixpointEvidence::Partial);
    let ones = arena.value_thunk(fixpoint);
    let ones_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(ones_constant);
    let rest = arena.computation_project(gandr_kernel_term::Component::from(1_usize), forced);
    let second = arena.computation_project(gandr_kernel_term::Component::from(0_usize), rest);
    let second = arena.value_thunk(second);
    let returner = arena.comp_type_returner(unit_type);
    let returner = arena.value_type_thunk(returner);
    let definition = |position: usize, declared, body| {
        Declaration::new(
            ConstantIndex::from(position),
            Maybe::Present(declared),
            Maybe::Present(body),
            OriginToken::from(position),
        )
    };
    Program::new(arena, vec![
        Item::new(ItemKey::from("Stream"), stream),
        Item::new(ItemKey::from("ones"), definition(1, units, ones)),
        Item::new(ItemKey::from("second"), definition(2, returner, second)),
        Item::new(ItemKey::from("unit"), definition(3, unit_type, unit)),
    ])
    .expect("fixture positions ascend")
}

#[test]
fn a_codata_reader_is_judged_afresh()
{
    let original = check_program(&mut streams(Observed::HeadFirst), CheckBudget::DEFAULT)
        .expect("the initial pass succeeds");
    let checkpoints = original.checkpoints();
    assert_eq!(checkpoints.items()[0].typing(), &Typing::Data);
    for item in &checkpoints.items()[1 ..] {
        assert!(
            matches!(item.typing(), Typing::Checked { .. }),
            "{:?}",
            item.typing()
        );
    }
    assert!(
        checkpoints.items()[2]
            .support()
            .iter()
            .any(|answered| matches!(answered.answer(), Answer::Codata)),
        "the reader consulted the stream's signature"
    );
    assert_eq!(
        encode_checkpoints(checkpoints).err(),
        Some(
            gandr_core_incremental::CheckpointStoreError::UnsupportedPersistence(
                gandr_core_incremental::UnsupportedPersistence::Codata
            )
        ),
        "a codata signature has no content form to persist"
    );
    let unchanged =
        resume_from(checkpoints, &mut streams(Observed::HeadFirst)).expect("the program resumes");
    assert_eq!(unchanged.checkpoints(), checkpoints);
    assert_eq!(
        unchanged.adoptions(),
        [
            Adoption::Judged,
            Adoption::Judged,
            Adoption::Judged,
            Adoption::Adopted
        ],
        "the stream and every item reading it are judged; the bystander is adopted"
    );
    let swapped =
        resume_from(checkpoints, &mut streams(Observed::TailFirst)).expect("the program resumes");
    let fresh = check_program(&mut streams(Observed::TailFirst), CheckBudget::DEFAULT)
        .expect("fresh checking succeeds");
    assert_eq!(swapped.checkpoints(), fresh.checkpoints());
    assert!(
        matches!(
            swapped.checkpoints().items()[2].typing(),
            Typing::Refused(_)
        ),
        "the reader of swapped observations is refused: {:?}",
        swapped.checkpoints().items()[2].typing()
    );
}
