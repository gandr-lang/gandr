//! The tests of `encoding` that build their fixtures with the judgement: each
//! one admits through `Environment` or reads through conversion, which stand
//! above the record, so it runs in this crate.

use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::encoding::ContentEncoding;
use crate::encoding::ContentId;
use crate::encoding::ContentTable;
use crate::encoding::RecordName;
use crate::encoding::SupportGoal;
use crate::encoding::Telescope;
use crate::encoding::support_key;

/// Where a naming fixture admits its referent beside the unrelated pair.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReferentOrder
{
    /// The referent, then the pair.
    First,
    /// The pair, then the referent.
    Second,
}

/// Whether a naming fixture's table holds a record before the goal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TableState
{
    /// The table holds nothing before the goal.
    Cold,
    /// The table holds the declared type's goal before the goal.
    Warm,
}

/// Admit `referent` and a pair definition in `order`, then
/// `c : Unit = referent`; return the environment, `c`'s body and `c`'s
/// declared type.
///
/// # Specification
/// - requires: `referent` admits one declaration at the unit type.
/// - ensures: an environment that holds the referent, the pair and `c`, in that
///   order or with the pair first.
/// - provides: the admission-order environments the constant naming cases and
///   the record naming cases read.
/// - fails: never.
/// - panics: when an admission refuses.
/// - executable: none — the cases compare two calls' environments, which no
///   single call's predicate states.
///
/// # Adequacy
/// - hypothesis: L3 — a definition and an axiom referent each admitted before
///   and after an unrelated definition.
/// - witness: `environment::encoding_tests::a_definition_reference_reads_alike_in_either_admission_order`
/// - witness: `environment::encoding_tests::a_goal_takes_one_name_in_either_admission_order_864`
fn reference_environment(
    referent: &dyn Fn(&mut crate::Environment) -> ConstantIndex,
    order: ReferentOrder,
) -> (crate::Environment, ValueId, ValueTypeId)
{
    let mut environment = crate::Environment::new();
    let pair = |environment: &mut crate::Environment| {
        let mut staging = environment.stage();
        let unit = staging.arena().value_type_unit();
        let declared = staging.arena().value_type_product(&[unit, unit]);
        let one = staging.arena().value_unit();
        let body = staging.arena().value_tuple(&[one, one]);
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        environment.add_decl(staged).expect("the pair admits")
    };
    let reached = match order {
        ReferentOrder::First => {
            let reached = referent(&mut environment);
            let _pair = pair(&mut environment);
            reached
        },
        ReferentOrder::Second => {
            let _pair = pair(&mut environment);
            referent(&mut environment)
        },
    };
    let mut staging = environment.stage();
    let declared = staging.arena().value_type_unit();
    let reference = staging.arena().value_constant(reached);
    let staged = staging.def(LevelSignature::monomorphic(), declared, reference);
    let _c = environment.add_decl(staged).expect("the reference admits");
    (environment, reference, declared)
}

/// Admit `referent` and a pair definition in `order`, then
/// `c : Unit = referent`; return the record stream a table told the
/// environment's entries builds for `c`'s body.
///
/// # Specification
/// - requires: `referent` admits one declaration at the unit type.
/// - ensures: the stream of every record `c`'s body reaches, in the order the
///   walk assigns them.
/// - provides: the admission-order fixtures the constant naming cases compare.
/// - fails: never.
/// - panics: when an admission refuses.
/// - executable: none — the cases compare two calls' streams, which no single
///   call's predicate states.
///
/// # Adequacy
/// - hypothesis: L3 — a definition and an axiom referent each admitted before
///   and after an unrelated definition.
/// - witness: `environment::encoding_tests::a_definition_reference_reads_alike_in_either_admission_order`
/// - witness: `environment::encoding_tests::an_axiom_reference_keeps_its_position`
fn reference_stream(
    referent: &dyn Fn(&mut crate::Environment) -> ConstantIndex,
    order: ReferentOrder,
) -> ContentEncoding
{
    let (environment, reference, _declared) = reference_environment(referent, order);
    let mut table = ContentTable::new();
    table.name_constants(environment.entries());
    let _id = gandr_kernel_core_base::fixture::place(
        &mut table,
        environment.arena(),
        AnyNode::Value(reference),
    );
    gandr_kernel_core_base::fixture::stream(&table).clone()
}

/// Admit `referent` and a pair definition in `order`, then
/// `c : Unit = referent`; key the goal that synthesises `c`'s body under
/// `c`'s declared type as its one binder, in a table that names its
/// records. A `warm` table first keys the level of `c`'s declared type,
/// so it numbers the goal later.
///
/// # Specification
/// - requires: `referent` admits one declaration at the unit type.
/// - ensures: the goal's id and its name.
/// - provides: the admission-order fixtures the record naming cases compare.
/// - fails: never.
/// - panics: when an admission refuses, or when the table gives no name.
/// - executable: none — the cases compare two calls' names, which no single
///   call's predicate states.
///
/// # Adequacy
/// - hypothesis: L3 — a definition and an axiom referent each admitted before
///   and after an unrelated definition, in a cold and a warm table.
/// - witness: `environment::encoding_tests::a_goal_takes_one_name_in_either_admission_order_864`
/// - witness: `environment::encoding_tests::a_goal_over_an_axiom_takes_its_position_s_name_864`
fn goal_name(
    referent: &dyn Fn(&mut crate::Environment) -> ConstantIndex,
    order: ReferentOrder,
    state: TableState,
) -> (ContentId, RecordName)
{
    let (environment, reference, declared) = reference_environment(referent, order);
    let mut table = ContentTable::named();
    table.name_constants(environment.entries());
    if state == TableState::Warm {
        let _warmed = support_key(
            &mut table,
            environment.arena(),
            SupportGoal::ValueTypeLevel(declared),
            Telescope::Whole(&[]),
        );
    }
    let id = support_key(
        &mut table,
        environment.arena(),
        SupportGoal::SynthValue(reference),
        Telescope::Whole(&[declared]),
    );
    match table.name(id) {
        Maybe::Present(name) => (id, name),
        Maybe::Absent(absent) => panic!("a named table names each goal: {absent:?}"),
    }
}

/// Admit the axiom `name : Unit`.
///
/// # Specification
/// - ensures: the axiom's position.
/// - provides: the axiom the naming cases reference.
/// - fails: never.
/// - panics: when the admission refuses.
/// - executable: none — the position is the environment's, which the cases read
///   back through its entries.
///
/// # Adequacy
/// - hypothesis: L3 — the unit axiom admits in every environment.
/// - witness: `environment::encoding_tests::an_axiom_reference_keeps_its_position`
/// - witness: `environment::encoding_tests::a_goal_over_an_axiom_takes_its_position_s_name_864`
fn unit_axiom(environment: &mut crate::Environment) -> ConstantIndex
{
    let mut staging = environment.stage();
    let declared = staging.arena().value_type_unit();
    let staged = staging.axiom(LevelSignature::monomorphic(), declared);
    environment
        .add_decl(staged)
        .expect("the axiom admits")
        .position()
}

/// Admit `name : Unit = ()`.
///
/// # Specification
/// - ensures: the definition's position.
/// - provides: the plain definition the naming cases reference.
/// - fails: never.
/// - panics: when the admission refuses.
/// - executable: none — the position is the environment's, which the cases read
///   back through its entries.
///
/// # Adequacy
/// - hypothesis: L3 — the unit definition admits in every environment.
/// - witness: `environment::encoding_tests::a_definition_reference_reads_alike_in_either_admission_order`
/// - witness: `environment::encoding_tests::each_twin_of_one_content_ranks_past_the_latest_3686`
fn unit_definition(environment: &mut crate::Environment) -> ConstantIndex
{
    let mut staging = environment.stage();
    let declared = staging.arena().value_type_unit();
    let body = staging.arena().value_unit();
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    environment
        .add_decl(staged)
        .expect("the unit definition admits")
        .position()
}

#[test]
fn a_definition_reference_reads_alike_in_either_admission_order()
{
    let first = reference_stream(&unit_definition, ReferentOrder::First);
    let second = reference_stream(&unit_definition, ReferentOrder::Second);
    assert_eq!(
        first, second,
        "a plain definition's reference reads its content, not where it was admitted"
    );
}

#[test]
fn an_axiom_reference_keeps_its_position()
{
    let first = reference_stream(&unit_axiom, ReferentOrder::First);
    let second = reference_stream(&unit_axiom, ReferentOrder::Second);
    assert_ne!(
        first, second,
        "an axiom has no body to name it by, so its reference reads its position"
    );
}

/// #7426: a position that holds no admitted declaration takes no name by its
/// position. The reference to constant 0 reads apart in an environment that
/// admits an axiom at position 0 and in one whose rejection leaves position 0
/// a vacancy, so no memo key names the vacancy as it names the axiom.
#[test]
fn a_reference_to_a_vacancy_reads_apart_from_the_constant_at_its_position_7426()
{
    let stream = |environment: &mut crate::Environment| {
        let mut table = ContentTable::new();
        table.name_constants(environment.entries());
        let mut staging = environment.stage();
        let reference = staging.arena().value_constant(ConstantIndex::from(0_usize));
        let _id = gandr_kernel_core_base::fixture::place(
            &mut table,
            staging.arena(),
            AnyNode::Value(reference),
        );
        gandr_kernel_core_base::fixture::stream(&table).clone()
    };
    let mut admitted = crate::Environment::new();
    let _axiom = unit_axiom(&mut admitted);
    let mut vacated = crate::Environment::new();
    let staged = {
        let mut staging = vacated.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_constant(ConstantIndex::from(9_usize));
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    assert!(
        vacated.add_decl(staged).is_err(),
        "a body naming no declaration is rejected"
    );
    assert_ne!(
        stream(&mut admitted),
        stream(&mut vacated),
        "a vacancy takes no name by its position"
    );
}

#[test]
fn a_goal_takes_one_name_in_either_admission_order_864()
{
    let (cold, first) = goal_name(&unit_definition, ReferentOrder::First, TableState::Cold);
    let (warmed, second) = goal_name(&unit_definition, ReferentOrder::Second, TableState::Warm);
    assert_ne!(cold, warmed, "the warm table numbers the goal later");
    assert_eq!(
        first, second,
        "a goal's name reads its content and its members' names, never their ids"
    );
}

#[test]
fn a_goal_over_an_axiom_takes_its_position_s_name_864()
{
    let (_, first) = goal_name(&unit_axiom, ReferentOrder::First, TableState::Cold);
    let (_, second) = goal_name(&unit_axiom, ReferentOrder::Second, TableState::Cold);
    assert_ne!(
        first, second,
        "an axiom's reference reads its position, so its goal's name does too"
    );
}

#[test]
fn each_twin_of_one_content_ranks_past_the_latest_3686()
{
    let mut environment = crate::Environment::new();
    let left = unit_definition(&mut environment);
    let right = unit_definition(&mut environment);
    let mut staging = environment.stage();
    let unit = staging.arena().value_type_unit();
    let declared = staging.arena().value_type_product(&[unit, unit]);
    let first = staging.arena().value_unit();
    let second = staging.arena().value_unit();
    let pair = staging.arena().value_tuple(&[first, second]);
    let staged = staging.def(LevelSignature::monomorphic(), declared, pair);
    let other = environment
        .add_decl(staged)
        .expect("a definition of other content admits")
        .position();
    let third = unit_definition(&mut environment);
    let ranks = [left, right, other, third].map(|position| {
        match environment
            .entries()
            .get(usize::from(position))
            .map(crate::env::AdmittedDeclaration::key_name)
        {
            Some(crate::encoding::ConstantName::Definition { rank, .. }) => rank,
            Some(
                crate::encoding::ConstantName::Position
                | crate::encoding::ConstantName::Admitted { .. }
                | crate::encoding::ConstantName::Unadmitted,
            )
            | None => {
                panic!("a plain definition is named by its content")
            },
        }
    });
    assert_eq!(
        ranks,
        [
            crate::encoding::DefinitionRank::from(0_usize),
            crate::encoding::DefinitionRank::from(1_usize),
            crate::encoding::DefinitionRank::from(0_usize),
            crate::encoding::DefinitionRank::from(2_usize),
        ],
        "each definition of one type and body is ranked behind every earlier \
         one, past a definition of other content between them"
    );
    let mut staging = environment.stage();
    let left = staging.arena().value_constant(left);
    let right = staging.arena().value_constant(right);
    let unit = staging.arena().value_type_unit();
    let declared = staging.arena().value_type_product(&[unit, unit]);
    let pair = staging.arena().value_tuple(&[left, right]);
    let staged = staging.def(LevelSignature::monomorphic(), declared, pair);
    let _pair = environment
        .add_decl(staged)
        .expect("the pair of references admits");
    let mut table = ContentTable::new();
    table.name_constants(environment.entries());
    assert_ne!(
        gandr_kernel_core_base::fixture::place(
            &mut table,
            environment.arena(),
            AnyNode::Value(left)
        ),
        gandr_kernel_core_base::fixture::place(
            &mut table,
            environment.arena(),
            AnyNode::Value(right)
        ),
        "two definitions keep two names however alike their content: a key \
         never answers for one with the other"
    );
}
