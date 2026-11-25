use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use super::CodomainScope;
use super::Components;
use super::HoleForm;
use super::HoleId;
use super::HoleOrigin;
use super::HolePlace;
use super::Knowledge;
use super::MarkIndex;
use super::NominationIndex;
use super::comp_type_knowledge;
use super::matched_function;
use super::matched_list;
use super::matched_product;
use super::matched_returner;
use super::matched_returns;
use super::matched_stack;
use super::matched_static_pi;
use super::matched_sum;
use super::matched_thunk;
use super::matched_with;
use super::matching;
use super::value_type_knowledge;
use crate::arena::CoreArena;
use crate::arena::ValueTypeId;
use crate::classifier::Sort;
use crate::syntax::CompType;
use crate::syntax::ValueType;
use crate::syntax::Zone;

#[test]
fn a_nominated_hole_shares_no_name_with_a_written_one()
{
    let nominated = |index: u32| HoleId::nominated(NominationIndex::from(index));
    let wildcard = |index: u32| HoleId::wildcard(NominationIndex::from(index));
    let first = nominated(0).expect("the first index is named");
    let last = nominated((1 << 30_u32) - 1).expect("the last index is named");
    assert_eq!(u32::from(first), u32::MAX);
    assert_eq!(u32::from(last), 3 << 30_u32);
    assert_eq!([first.origin(), last.origin()], [HoleOrigin::Nominated; 2]);
    assert_ne!(nominated(1), Some(first), "two indices name two holes");
    assert_eq!(
        nominated(1 << 30_u32),
        None,
        "the quarter has no more names"
    );
    let first_wildcard = wildcard(0).expect("the first wildcard is named");
    let last_wildcard = wildcard((1 << 29_u32) - 1).expect("the last wildcard is named");
    assert_eq!(u32::from(first_wildcard), 1 << 31_u32);
    assert_eq!(u32::from(last_wildcard), (1 << 31_u32) + (1 << 29_u32) - 1);
    assert_eq!(
        [first_wildcard.origin(), last_wildcard.origin()],
        [HoleOrigin::Wildcard; 2],
        "a wildcard's name says it is one"
    );
    assert_ne!(
        wildcard(0),
        nominated(0),
        "a wildcard and an omitted implicit at one index are two holes"
    );
    assert_eq!(wildcard(1 << 29_u32), None, "the eighth has no more names");
    for written in [0_u32, 1, (1 << 31_u32) - 1] {
        assert_eq!(
            HoleId::from(written).origin(),
            HoleOrigin::Written,
            "a written name below the half is not nominated"
        );
    }
}

#[test]
fn a_spliced_hole_carries_its_tactic_in_its_name()
{
    let deepest = crate::tactic::Tactic::try_from(crate::tactic::Tactic::INTROS - 1)
        .expect("the deepest tactic is admitted");
    let spliced = |index: u32, tactic| HoleId::spliced(NominationIndex::from(index), tactic);
    let first = spliced(0, crate::tactic::Tactic::ASSUMPTION).expect("the first place is named");
    let last = spliced((1 << 24_u32) - 1, deepest).expect("the last place is named");
    assert_eq!(u32::from(first), (1 << 31_u32) + (1 << 29_u32));
    assert_eq!(u32::from(last), (3 << 30_u32) - 1, "the eighth's last name");
    assert_eq!([first.origin(), last.origin()], [HoleOrigin::Spliced; 2]);
    assert_eq!(first.tactic(), Some(crate::tactic::Tactic::ASSUMPTION));
    assert_eq!(last.tactic(), Some(deepest));
    assert_ne!(
        spliced(0, deepest),
        Some(first),
        "two tactics at one place are two holes"
    );
    assert_eq!(
        spliced(1 << 24_u32, crate::tactic::Tactic::ASSUMPTION),
        None,
        "the places past the last are refused"
    );
    let wildcard = HoleId::wildcard(NominationIndex::from(0)).expect("a wildcard's name");
    assert_eq!(wildcard.tactic(), None, "a wildcard runs no tactic");
    assert_eq!(
        HoleId::from(0_u32).tactic(),
        None,
        "a written hole runs none"
    );
}

#[test]
fn a_crossing_hole_counts_up_from_the_quarter_nominated_counts_down()
{
    let crossing = |index: u32| HoleId::crossing(NominationIndex::from(index));
    let first = crossing(0).expect("the first index is named");
    assert_eq!(u32::from(first), 3 << 30_u32, "the quarter's first name");
    assert_eq!(first.origin(), HoleOrigin::Nominated);
    assert_eq!(
        crossing(1).map(u32::from),
        Some((3 << 30_u32) + 1),
        "the next index counts up"
    );
    assert_ne!(
        crossing(0),
        HoleId::nominated(NominationIndex::from(0)),
        "the first crossing and the first omitted implicit are two holes"
    );
    assert_eq!(
        crossing(0),
        HoleId::nominated(NominationIndex::from((1 << 30_u32) - 1)),
        "the two meet only at the quarter's far end"
    );
    assert_eq!(crossing(1 << 30_u32), None, "the quarter has no more names");
}

#[test]
fn a_form_s_hole_names_are_apart_from_every_other_form_s_5598()
{
    /// A name of one origin at a form and a place.
    type Named = fn((HoleForm, HolePlace)) -> Option<HoleId>;
    let at = |form: u32, place: u32| (HoleForm::from(form), HolePlace::from(place));
    let splice = |(form, place)| HoleId::spliced_in(form, place, crate::tactic::Tactic::ASSUMPTION);
    let kinds: [(Named, u32, HoleOrigin); 4] = [
        (
            |(form, place)| HoleId::written(form, place),
            1 << 15_u32,
            HoleOrigin::Written,
        ),
        (
            |(form, place)| HoleId::nominated_in(form, place),
            1 << 14_u32,
            HoleOrigin::Nominated,
        ),
        (
            |(form, place)| HoleId::wildcard_in(form, place),
            1 << 13_u32,
            HoleOrigin::Wildcard,
        ),
        (splice, 1 << 8_u32, HoleOrigin::Spliced),
    ];
    let mut names = alloc::collections::BTreeSet::new();
    for (name, share, origin) in kinds {
        for (form, place) in [
            (0, 0),
            (0, share - 1),
            (1, 0),
            (1, share - 1),
            (u32::from(u16::MAX), share - 1),
        ] {
            let hole = name(at(form, place))
                .expect("a form below the last and a place in its share are named");
            assert_eq!(
                hole.origin(),
                origin,
                "a hole's name keeps its origin's part"
            );
            assert!(
                names.insert(hole),
                "no two forms, places or origins share a name"
            );
        }
        assert_eq!(
            name(at(0, share)),
            None,
            "a place past the form's share is refused"
        );
        assert_eq!(
            name(at(1 << 16_u32, 0)),
            None,
            "a form past the last is refused"
        );
    }
    assert_eq!(
        HoleId::written(HoleForm::from(1), HolePlace::from(0)).map(u32::from),
        Some(1 << 15_u32),
        "a form's first written name follows the form before's share"
    );
    assert_eq!(
        HoleId::nominated_in(HoleForm::from(1), HolePlace::from(0)),
        HoleId::nominated(NominationIndex::from(1 << 14_u32)),
        "a form's first nomination counts down past the form before's share"
    );
    assert_eq!(
        HoleId::spliced_in(
            HoleForm::from(1),
            HolePlace::from(0),
            crate::tactic::Tactic::ASSUMPTION
        ),
        HoleId::spliced(
            NominationIndex::from(1 << 8_u32),
            crate::tactic::Tactic::ASSUMPTION
        ),
        "a splice's form stands below its tactic's bits"
    );
}

#[test]
fn the_decode_of_a_hole_is_unknown_and_of_a_variable_is_not()
{
    let mut arena = CoreArena::new();
    let unknown = arena.value_type_unknown();
    let hole = arena.value_hole(HoleId::from(3_u32));
    let named = arena.value_type_element(hole, Level::zero());
    let marked = arena.value_mark(MarkIndex::from(0_u32), hole);
    let marked = arena.value_type_element(marked, Level::zero());
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(variable, Level::zero());
    let applied_hole = arena.value_static_application(hole, variable);
    let applied_hole = arena.value_static_application(applied_hole, variable);
    let applied_hole = arena.value_type_element(applied_hole, Level::zero());
    let applied_variable = arena.value_static_application(variable, hole);
    let applied_variable = arena.value_type_element(applied_variable, Level::zero());
    let forced = arena.computation_force(hole);
    let call = arena.computation_application(forced, variable);
    let called_hole = arena.value_returned(call);
    let called_hole = arena.value_type_element(called_hole, Level::zero());
    let forced = arena.computation_force(variable);
    let call = arena.computation_application(forced, hole);
    let called_variable = arena.value_returned(call);
    let called_variable = arena.value_type_element(called_variable, Level::zero());
    let atom = arena.value_type_base(BaseType::Integer);
    for (subject, knowledge) in [
        (unknown, Knowledge::Unknown),
        (named, Knowledge::Unknown),
        (marked, Knowledge::Unknown),
        (applied_hole, Knowledge::Unknown),
        (called_hole, Knowledge::Unknown),
        (decoded, Knowledge::Known),
        (applied_variable, Knowledge::Known),
        (called_variable, Knowledge::Known),
        (atom, Knowledge::Known),
    ] {
        assert_eq!(value_type_knowledge(&arena, subject), knowledge);
    }
    assert_eq!(
        value_type_knowledge(&CoreArena::new(), unknown),
        Knowledge::Known,
        "a dangling id reads as known"
    );
    let unknown = arena.comp_type_unknown();
    let named = arena.comp_type_element(hole, Level::zero());
    let decoded = arena.comp_type_element(variable, Level::zero());
    let returner = arena.comp_type_returner(atom);
    for (subject, knowledge) in [
        (unknown, Knowledge::Unknown),
        (named, Knowledge::Unknown),
        (decoded, Knowledge::Known),
        (returner, Knowledge::Known),
    ] {
        assert_eq!(comp_type_knowledge(&arena, subject), knowledge);
    }
}

#[test]
fn the_unknown_type_matches_every_former_with_unknown_components()
{
    let mut arena = CoreArena::new();
    let unknown = arena.value_type_unknown();
    let hole = arena.value_hole(HoleId::from(1_u32));
    let named = arena.value_type_element(hole, Level::zero());
    for subject in [unknown, named] {
        let Maybe::Present(body) = matched_thunk(&mut arena, subject)
        else {
            panic!("the unknown type matches a thunk");
        };
        assert_eq!(arena.comp_type(body), Some(&CompType::Unknown));
        for matched in [
            matched_product(&mut arena, subject),
            matched_sum(&mut arena, subject),
        ] {
            let Maybe::Present(Components::Unknown(component)) = matched
            else {
                panic!("the unknown type matches a product and a sum of unknowns");
            };
            assert_eq!(arena.value_type(component), Some(&ValueType::Unknown));
        }
        let Maybe::Present((first, second)) = matched_static_pi(&mut arena, subject)
        else {
            panic!("the unknown type matches a static Pi");
        };
        assert_eq!(arena.value_type(first), Some(&ValueType::Unknown));
        assert_eq!(arena.value_type(second), Some(&ValueType::Unknown));
        let Maybe::Present(element) = matched_list(&mut arena, subject)
        else {
            panic!("the unknown type matches a List");
        };
        assert_eq!(arena.value_type(element), Some(&ValueType::Unknown));
        let Maybe::Present((input, output)) = matched_stack(&mut arena, subject)
        else {
            panic!("the unknown type matches a stack");
        };
        assert_eq!(arena.comp_type(input), Some(&CompType::Unknown));
        assert_eq!(arena.comp_type(output), Some(&CompType::Unknown));
    }
    let unknown = arena.comp_type_unknown();
    let Maybe::Present(result) = matched_returner(&mut arena, unknown)
    else {
        panic!("the unknown type matches a returner");
    };
    assert_eq!(arena.value_type(result), Some(&ValueType::Unknown));
    let Maybe::Present(function) = matched_function(&mut arena, unknown)
    else {
        panic!("the unknown type matches a function");
    };
    assert_eq!(
        arena.value_type(function.domain()),
        Some(&ValueType::Unknown)
    );
    assert_eq!(
        arena.comp_type(function.codomain()),
        Some(&CompType::Unknown)
    );
    assert_eq!(function.scope(), CodomainScope::Ambient);
    let Maybe::Present(Components::Unknown(component)) = matched_with(&mut arena, unknown)
    else {
        panic!("the unknown type matches a lazy product of unknown components");
    };
    assert_eq!(arena.comp_type(component), Some(&CompType::Unknown));
}

#[test]
fn a_known_type_matches_only_its_own_former()
{
    let mut arena = CoreArena::new();
    let atom = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let product = arena.value_type_product(&[atom, text]);
    let sum = arena.value_type_sum(&[text, atom]);
    let returner = arena.comp_type_returner(atom);
    let thunk = arena.value_type_thunk(returner);
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let static_pi = arena.value_type_static_pi(universe, universe);
    let arrow = arena.comp_type_arrow(atom, returner);
    let pi = arena.comp_type_pi(text, returner);
    let list = arena.value_type_list(atom);
    let stack = arena.value_type_stack(returner, arrow);
    let with = arena.comp_type_with(&[returner, arrow, returner]);
    let top = arena.comp_type_with(&[]);
    assert_eq!(matched_thunk(&mut arena, thunk), Maybe::Present(returner));
    let known = |parts: &[ValueTypeId]| Maybe::Present(Components::Known(parts.into()));
    assert_eq!(matched_product(&mut arena, product), known(&[atom, text]));
    assert_eq!(matched_sum(&mut arena, sum), known(&[text, atom]));
    let triple = arena.value_type_product(&[atom, text, atom]);
    let unit = arena.value_type_unit();
    let empty = arena.value_type_sum(&[]);
    assert_eq!(
        matched_product(&mut arena, triple),
        known(&[atom, text, atom]),
        "a product of three matches with its three components"
    );
    assert_eq!(
        matched_product(&mut arena, unit),
        known(&[]),
        "the unit type is the product of no components"
    );
    assert_eq!(
        matched_sum(&mut arena, empty),
        known(&[]),
        "the empty type is the sum of no summands"
    );
    assert_eq!(
        matched_static_pi(&mut arena, static_pi),
        Maybe::Present((universe, universe))
    );
    assert_eq!(matched_returner(&mut arena, returner), Maybe::Present(atom));
    assert_eq!(matched_list(&mut arena, list), Maybe::Present(atom));
    assert_eq!(
        matched_stack(&mut arena, stack),
        Maybe::Present((returner, arrow))
    );
    assert_eq!(
        matched_with(&mut arena, with),
        Maybe::Present(Components::Known([returner, arrow, returner].into())),
        "a lazy product of three matches with its three components"
    );
    assert_eq!(
        matched_with(&mut arena, top),
        Maybe::Present(Components::Known([].into())),
        "the terminal type is the lazy product of no components"
    );
    let Maybe::Present(ambient) = matched_function(&mut arena, arrow)
    else {
        panic!("an arrow matches a function");
    };
    assert_eq!(
        (ambient.domain(), ambient.codomain(), ambient.scope()),
        (atom, returner, CodomainScope::Ambient)
    );
    let Maybe::Present(dependent) = matched_function(&mut arena, pi)
    else {
        panic!("a dependent arrow matches a function");
    };
    assert_eq!(
        (dependent.domain(), dependent.codomain(), dependent.scope()),
        (text, returner, CodomainScope::UnderBinder)
    );
    let mismatched = matching::Absent::Mismatched;
    assert_eq!(matched_thunk(&mut arena, atom), Maybe::Absent(mismatched));
    assert_eq!(matched_product(&mut arena, sum), Maybe::Absent(mismatched));
    assert_eq!(matched_sum(&mut arena, product), Maybe::Absent(mismatched));
    assert_eq!(
        matched_static_pi(&mut arena, product),
        Maybe::Absent(mismatched)
    );
    assert_eq!(
        matched_returner(&mut arena, arrow),
        Maybe::Absent(mismatched)
    );
    assert_eq!(
        matched_function(&mut arena, returner),
        Maybe::Absent(mismatched)
    );
    assert_eq!(matched_list(&mut arena, product), Maybe::Absent(mismatched));
    assert_eq!(matched_stack(&mut arena, list), Maybe::Absent(mismatched));
    assert_eq!(matched_with(&mut arena, arrow), Maybe::Absent(mismatched));
    assert_eq!(
        matched_thunk(&mut CoreArena::new(), thunk),
        Maybe::Absent(matching::Absent::Dangling)
    );
}

#[test]
fn a_returner_of_several_values_matches_only_at_its_arity()
{
    let mut arena = CoreArena::new();
    let count = crate::syntax::ComponentCount::from;
    let atom = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let pair = arena.comp_type_returns_with_effects(&[atom, text], crate::effect::EffectRow::EMPTY);
    let none = arena.comp_type_returns_with_effects(&[], crate::effect::EffectRow::EMPTY);
    let returner = arena.comp_type_returner(atom);
    assert_eq!(
        matched_returns(&mut arena, pair, count(2)),
        Maybe::Present(alloc::vec::Vec::from([atom, text])),
        "a returner of two values matches at two, its results in order"
    );
    assert_eq!(
        matched_returns(&mut arena, none, count(0)),
        Maybe::Present(alloc::vec::Vec::new())
    );
    let mismatched = Maybe::Absent(matching::Absent::Mismatched);
    assert_eq!(matched_returns(&mut arena, pair, count(3)), mismatched);
    assert_eq!(matched_returns(&mut arena, none, count(2)), mismatched);
    assert_eq!(
        matched_returns(&mut arena, returner, count(2)),
        mismatched,
        "a returner of one value is no returner of two"
    );
    assert_eq!(
        matched_returner(&mut arena, pair),
        Maybe::Absent(matching::Absent::Mismatched)
    );
    let unknown = arena.comp_type_unknown();
    let Maybe::Present(results) = matched_returns(&mut arena, unknown, count(2))
    else {
        panic!("the unknown type matches a returner of any arity");
    };
    assert!(
        results
            .iter()
            .all(|&result| arena.value_type(result) == Some(&ValueType::Unknown)),
        "with an unknown type per result"
    );
    assert_eq!(results.len(), 2);
    assert_eq!(
        matched_returns(&mut CoreArena::new(), pair, count(2)),
        Maybe::Absent(matching::Absent::Dangling)
    );
}
