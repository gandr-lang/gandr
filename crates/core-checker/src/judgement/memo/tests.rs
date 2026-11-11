//! The goal memo's tests: a shared term costs the run its shared work, and a
//! key keeps apart the goals that the binders they read keep apart.

use alloc::collections::BTreeMap;
use alloc::string::String;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;

use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::check_value;
use crate::form_value_type;

/// The depth of the iterated pair the tests judge.
const DEPTH: usize = 20;

/// The steps one level of the pair may spend when the memo answers each goal
/// met again. A level spends three: its own goal, its first field's and the
/// answer for its second. The unshared tree spends `2^DEPTH` goals.
const STEPS_PER_LEVEL: usize = 4;

/// The iterated pair of depth [`DEPTH`] beside its type: `t₀ = ()` and
/// `t_{k+1} = *{l = t_k, r = t_k}`, each level one node that both fields of the
/// next level share, and its type built the same way from `Unit`.
///
/// # Specification
/// trivial.
fn iterated_pair(arena: &mut CoreArena) -> (ValueId, ValueTypeId)
{
    let [left, right] = ["l", "r"].map(|label| FieldLabel::from(String::from(label)));
    let mut pair = arena.value_unit();
    let mut ty = arena.value_type_unit();
    for _level in 0 .. DEPTH {
        pair = arena.value_record(BTreeMap::from([
            (left.clone(), pair),
            (right.clone(), pair),
        ]));
        ty = arena.value_type_record(BTreeMap::from([(left.clone(), ty), (right.clone(), ty)]));
    }
    (pair, ty)
}

#[test]
fn a_shared_pair_spends_a_step_for_each_distinct_goal()
{
    let shared = CheckBudget::from(STEPS_PER_LEVEL * (DEPTH + 1));
    let mut arena = CoreArena::new();
    let (pair, ty) = iterated_pair(&mut arena);
    let mut context = CheckingContext::new(&mut arena, shared);
    let formed = form_value_type(&mut context, ty)
        .expect("the pair's type forms within a budget linear in its depth");
    assert!(
        check_value(&mut context, pair, formed).is_ok(),
        "the pair checks within a budget linear in its depth"
    );

    let mut arena = CoreArena::new();
    let (pair, ty) = iterated_pair(&mut arena);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.memoise_goals(MemoActivity::Inactive);
    let exceeded = Err(CheckRefusal::BudgetExceeded {
        budget: CheckBudget::DEFAULT,
    });
    assert_eq!(
        form_value_type(&mut context, ty).map(|_formed| ()),
        exceeded,
        "without the memo the type's formation walks the unshared tree"
    );
    context.memoise_goals(MemoActivity::Active);
    let formed = form_value_type(&mut context, ty).expect("the type forms with the memo");
    context.memoise_goals(MemoActivity::Inactive);
    assert_eq!(
        check_value(&mut context, pair, formed).map(|_checked| ()),
        exceeded,
        "without the memo the pair's check walks the unshared tree"
    );
}

/// The tally counts a miss for each goal the memo keys first and a hit for
/// each goal it meets again. The iterated pair reads each level's goal twice,
/// once through each field, so each plane counts one hit for each level. The
/// type's formation keys one goal for each level and the unit's, and the
/// pair's check keys one goal more than the formation.
/// A tally that counted a hit as a miss, or a consult on the wrong plane,
/// changes a count.
#[cfg(feature = "instrument")]
#[test]
fn the_tally_counts_a_hit_for_each_goal_met_again()
{
    let mut arena = CoreArena::new();
    let (pair, ty) = iterated_pair(&mut arena);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let formed = form_value_type(&mut context, ty).expect("the type forms");
    let formation = context.tally();
    assert!(
        check_value(&mut context, pair, formed).is_ok(),
        "the pair checks"
    );
    let check = context.tally().since(formation);
    let read = |tally: crate::tally::MemoTally| {
        [
            tally.term_hits(),
            tally.term_misses(),
            tally.type_hits(),
            tally.type_misses(),
        ]
        .map(u64::from)
    };
    let depth = u64::try_from(DEPTH).unwrap_or(u64::MAX);
    assert_eq!(
        (read(formation), read(check)),
        ([0, 0, depth, depth.saturating_add(1)], [
            depth,
            depth.saturating_add(2),
            0,
            0
        ]),
        "each plane counts its own consults: one hit for each level"
    );
}

#[test]
fn a_node_read_under_two_binder_types_is_judged_under_each()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(variable);
    let function = arena.computation_lambda(returned);
    let thunk = arena.value_thunk(function);
    let pair = arena.value_tuple(&[thunk, thunk]);
    let answer = arena.comp_type_returner(integer);
    let [from_integer, from_string] = [integer, string].map(|domain| {
        let arrow = arena.comp_type_arrow(domain, answer);
        arena.value_type_thunk(arrow)
    });
    let alike = arena.value_type_product(&[from_integer, from_integer]);
    let apart = arena.value_type_product(&[from_integer, from_string]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let alike = form_value_type(&mut context, alike).expect("the product forms");
    assert!(
        check_value(&mut context, pair, alike).is_ok(),
        "the identity on the integers checks at both components"
    );
    let apart = form_value_type(&mut context, apart).expect("the product forms");
    assert!(
        matches!(
            check_value(&mut context, pair, apart),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "the variable read under a string binder is refused, though the run judged it under an \
         integer binder first"
    );
}
