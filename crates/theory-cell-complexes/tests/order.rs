//! The reduction order over generated patterns: a strict order, and stable
//! under instantiating a hole on both sides.

use core::cmp::Ordering;

use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::reduction_cmp;
use proptest::prelude::*;

use crate::generate::LEFT;
use crate::generate::cmd;
use crate::generate::prod;

proptest! {
    /// The relation is a strict order: never both ways, and never a pattern
    /// against itself.
    #[test]
    fn the_order_is_a_strict_order_over_generated_patterns(
        left in cmd(LEFT),
        right in cmd(LEFT),
    ) {
        prop_assert_eq!(
            Ordering::Equal,
            reduction_cmp(&left, &left),
            "irreflexive: a pattern never exceeds itself"
        );
        let forward = reduction_cmp(&left, &right);
        let backward = reduction_cmp(&right, &left);
        prop_assert_eq!(forward.reverse(), backward, "antisymmetric: the mirror verdict is reversed");
    }

    /// The order is stable under substitution on the pairs it orients:
    /// instantiating a hole uniformly on both sides cannot reverse a strict
    /// verdict.
    #[test]
    fn the_path_order_survives_a_uniform_hole_instantiation(
        left in cmd(LEFT),
        right in cmd(LEFT),
        filler in prod(LEFT),
    ) {
        let verdict = reduction_cmp(&left, &right);
        prop_assume!(verdict != Ordering::Equal);
        let mut subst = Subst::new();
        subst
            .bind_prod(MetaVar::producer("x"), filler)
            .expect("a fresh producer hole binds");
        prop_assert_eq!(
            verdict,
            reduction_cmp(&subst.apply_cmd(&left), &subst.apply_cmd(&right)),
            "a strict verdict survives instantiating the hole `x` on both sides"
        );
    }
}
