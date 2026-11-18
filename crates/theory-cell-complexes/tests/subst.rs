//! Matching and unification over generated patterns: every match
//! reproduces its target, every unifier equates its two sides, and a refusal
//! binds nothing.

use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::match_cmd;
use gandr_theory_cell_complexes::unify_cmd;
use proptest::prelude::*;

use crate::generate::LEFT;
use crate::generate::RIGHT;
use crate::generate::cmd;
use crate::generate::instantiation;
use crate::generate::renaming;

proptest! {
    /// A pattern matches every instance of itself, reproducing it; any other
    /// target either matches and is reproduced, or is refused with nothing
    /// bound.
    #[test]
    fn every_match_reproduces_its_target(
        pattern in cmd(LEFT),
        sigma in instantiation(LEFT, RIGHT),
        other in cmd(RIGHT),
    ) {
        let instance = sigma.apply_cmd(&pattern);
        let mut subst = Subst::new();
        prop_assert!(
            bool::from(match_cmd(&pattern, &instance, &mut subst)),
            "a pattern matches its own instance"
        );
        prop_assert_eq!(&instance, &subst.apply_cmd(&pattern), "and the match reproduces it");
        let mut subst = Subst::new();
        if bool::from(match_cmd(&pattern, &other, &mut subst)) {
            prop_assert_eq!(&other, &subst.apply_cmd(&pattern), "every match reproduces its target");
        }
        else {
            prop_assert!(bool::from(subst.is_empty()), "a refused match binds nothing");
        }
    }

    /// A pattern unifies with an instance of its renamed copy, and every
    /// unifier found, for that pair or an unrelated one, equates the two
    /// sides after one application; a refusal binds nothing.
    #[test]
    fn every_unifier_equates_its_two_sides(
        left in cmd(LEFT),
        tau in instantiation(RIGHT, RIGHT),
        other in cmd(RIGHT),
    ) {
        let instance = tau.apply_cmd(&renaming(LEFT, RIGHT).apply_cmd(&left));
        let mut subst = Subst::new();
        prop_assert!(
            bool::from(unify_cmd(&left, &instance, &mut subst)),
            "a pattern unifies with an instance of its renamed copy"
        );
        prop_assert_eq!(
            subst.apply_cmd(&left),
            subst.apply_cmd(&instance),
            "and the unifier equates the two sides"
        );
        let mut subst = Subst::new();
        if bool::from(unify_cmd(&left, &other, &mut subst)) {
            prop_assert_eq!(
                subst.apply_cmd(&left),
                subst.apply_cmd(&other),
                "every unifier equates its two sides"
            );
        }
        else {
            prop_assert!(bool::from(subst.is_empty()), "a refused unification binds nothing");
        }
    }
}
