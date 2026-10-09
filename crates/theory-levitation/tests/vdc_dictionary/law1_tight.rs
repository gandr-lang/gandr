//! Law 1, the tight category: strict.
//!
//! Signature-morphism composition is strictly associative and unital, its
//! term action is contravariantly functorial, and the chosen product
//! satisfies the β-laws and terminal uniqueness on the nose. Every equality
//! is structural on the crate's own structures.
//!
//! The crate ships no signature-morphism type: `SigMorphism` and its checker
//! `check_morphism` live in the suite's harness, and the first two tests
//! here witness that a valid one is accepted and an invalid one rejected.

use alloc::collections::BTreeMap;

use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use proptest::prelude::*;

use crate::support::DescriptorFactorIndex;
use crate::vdc_dictionary::fixtures::nat_names;
use crate::vdc_dictionary::fixtures::nat_obj;
use crate::vdc_dictionary::fixtures::renaming;
use crate::vdc_dictionary::fixtures::sample_faces;
use crate::vdc_dictionary::harness::FactorRoute;
use crate::vdc_dictionary::harness::SigMorphism;
use crate::vdc_dictionary::harness::apply_term;
use crate::vdc_dictionary::harness::check_morphism;
use crate::vdc_dictionary::harness::compose;

/// A tag strategy over a small alphabet; `nat_names` role-prefixes every
/// name, so tags may repeat harmlessly.
///
/// # Specification
/// trivial.
fn tag() -> impl Strategy<Value = &'static str>
{
    proptest::sample::select(vec!["a", "b", "c", "d", "e", "f"])
}

/// The first factor, the only one a `Nat`-shaped object has.
///
/// # Specification
/// trivial.
fn first() -> DescriptorFactorIndex
{
    DescriptorFactorIndex::from(0_usize)
}

#[test]
fn check_morphism_accepts_a_role_matched_renaming()
{
    let source = nat_names("a".into());
    let target = nat_names("b".into());
    let morphism = renaming(&source, &target);
    assert!(
        check_morphism(&morphism).is_empty(),
        "a role-matched renaming is a valid signature morphism"
    );
}

#[test]
fn check_morphism_rejects_code_and_arity_violations()
{
    // The `Zero` role (code `1`) mapped to the `Succ` role (code `var`), and
    // the binary operation to the unary one: both break payload identity.
    let source = nat_names("a".into());
    let target = nat_names("b".into());
    let map: BTreeMap<Name, Name> = [
        (target.zero.clone(), source.succ.clone()),
        (target.succ.clone(), source.succ.clone()),
        (target.plus.clone(), source.double.clone()),
        (target.double.clone(), source.double.clone()),
    ]
    .into_iter()
    .collect();
    let bad = SigMorphism {
        src: nat_obj(&source),
        tgt: nat_obj(&target),
        routes: vec![FactorRoute {
            src_factor: first(),
            map,
        }],
    };
    let errors = check_morphism(&bad);
    assert!(
        errors.len() >= 2,
        "the code violation and the arity violation are both reported: {errors:?}"
    );
}

#[test]
fn the_diagonal_projects_back_to_the_identity()
{
    let a = nat_obj(&nat_names("a".into()));
    let diagonal = SigMorphism::diagonal(&a);
    assert!(
        check_morphism(&diagonal).is_empty(),
        "the diagonal is a valid morphism"
    );
    let proj0 = SigMorphism::projection(&diagonal.tgt, DescriptorFactorIndex::from(0_usize));
    let proj1 = SigMorphism::projection(&diagonal.tgt, DescriptorFactorIndex::from(1_usize));
    assert_eq!(
        compose(&diagonal, &proj0),
        SigMorphism::identity(&a),
        "π₀ ∘ Δ = id"
    );
    assert_eq!(
        compose(&diagonal, &proj1),
        SigMorphism::identity(&a),
        "π₁ ∘ Δ = id"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    /// Composition is strictly associative as structural equality.
    #[test]
    fn composition_is_strictly_associative(
        ta in tag(), tb in tag(), tc in tag(), td in tag()
    ) {
        let (a, b, c, d) = (
            nat_names(ta.into()),
            nat_names(tb.into()),
            nat_names(tc.into()),
            nat_names(td.into()),
        );
        let f_ab = renaming(&a, &b);
        let f_bc = renaming(&b, &c);
        let f_cd = renaming(&c, &d);
        let left = compose(&compose(&f_ab, &f_bc), &f_cd);
        let right = compose(&f_ab, &compose(&f_bc, &f_cd));
        prop_assert_eq!(left, right, "(h∘g)∘f = h∘(g∘f)");
    }

    /// The identity is a strict two-sided unit for composition.
    #[test]
    fn identity_is_a_strict_unit(ta in tag(), tb in tag()) {
        let (a, b) = (nat_names(ta.into()), nat_names(tb.into()));
        let f_ab = renaming(&a, &b);
        let id_a = SigMorphism::identity(&nat_obj(&a));
        let id_b = SigMorphism::identity(&nat_obj(&b));
        prop_assert!(compose(&id_a, &f_ab) == f_ab, "id ∘ f = f");
        prop_assert!(compose(&f_ab, &id_b) == f_ab, "f ∘ id = f");
    }

    /// The term action is contravariantly functorial and fixes the
    /// identity.
    #[test]
    fn term_action_is_contravariantly_functorial(
        ta in tag(), tb in tag(), tc in tag(), idx in 0_usize .. 4
    ) {
        let (a, b, c) = (nat_names(ta.into()), nat_names(tb.into()), nat_names(tc.into()));
        let outer = renaming(&a, &b); // f : A → B
        let inner = renaming(&b, &c); // g : B → C
        let term: FreeTerm = sample_faces(&c)[idx].lhs.clone();
        // apply_term(g∘f, t) = apply_term(f, apply_term(g, t)): note the variance.
        let composed = apply_term(&compose(&outer, &inner), first(), &term);
        let staged = apply_term(&outer, first(), &apply_term(&inner, first(), &term));
        prop_assert_eq!(composed, staged, "the action is contravariantly functorial");

        let identity = SigMorphism::identity(&nat_obj(&c));
        prop_assert_eq!(apply_term(&identity, first(), &term), term, "id acts trivially");
    }

    /// The chosen product satisfies the projection β-laws and terminal
    /// uniqueness strictly.
    #[test]
    fn chosen_product_beta_and_terminal_hold_strictly(
        ta in tag(), tb in tag(), tc in tag()
    ) {
        let (a, b, c) = (nat_names(ta.into()), nat_names(tb.into()), nat_names(tc.into()));
        let f = renaming(&a, &b); // f : A → B
        let g = renaming(&a, &c); // g : A → C, the shared source A
        let paired = SigMorphism::pairing(&f, &g); // ⟨f, g⟩ : A → B × C
        let proj0 = SigMorphism::projection(&paired.tgt, DescriptorFactorIndex::from(0_usize));
        let proj1 = SigMorphism::projection(&paired.tgt, DescriptorFactorIndex::from(1_usize));
        prop_assert_eq!(compose(&paired, &proj0), f, "π₀ ∘ ⟨f, g⟩ = f");
        prop_assert_eq!(compose(&paired, &proj1), g, "π₁ ∘ ⟨f, g⟩ = g");

        // Terminal uniqueness: `!` has no routes, and `! ∘ f = !`.
        let bang_a = SigMorphism::terminal(&nat_obj(&a));
        prop_assert!(bang_a.routes.is_empty(), "the terminal arrow has no routes");
        let f2 = renaming(&a, &b);
        let bang_b = SigMorphism::terminal(&nat_obj(&b));
        prop_assert_eq!(compose(&f2, &bang_b), bang_a, "! ∘ f = ! (uniqueness)");
    }
}
