//! Anti-unification over generated families: every member is its
//! generalization under its own arms, a point stands only where the members
//! differ and once per distinct column, and a family of instances of one
//! pattern generalizes to an instance of that pattern.

use anodized::spec;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Generalization;
use gandr_theory_cell_complexes::GeneralizationPoint;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::anti_unify_cmd;
use gandr_theory_cell_complexes::binding;
use gandr_theory_cell_complexes::match_cmd;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use crate::generate::LEFT;
use crate::generate::RIGHT;
use crate::generate::cmd;
use crate::generate::instantiation;

/// What one arm binds its point to: the producer image or the consumer image,
/// the other absent.
type Image<'point> = (
    Maybe<&'point ProdPat, binding::Absent>,
    Maybe<&'point ConsPat, binding::Absent>,
);

/// The column a point stands for: its image under each member's arm.
///
/// # Specification
/// trivial.
fn column(point: &GeneralizationPoint<SequentAlphabet>) -> Vec<Image<'_>>
{
    point
        .arms
        .iter()
        .map(|arm| {
            (
                arm.binding.get_prod(&point.var),
                arm.binding.get_cons(&point.var),
            )
        })
        .collect()
}

/// The generalization of `family`, or the property fails.
///
/// # Specification
/// - requires: a nonempty family of equally wide tuples whose corresponding
///   commands have the same polarity.
/// - ensures: one generalized pattern per component and one arm per member at
///   each disagreement point.
/// - panics: when the family is refused; generated members share one polarity
///   and one length, so a refusal is a defect.
///
/// # Adequacy
/// - hypothesis: L3 — generated nonempty uniform families reconstruct every
///   member from the returned arms and compare shared patterns against the
///   generalization. Wrong component widths, arms or disagreement sharing
///   change these observations.
/// - witness: `tests::generalize::every_member_is_its_generalization_under_its_arms`
#[spec(
    requires: family.first().is_some_and(|first| family.iter().all(|member| member.len() == first.len()
        && member.iter().zip(first).all(|(left, right)| left.polarity() == right.polarity()))),
    ensures: |output| family.first().is_some_and(|first| output.patterns.len() == first.len())
        && output.points.iter().all(|point| point.arms.len() == family.len()),
)]
fn generalized(family: &[Vec<CmdPat>]) -> Generalization<SequentAlphabet>
{
    let members: Vec<&[CmdPat]> = family.iter().map(Vec::as_slice).collect();
    let Maybe::Present(generalization) = anti_unify_cmd(&members)
    else {
        panic!("a generated family generalizes");
    };
    generalization
}

proptest! {
    /// Members drawn as instances of a pattern pair, beside unrelated pairs:
    /// each member is its generalization under its arms, no point's arms all
    /// bind one image, and no two points stand for one column.
    #[test]
    fn every_member_is_its_generalization_under_its_arms(
        peak in cmd(LEFT),
        join in cmd(LEFT),
        sigmas in prop::collection::vec(instantiation(LEFT, RIGHT), 1 .. 5),
        others in prop::collection::vec((cmd(RIGHT), cmd(RIGHT)), 0 .. 3),
    ) {
        let family: Vec<Vec<CmdPat>> = sigmas
            .iter()
            .map(|sigma| vec![sigma.apply_cmd(&peak), sigma.apply_cmd(&join)])
            .chain(others.into_iter().map(|(left, right)| vec![left, right]))
            .collect();
        let generalization = generalized(&family);
        for (index, member) in family.iter().enumerate() {
            let rebuilt: Vec<CmdPat> = generalization
                .patterns
                .iter()
                .map(|pattern| {
                    generalization
                        .points
                        .iter()
                        .fold(pattern.clone(), |term, point| point.arms[index].binding.apply_cmd(&term))
                })
                .collect();
            prop_assert_eq!(member, &rebuilt, "each member is its generalization under its arms");
        }
        let columns: Vec<Vec<Image<'_>>> = generalization.points.iter().map(column).collect();
        for (index, images) in columns.iter().enumerate() {
            prop_assert!(
                images.iter().any(|image| image != &images[0]),
                "a point stands only where two members differ"
            );
            prop_assert!(
                !columns[.. index].contains(images),
                "and one point stands per distinct column"
            );
        }
    }

    /// A family of instances of one pattern generalizes to an instance of
    /// that pattern: the generalization is no more general than any pattern
    /// every member shares.
    #[test]
    fn a_shared_pattern_matches_the_generalization(
        pattern in cmd(LEFT),
        sigmas in prop::collection::vec(instantiation(LEFT, RIGHT), 1 .. 5),
    ) {
        let family: Vec<Vec<CmdPat>> = sigmas
            .iter()
            .map(|sigma| vec![sigma.apply_cmd(&pattern)])
            .collect();
        let generalization = generalized(&family);
        let mut subst = Subst::new();
        prop_assert!(
            bool::from(match_cmd(&pattern, &generalization.patterns[0], &mut subst)),
            "the shared pattern matches the generalization"
        );
    }
}
