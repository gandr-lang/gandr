//! Generated command patterns over a small alphabet, each drawing its holes
//! from a named set so two generated patterns can be kept apart.
//!
//! Every generator builds the crate's own flat patterns through their public
//! constructors: no fixture type routes ownership through itself.

use anodized::spec;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Subst;
use proptest::prelude::*;

/// The hole names a generated pattern draws from: two producer and two
/// consumer metavariables.
#[derive(Clone, Copy, Debug)]
pub struct Holes
{
    /// The producer hole names.
    producers: [&'static str; 2],
    /// The consumer hole names.
    consumers: [&'static str; 2],
}

/// The holes of a left-hand pattern.
pub const LEFT: Holes = Holes {
    producers: ["x", "y"],
    consumers: ["a", "b"],
};

/// The holes of a pattern kept apart from [`LEFT`].
pub const RIGHT: Holes = Holes {
    producers: ["u", "v"],
    consumers: ["c", "d"],
};

/// Generated producer patterns over `Zero`, `Succ`, `Pair` and `holes`.
///
/// # Specification
/// - ensures: generated producer patterns range over nullary Zero, unary Succ,
///   binary Pair and the supplied producer holes.
/// - panics: none.
/// - executable: none — instrumentation gives its wrapper closure this
///   impl-Trait return type, which Rust rejects for closures.
///
/// # Adequacy
/// - hypothesis: L2 — generated instances pass the reconstruction or order law
///   across leaf and recursive shapes. Wrong sorts and malformed patterns
///   violate those observations; the strategy itself is an opaque input-domain
///   description.
/// - witness: `tests::order::the_path_order_survives_a_uniform_hole_instantiation`
pub fn prod(holes: Holes) -> impl Strategy<Value = ProdPat>
{
    let [x, y] = holes.producers;
    let leaf = prop_oneof![
        Just(ProdPat::meta(x)),
        Just(ProdPat::meta(y)),
        Just(ProdPat::ctor("Zero", [])),
    ];
    leaf.prop_recursive(3_u32, 12_u32, 2_u32, |inner| {
        prop_oneof![
            inner.clone().prop_map(|arg| ProdPat::ctor("Succ", [arg])),
            proptest::collection::vec(inner, 2 ..= 2_usize)
                .prop_map(|args| ProdPat::ctor("Pair", args)),
        ]
    })
}

/// Generated consumer patterns over `★`, `Succ⁻`, `add` and `holes`.
///
/// # Specification
/// - ensures: generated consumer patterns range over the terminal, unary return
///   frames, one-argument operations and the supplied holes.
/// - panics: none.
/// - executable: none — instrumentation gives its wrapper closure this
///   impl-Trait return type, which Rust rejects for closures.
///
/// # Adequacy
/// - hypothesis: L2 — generated instances pass the reconstruction or order law
///   across leaf and recursive shapes. Wrong sorts and malformed patterns
///   violate those observations; the strategy itself is an opaque input-domain
///   description.
/// - witness: `tests::generalize::every_member_is_its_generalization_under_its_arms`
pub fn cons(holes: Holes) -> impl Strategy<Value = ConsPat>
{
    let [a, b] = holes.consumers;
    let leaf = prop_oneof![
        Just(ConsPat::meta(a)),
        Just(ConsPat::meta(b)),
        Just(ConsPat::top()),
    ];
    leaf.prop_recursive(3_u32, 12_u32, 2_u32, move |inner| {
        prop_oneof![
            inner.clone().prop_map(|ret| ConsPat::frame("Succ", ret)),
            (prod(holes), inner).prop_map(|(arg, ret)| ConsPat::op("add", [arg], ret)),
        ]
    })
}

/// Generated positive cuts over `holes`.
///
/// # Specification
/// trivial.
pub fn cmd(holes: Holes) -> impl Strategy<Value = CmdPat>
{
    (prod(holes), cons(holes)).prop_map(|(prod, cons)| CmdPat::cut(Polarity::Positive, prod, cons))
}

/// Generated substitutions binding every hole of `bound` to a pattern over
/// `images`.
///
/// # Specification
/// - requires: the two bound names in each category are distinct.
/// - ensures: each generated map binds every bound hole in its category to an
///   image over the supplied image-hole sets.
/// - panics: a generated binding fails only outside the distinct-name domain.
/// - executable: none — instrumentation gives its wrapper closure the
///   function's impl-Trait return type, which Rust rejects for closures.
///
/// # Adequacy
/// - hypothesis: L2 — generated maps instantiate both categories before match
///   and generalization reconstruction. Missing bindings or wrong-category
///   images change those properties; output samples are observed by the
///   property runner.
/// - witness: `tests::subst::every_match_reproduces_its_target`
pub fn instantiation(
    bound: Holes,
    images: Holes,
) -> impl Strategy<Value = Subst>
{
    (
        proptest::collection::vec(prod(images), 2 ..= 2_usize),
        proptest::collection::vec(cons(images), 2 ..= 2_usize),
    )
        .prop_map(move |(prods, conss)| {
            let mut subst = Subst::new();
            for (name, image) in bound.producers.into_iter().zip(prods) {
                subst
                    .bind_prod(MetaVar::producer(name), image)
                    .expect("a fresh producer hole binds");
            }
            for (name, image) in bound.consumers.into_iter().zip(conss) {
                subst
                    .bind_cons(MetaVar::consumer(name), image)
                    .expect("a fresh consumer hole binds");
            }
            subst
        })
}

/// The renaming that sends each hole of `from` to the hole of `to` at the
/// same place.
///
/// # Specification
/// - requires: the two source names in each category are distinct.
/// - ensures: four bindings, each source hole mapped to the corresponding
///   target hole without changing category.
/// - panics: a source collision can refuse a conflicting rebind.
///
/// # Adequacy
/// - hypothesis: L3 — the generated unifier property first renames one side
///   into a disjoint hole set, then instantiates it and checks both solved
///   faces. A missing or cross-category binding changes the reconstruction.
/// - witness: `tests::subst::every_unifier_equates_its_two_sides`
#[spec(requires: from.producers[0] != from.producers[1] && from.consumers[0] != from.consumers[1],
    ensures: |output| usize::from(output.len()) == from.producers.len().saturating_add(from.consumers.len()))]
pub fn renaming(
    from: Holes,
    to: Holes,
) -> Subst
{
    let mut subst = Subst::new();
    for (name, image) in from.producers.into_iter().zip(to.producers) {
        subst
            .bind_prod(MetaVar::producer(name), ProdPat::meta(image))
            .expect("a fresh producer hole binds");
    }
    for (name, image) in from.consumers.into_iter().zip(to.consumers) {
        subst
            .bind_cons(MetaVar::consumer(name), ConsPat::meta(image))
            .expect("a fresh consumer hole binds");
    }
    subst
}
