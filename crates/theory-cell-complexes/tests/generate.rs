//! Generated command patterns over a small alphabet, each drawing its holes
//! from a named set so two generated patterns can be kept apart.
//!
//! Every generator builds the crate's own flat patterns through their public
//! constructors: no fixture type routes ownership through itself.

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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
