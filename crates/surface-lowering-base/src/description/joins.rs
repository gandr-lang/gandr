//! The joins of the include graph: a `theory` block is well formed when every
//! two theories it reaches through `include` have one join among the theories
//! it sees, the poorest one reaching both (Sakaguchi, _Refinement and
//! extension of mathematical structures in proof assistants based on
//! dependent type theory_, 2023, § 5.2). The block that gives a pair a second
//! incomparable minimal common extension is refused, the pair and every such
//! join named, so a search for a model meets one route to each request.
//!
//! # Witnesses
//!
//! `description::theory::tests::two_joins_of_one_pair_are_refused_by_name`,
//! `description::theory::tests::an_included_theory_is_the_extension_restricted`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use quenchant_shape::shape::Maybe;

use crate::circuit::JoinFault;
use crate::description::DescribedDeclaration;
use crate::description::Visible;

/// The include graph: each theory's serial, the serials it includes directly,
/// and its name.
type Graph = BTreeMap<NominalSerial, (Vec<NominalSerial>, Name)>;

/// Every theory `from` reaches through `include` in `graph`, itself among
/// them.
///
/// # Specification
/// - ensures: `from` and the closure of `graph`'s edges from it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a theory two steps up a chain is reached.
/// - witness: `description::theory::tests::an_included_theory_is_the_extension_restricted`
#[spec(ensures: |ret| ret.contains(&from))]
fn reached(
    graph: &Graph,
    from: NominalSerial,
) -> BTreeSet<NominalSerial>
{
    let mut seen = BTreeSet::from([from]);
    let mut pending = Vec::from([from]);
    while let Some(theory) = pending.pop() {
        let edges = graph
            .get(&theory)
            .map_or(&[][..], |&(ref edges, _)| edges.as_slice());
        for &above in edges {
            if seen.insert(above) {
                pending.push(above);
            }
        }
    }
    seen
}

/// The serial a declaration presenting a theory carries.
///
/// # Specification
/// trivial.
fn presenting(declaration: &DescribedDeclaration) -> Option<NominalSerial>
{
    match declaration.presentation {
        Maybe::Present(_) => Some(declaration.description.id.serial),
        Maybe::Absent(_) => None,
    }
}

/// The first pair of theories `block`, including `direct`, reaches that
/// `block` gives a second join among the theories `visible` sees.
///
/// # Specification
/// - requires: `visible` was read for `block`.
/// - ensures: `None` unless `block` is one of two or more minimal common
///   extensions, among the seen theories and itself, of an incomparable pair it
///   reaches; then the first such pair in the order `block` reaches them, with
///   its minimal common extensions in reading order, `block` last. A comparable
///   pair's join is the greater and is never refused; a block above a pair
///   already joined twice reaches it through a join, and the refusal stays with
///   the block that added the second.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a second theory including one pair is refused naming both
///   joins, and a block above it is not; a diamond over one base is accepted.
/// - witness: `description::theory::tests::two_joins_of_one_pair_are_refused_by_name`
/// - witness: `description::theory::tests::an_included_theory_is_the_extension_restricted`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|fault| fault.joins.len() >= 2
    && fault.joins.last() == Some(&block.name)))]
pub(super) fn ambiguous_join(
    block: &NominalId,
    direct: &[&NominalId],
    visible: &Visible<'_>,
) -> Option<JoinFault>
{
    let mut graph: Graph = visible
        .read()
        .filter_map(|declaration| match declaration.presentation {
            Maybe::Present(ref presented) => Some((
                declaration.description.id.serial,
                (
                    presented
                        .inclusions
                        .iter()
                        .map(|included| included.theory.serial)
                        .collect(),
                    declaration.description.id.name.clone(),
                ),
            )),
            Maybe::Absent(_) => None,
        })
        .collect();
    let _previous = graph.insert(
        block.serial,
        (
            direct.iter().map(|theory| theory.serial).collect(),
            block.name.clone(),
        ),
    );
    let mut candidates: Vec<(NominalSerial, BTreeSet<NominalSerial>)> = visible
        .seen()
        .filter_map(presenting)
        .filter(|&serial| serial != block.serial)
        .map(|serial| (serial, reached(&graph, serial)))
        .collect();
    candidates.push((block.serial, reached(&graph, block.serial)));
    let mut placed: BTreeSet<NominalSerial> = BTreeSet::new();
    let mut order: Vec<NominalSerial> = Vec::new();
    for theory in direct {
        for found in reached(&graph, theory.serial) {
            if placed.insert(found) {
                order.push(found);
            }
        }
    }
    let reach: BTreeMap<NominalSerial, BTreeSet<NominalSerial>> = order
        .iter()
        .map(|&serial| (serial, reached(&graph, serial)))
        .collect();
    let reaches = |from: NominalSerial, to: NominalSerial| {
        reach.get(&from).is_some_and(|above| above.contains(&to))
    };
    let named = |serial: NominalSerial| {
        graph
            .get(&serial)
            .map_or_else(|| block.name.clone(), |&(_, ref name)| name.clone())
    };
    let mut bounds: Vec<&(NominalSerial, BTreeSet<NominalSerial>)> = Vec::new();
    let mut bounding: BTreeSet<NominalSerial> = BTreeSet::new();
    let mut joins: Vec<NominalSerial> = Vec::new();
    for (index, &one) in order.iter().enumerate() {
        for &other in order.get(index.saturating_add(1) ..).unwrap_or_default() {
            if reaches(one, other) || reaches(other, one) {
                continue;
            }
            bounds.clear();
            bounds.extend(
                candidates
                    .iter()
                    .filter(|&&(_, ref above)| above.contains(&one) && above.contains(&other)),
            );
            bounding.clear();
            bounding.extend(bounds.iter().map(|&&(serial, _)| serial));
            joins.clear();
            joins.extend(
                bounds
                    .iter()
                    .filter(|&&&(serial, ref above)| {
                        above.intersection(&bounding).all(|&lower| lower == serial)
                    })
                    .map(|&&(serial, _)| serial),
            );
            if joins.len() > 1 && joins.last() == Some(&block.serial) {
                return Some(JoinFault {
                    pair: [named(one), named(other)],
                    joins: joins.iter().copied().map(named).collect(),
                });
            }
        }
    }
    None
}
