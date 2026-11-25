//! The overlaps of two diagrams: every way two wirings glue along a non-empty
//! set of shared generators into one diagram still inside the monogamous
//! acyclic fragment. Read at two rules' left-hand sides, each overlap is a
//! pre-critical pair of convex rewriting with interfaces: both sides embed
//! into its peak, and together they cover it. For a left-connected system —
//! left-linear, every rule an ma-rule, every left-hand side strongly
//! connected, which every spine reading of a linear pattern is — local
//! confluence follows from the joinability of these pairs (part III of the
//! series below, cor. 5.1).
//!
//! # Items
//!
//! [`overlaps`] enumerates the family of one ordered pair of wirings, and an
//! [`Overlap`] is one member: its peak, where each side's generators and
//! wires landed in it, and its [`OverlapShape`].
//!
//! Monogamy makes a gluing choice-free once one pair of generators is
//! identified. A shared wire both sides produce has its two producers
//! identified, port for port, or the diagram would combine two producers; a
//! shared wire both sides consume, its two consumers. One seed — a pair of
//! generators of one label — therefore determines its whole connected
//! overlap, and the family is the distinct overlaps the seeds reach whose
//! glued diagram [`Wiring::assemble`] admits.
//!
//! # Boundaries
//!
//! Only connected overlaps are enumerated: two shared regions no shared wire
//! joins are two seeds' overlaps, never one. Over trees, which every spine
//! reading of one cut is, gluing two such regions at once closes a directed
//! cycle, so nothing is lost there; a left-hand side with several outputs is
//! where a union of regions would be a pair of its own.
//!
//! A diagram asked against itself reaches the identity gluing, the trivially
//! joinable pair whose two contractions coincide. A caller reading one rule
//! against itself skips it, as the term enumerator skips a cell's overlap
//! with itself at the root.
//!
//! A rewriting that matches only where an anchor wire lands, as a command
//! rewrites only at the cut [`crate::read_spine`] names, keeps the overlaps
//! whose [`Overlap::right_wire`] sends the right side's anchor onto the left's;
//! the rest embed a side where that rewriting rewrites nothing.
//!
//! # Witnesses
//!
//! - `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
//! - `overlap::tests::a_cancellation_overlaps_its_inverse_below_the_root`
//! - `overlap::tests::a_shared_region_that_would_copy_a_wire_is_no_overlap`
//! - `overlap::tests::a_gluing_that_closes_a_cycle_is_no_overlap`
//! - `overlap::tests::a_side_inside_the_other_is_an_inclusion`
//!
//! # References
//!
//! - Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and
//!   Fabio Zanasi. "String Diagram Rewrite Theory III: Confluence with and
//!   without Frobenius." _Mathematical Structures in Computer Science_ 32, 7
//!   (2022), pages 829–869. `doi:10.1017/S0960129522000123`; preprint
//!   `arXiv:2109.06049` — pre-critical pairs with interfaces, left-connected
//!   systems, and cor. 5.1: a terminating left-connected system is confluent
//!   exactly when its pre-critical pairs are joinable.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::interface::Edge;
use crate::interface::EdgeCount;
use crate::interface::Generator;
use crate::interface::Interface;
use crate::interface::Wire;
use crate::interface::WireCount;
use crate::interface::Wiring;

/// How an overlap's shared generators sit in its two sides.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OverlapShape
{
    /// Every generator of both sides is shared: the two sides are one
    /// diagram glued onto itself.
    Coincident,
    /// Every generator of the left side is shared, and the right keeps one
    /// more: the left side stands inside the right.
    LeftIncluded,
    /// Every generator of the right side is shared, and the left keeps one
    /// more: the right side stands inside the left.
    RightIncluded,
    /// Each side keeps a generator the other does not hold.
    Regular,
}

/// One overlap of two diagrams: the peak they glue into and where each
/// side's generators landed in it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Overlap
{
    /// The glued diagram.
    peak: Wiring,
    /// Each right generator's position in the peak, by right position.
    right: Box<[Edge]>,
    /// Each right wire's number in the peak, by right number.
    right_wires: Box<[Wire]>,
    /// How many generators the two sides share.
    shared: EdgeCount,
    /// How the shared generators sit in the two sides.
    shape: OverlapShape,
}

impl Overlap
{
    /// The glued diagram both sides embed into and together cover.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn peak(&self) -> &Wiring
    {
        &self.peak
    }

    /// Where the right generator at `edge` landed in the peak. The left side's
    /// generators keep their positions: the peak lists them first.
    ///
    /// # Specification
    /// - provides: absent when `edge` is at or past the right side's generator
    ///   count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared generator lands on its left partner and a
    ///   kept one past the left side's generators.
    /// - witness: `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
    #[spec(ensures: |ret| ret.is_none_or(|image| usize::from(image) < self.peak.generators().len()))]
    #[inline]
    #[must_use]
    pub fn right_image(
        &self,
        edge: Edge,
    ) -> Option<Edge>
    {
        self.right.get(usize::from(edge)).copied()
    }

    /// Where the right wire `wire` landed in the peak. The left side's wires
    /// keep their numbers, so a right wire glued to a left one lands on it.
    ///
    /// # Specification
    /// - provides: absent when `wire` is at or past the right side's wire
    ///   count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a glued wire lands on its left partner and a kept one
    ///   past the left side's wires.
    /// - witness: `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
    #[spec(ensures: |ret| ret.is_none_or(|image| usize::from(image) < usize::from(self.peak.wire_count())))]
    #[inline]
    #[must_use]
    pub fn right_wire(
        &self,
        wire: Wire,
    ) -> Option<Wire>
    {
        self.right_wires.get(usize::from(wire)).copied()
    }

    /// How many generators the two sides share.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shared(&self) -> EdgeCount
    {
        self.shared
    }

    /// How the shared generators sit in the two sides.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shape(&self) -> OverlapShape
    {
        self.shape
    }
}

/// Whether an identification still holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fit
{
    /// Every identification so far is consistent.
    Agrees,
    /// An identification contradicts one already made, or pairs two
    /// generators of different labels or arities.
    Clashes,
}

/// One seed's identification of right generators and wires with left ones,
/// cleared between seeds.
#[derive(Debug, Default)]
struct Gluing
{
    /// Right generator to its left partner.
    edges: BTreeMap<Edge, Edge>,
    /// The left generators already partnered, which keeps the map injective.
    claimed: BTreeSet<Edge>,
    /// Right wire to its left partner.
    wires: BTreeMap<Wire, Wire>,
    /// The left wires already partnered.
    taken: BTreeSet<Wire>,
    /// Partnered generators whose ports are still to be partnered.
    pending: Vec<(Edge, Edge)>,
}

impl Gluing
{
    /// Forget every identification.
    ///
    /// # Specification
    /// trivial.
    fn clear(&mut self)
    {
        self.edges.clear();
        self.claimed.clear();
        self.wires.clear();
        self.taken.clear();
        self.pending.clear();
    }

    /// Partner the right generator `right_edge` with the left one
    /// `left_edge`.
    ///
    /// # Specification
    /// - ensures: [`Fit::Agrees`] when the two were already partners, or when
    ///   neither had one and they carry one label and one arity, in which case
    ///   they are partnered and queued; [`Fit::Clashes`] otherwise, the
    ///   identification unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a seed of two labels, and a forced partner already
    ///   taken, each clash.
    /// - witness: `overlap::tests::a_shared_region_that_would_copy_a_wire_is_no_overlap`
    #[spec(ensures: |ret| ret == Fit::Clashes || self.edges.get(&right_edge) == Some(&left_edge))]
    fn partner_edges(
        &mut self,
        (left, right): (&Wiring, &Wiring),
        left_edge: Edge,
        right_edge: Edge,
    ) -> Fit
    {
        if let Some(&partner) = self.edges.get(&right_edge) {
            return if partner == left_edge {
                Fit::Agrees
            }
            else {
                Fit::Clashes
            };
        }
        if self.claimed.contains(&left_edge) {
            return Fit::Clashes;
        }
        let (Maybe::Present(on_left), Maybe::Present(on_right)) =
            (left.generator(left_edge), right.generator(right_edge))
        else {
            return Fit::Clashes;
        };
        if on_left.label() != on_right.label()
            || on_left.sources().len() != on_right.sources().len()
            || on_left.targets().len() != on_right.targets().len()
        {
            return Fit::Clashes;
        }
        let _fresh = self.edges.insert(right_edge, left_edge);
        let _claimed = self.claimed.insert(left_edge);
        self.pending.push((left_edge, right_edge));
        Fit::Agrees
    }

    /// Partner the right wire `right_wire` with the left one `left_wire`, and
    /// the two wires' producers and consumers where both sides have one.
    ///
    /// # Specification
    /// - ensures: [`Fit::Agrees`] when the two were already partners, or when
    ///   neither had one and partnering the producers both sides have, and the
    ///   consumers both sides have, agrees; [`Fit::Clashes`] otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wire whose two consumers differ in label clashes,
    ///   which is the copy monogamy refuses.
    /// - witness: `overlap::tests::a_shared_region_that_would_copy_a_wire_is_no_overlap`
    #[spec(ensures: |ret| ret == Fit::Clashes || self.wires.get(&right_wire) == Some(&left_wire))]
    fn partner_wires(
        &mut self,
        sides: (&Wiring, &Wiring),
        left_wire: Wire,
        right_wire: Wire,
    ) -> Fit
    {
        if let Some(&partner) = self.wires.get(&right_wire) {
            return if partner == left_wire {
                Fit::Agrees
            }
            else {
                Fit::Clashes
            };
        }
        if !self.taken.insert(left_wire) {
            return Fit::Clashes;
        }
        let _fresh = self.wires.insert(right_wire, left_wire);
        let (left, right) = sides;
        if let (Maybe::Present(on_left), Maybe::Present(on_right)) =
            (left.producer_of(left_wire), right.producer_of(right_wire))
            && self.partner_edges(sides, on_left, on_right) == Fit::Clashes
        {
            return Fit::Clashes;
        }
        if let (Maybe::Present(on_left), Maybe::Present(on_right)) =
            (left.consumer_of(left_wire), right.consumer_of(right_wire))
            && self.partner_edges(sides, on_left, on_right) == Fit::Clashes
        {
            return Fit::Clashes;
        }
        Fit::Agrees
    }

    /// Grow the identification from the seed `(left_edge, right_edge)` until
    /// every partnered generator's ports are partnered.
    ///
    /// # Specification
    /// - ensures: [`Fit::Agrees`] exactly when the forced identifications are
    ///   consistent; the queue is then empty, and every partnered generator's
    ///   sources and targets are partnered port for port.
    /// - panics: none.
    ///
    /// # Termination
    /// A generator is queued once, when it is first partnered, and each round
    /// takes one from the queue; the two sides hold finitely many.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a seed on two calls grows over their arguments, and a
    ///   seed below the root grows up to it.
    /// - witness: `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
    /// - witness: `overlap::tests::a_cancellation_overlaps_its_inverse_below_the_root`
    #[spec(ensures: |ret| ret == Fit::Clashes || self.pending.is_empty())]
    fn grow(
        &mut self,
        sides: (&Wiring, &Wiring),
        left_edge: Edge,
        right_edge: Edge,
    ) -> Fit
    {
        if self.partner_edges(sides, left_edge, right_edge) == Fit::Clashes {
            return Fit::Clashes;
        }
        let (left, right) = sides;
        while let Some((on_left, on_right)) = self.pending.pop() {
            let (Maybe::Present(left_generator), Maybe::Present(right_generator)) =
                (left.generator(on_left), right.generator(on_right))
            else {
                return Fit::Clashes;
            };
            let ports = left_generator
                .sources()
                .iter()
                .zip(right_generator.sources())
                .chain(
                    left_generator
                        .targets()
                        .iter()
                        .zip(right_generator.targets()),
                );
            for (&left_wire, &right_wire) in ports {
                if self.partner_wires(sides, left_wire, right_wire) == Fit::Clashes {
                    return Fit::Clashes;
                }
            }
        }
        Fit::Agrees
    }
}

/// The peak a consistent identification glues: the left side's generators and
/// wires first, then the right side's unpartnered ones.
///
/// # Specification
/// - requires: `gluing` is a consistent identification of `right` into `left`.
/// - ensures: the overlap whose peak lists the left generators at their own
///   positions, then each unpartnered right generator in right order, its wires
///   renumbered past the left side's; whose inputs and outputs are the left
///   side's open ports the gluing leaves open, then the right side's, in their
///   own orders; or absent when [`Wiring::assemble`] refuses the peak.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an overlap at a shared frame, one below the root, an
///   inclusion, and a gluing that closes a cycle (absent).
/// - witness: `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
/// - witness: `overlap::tests::a_gluing_that_closes_a_cycle_is_no_overlap`
/// - witness: `overlap::tests::a_side_inside_the_other_is_an_inclusion`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|overlap| overlap.right.len() == right.generators().len()
    && overlap.right_wires.len() == usize::from(right.wire_count())
    && usize::from(overlap.shared) == gluing.edges.len()))]
fn glued(
    left: &Wiring,
    right: &Wiring,
    gluing: &Gluing,
) -> Option<Overlap>
{
    let left_wires = usize::from(left.wire_count());
    let mut fresh = left_wires;
    let renamed: Vec<Wire> = right
        .wire_count()
        .wires()
        .map(|wire| {
            gluing.wires.get(&wire).copied().unwrap_or_else(|| {
                let next = Wire::from(fresh);
                fresh = fresh.saturating_add(1);
                next
            })
        })
        .collect();
    let rename = |wire: &Wire| renamed.get(usize::from(*wire)).copied().unwrap_or(*wire);
    let mut generators = left.generators().to_vec();
    let mut images = Vec::with_capacity(right.generators().len());
    for (position, generator) in right.generators().iter().enumerate() {
        if let Some(&partner) = gluing.edges.get(&Edge::from(position)) {
            images.push(partner);
            continue;
        }
        images.push(Edge::from(generators.len()));
        generators.push(renamed_generator(generator, &rename));
    }
    let open = |wires: &[Wire], on_left: bool| -> Vec<Wire> {
        wires
            .iter()
            .map(|wire| if on_left { *wire } else { rename(wire) })
            .collect()
    };
    let mut inputs = open(left.boundary().inputs(), true);
    inputs.extend(open(right.boundary().inputs(), false));
    let mut outputs = open(left.boundary().outputs(), true);
    outputs.extend(open(right.boundary().outputs(), false));
    let produced: BTreeSet<Wire> = generators
        .iter()
        .flat_map(|generator| generator.targets().iter().copied())
        .collect();
    let consumed: BTreeSet<Wire> = generators
        .iter()
        .flat_map(|generator| generator.sources().iter().copied())
        .collect();
    let mut seen: BTreeSet<Wire> = BTreeSet::new();
    inputs.retain(|wire| !produced.contains(wire) && seen.insert(*wire));
    seen.clear();
    outputs.retain(|wire| !consumed.contains(wire) && seen.insert(*wire));
    let peak = Wiring::assemble(
        WireCount::from(fresh),
        generators,
        Interface::new(inputs, outputs),
    )
    .ok()?;
    let shared = gluing.edges.len();
    let shape = match (
        shared == left.generators().len(),
        shared == right.generators().len(),
    ) {
        (true, true) => OverlapShape::Coincident,
        (true, false) => OverlapShape::LeftIncluded,
        (false, true) => OverlapShape::RightIncluded,
        (false, false) => OverlapShape::Regular,
    };
    Some(Overlap {
        peak,
        right: images.into_boxed_slice(),
        right_wires: renamed.into_boxed_slice(),
        shared: EdgeCount::from(shared),
        shape,
    })
}

/// `generator` with every port renamed by `rename`.
///
/// # Specification
/// trivial.
fn renamed_generator(
    generator: &Generator,
    rename: &impl Fn(&Wire) -> Wire,
) -> Generator
{
    Generator::new(
        generator.label().clone(),
        generator
            .sources()
            .iter()
            .map(rename)
            .collect::<Box<[Wire]>>(),
        generator
            .targets()
            .iter()
            .map(rename)
            .collect::<Box<[Wire]>>(),
    )
}

/// Every connected overlap of `left` and `right`: each distinct gluing one
/// pair of like-labelled generators forces whose peak the fragment admits.
///
/// # Specification
/// - ensures: one overlap per distinct identification, in the order its first
///   seed is met — left generators outer, right inner, both ascending; every
///   overlap shares at least one generator, and its peak is a [`Wiring`].
/// - panics: none.
/// - intension: a seed already inside a found overlap is skipped, since it
///   forces that overlap again.
///
/// # Termination
/// The seeds are the finitely many pairs of the two sides' generators, and
/// each seed's growth terminates ([`Gluing::grow`]).
///
/// # Adequacy
/// - hypothesis: L3 — two calls of one operation overlap once at their frame; a
///   cancellation and its inverse overlap twice below their roots; a shared
///   argument whose consumers differ, and a gluing that closes a cycle, are no
///   overlap; one side inside the other is an inclusion.
/// - witness: `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
/// - witness: `overlap::tests::a_cancellation_overlaps_its_inverse_below_the_root`
/// - witness: `overlap::tests::a_shared_region_that_would_copy_a_wire_is_no_overlap`
/// - witness: `overlap::tests::a_gluing_that_closes_a_cycle_is_no_overlap`
/// - witness: `overlap::tests::a_side_inside_the_other_is_an_inclusion`
#[spec(ensures: |ret| ret.iter().all(|overlap| usize::from(overlap.shared) > 0_usize
    && overlap.right.len() == right.generators().len()))]
#[inline]
#[must_use]
pub fn overlaps(
    left: &Wiring,
    right: &Wiring,
) -> Vec<Overlap>
{
    let mut found = Vec::new();
    let mut reached: BTreeSet<(Edge, Edge)> = BTreeSet::new();
    let mut gluing = Gluing::default();
    let seeds = (0 .. left.generators().len()).flat_map(|on_left| {
        (0 .. right.generators().len())
            .map(move |on_right| (Edge::from(on_left), Edge::from(on_right)))
    });
    for (on_left, on_right) in seeds {
        if reached.contains(&(on_left, on_right)) {
            continue;
        }
        gluing.clear();
        if gluing.grow((left, right), on_left, on_right) == Fit::Clashes {
            continue;
        }
        let Some(overlap) = glued(left, right, &gluing)
        else {
            continue;
        };
        reached.extend(
            gluing
                .edges
                .iter()
                .map(|(&right_edge, &left_edge)| (left_edge, right_edge)),
        );
        found.push(overlap);
    }
    found
}

#[cfg(test)]
mod tests;
