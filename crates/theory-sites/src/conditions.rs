//! The generalized Reedy conditions, and the site's other finite
//! properties, run over a catalogue.
//!
//! Each condition walks its cases least total size first and stops at the
//! first failure, which is then the smallest counter-example at the bound.
//! A failing outcome carries its counter-example, and each condition's
//! postcondition checks that the counter-example refutes it.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;

use crate::catalogue::Catalogue;
use crate::degree::Degree;
use crate::map::Invertibility;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::outcome::CaseCount;
use crate::outcome::Chain;
use crate::outcome::MapCase;
use crate::outcome::Outcome;
use crate::outcome::Tally;
use crate::outcome::Verdict;
use crate::shape::Shape;
use crate::shape::WireKind;

wrapper! {
    /// A shape's position in a site.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    struct Node(usize);
}

/// One map of the site, sorted into its classes.
#[derive(Clone, Copy, Debug)]
struct Arrow<'catalogue>
{
    /// The map.
    map: &'catalogue SiteMap,
    /// Whether it is in the raising class.
    raising: Membership,
    /// Whether it is in the lowering class.
    lowering: Membership,
    /// Whether it is an isomorphism.
    invertibility: Invertibility,
}

/// A catalogue as a category: its shapes, and the maps between them sorted
/// into the raising and the lowering class.
///
/// # Specification
/// - ensures: one node per catalogue shape in catalogue order, and every map of
///   every hom set, each carrying [`SiteMap::raising`], [`SiteMap::lowering`]
///   and [`SiteMap::invertibility`] against its target.
/// - provides: the category every condition quantifies over.
/// - panics: none.
/// - executable: none — a type carries no runtime predicate; the constructor's
///   postcondition checks the node and map counts.
///
/// # Adequacy
/// - hypothesis: L2 — the conditions' case counts are related to the
///   catalogue's shape and hom counts, so a lost node or map changes a count.
/// - witness: `tests::reedy::the_class_is_a_category_with_two_classes`
#[derive(Clone, Debug)]
pub struct Site<'catalogue>
{
    /// The shapes, in catalogue order.
    nodes: Vec<&'catalogue Shape>,
    /// The maps, row-major by source and target node.
    arrows: Vec<Vec<Arrow<'catalogue>>>,
    /// Every ordered pair of nodes, least total size first.
    pairs: Vec<(Node, Node)>,
}

impl<'catalogue> Site<'catalogue>
{
    /// The site of `catalogue`.
    ///
    /// # Specification
    /// - ensures: as the type states; the pairs are ordered by total size, then
    ///   by source and target node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as the type.
    /// - witness: `tests::reedy::the_class_is_a_category_with_two_classes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref site| [
        site.nodes.len() == catalogue.shapes().len(),
        site.arrows.len() == site.nodes.len().saturating_mul(site.nodes.len()),
        site.pairs.len() == site.arrows.len(),
        site.arrows.iter().flatten().all(|arrow| arrow.raising == arrow.map.raising()),
    ])]
    pub fn new(catalogue: &'catalogue Catalogue) -> Self
    {
        let nodes: Vec<&Shape> = catalogue.shapes().iter().collect();
        let mut arrows: Vec<Vec<Arrow<'catalogue>>> =
            Vec::with_capacity(nodes.len().saturating_mul(nodes.len()));
        for (source_index, _) in catalogue.entries() {
            for (target_index, target) in catalogue.entries() {
                let maps = match catalogue.maps(source_index, target_index) {
                    | quenchant_shape::shape::Maybe::Present(maps) => maps,
                    | quenchant_shape::shape::Maybe::Absent(_) => &[],
                };
                arrows.push(
                    maps.iter()
                        .map(|map| Arrow {
                            map,
                            raising: map.raising(),
                            lowering: map.lowering(target),
                            invertibility: map.invertibility(target),
                        })
                        .collect(),
                );
            }
        }
        let mut pairs: Vec<(Node, Node)> = Vec::with_capacity(arrows.len());
        for source in 0 .. nodes.len() {
            for target in 0 .. nodes.len() {
                pairs.push((Node(source), Node(target)));
            }
        }
        pairs.sort_by_key(|pair| {
            let size = |node: Node| {
                nodes
                    .get(node.0)
                    .map_or(0, |shape| usize::from(shape.size()))
            };
            (size(pair.0).saturating_add(size(pair.1)), pair.0, pair.1)
        });
        Self {
            nodes,
            arrows,
            pairs,
        }
    }

    /// How many maps the site holds.
    ///
    /// # Specification
    /// trivial.
    fn map_count(&self) -> CaseCount
    {
        CaseCount::from(
            self.arrows
                .iter()
                .map(Vec::len)
                .fold(0_usize, usize::saturating_add),
        )
    }

    /// How many shapes the site holds.
    ///
    /// # Specification
    /// trivial.
    fn node_count(&self) -> CaseCount
    {
        CaseCount::from(self.nodes.len())
    }

    /// The maps from `source` to `target`, empty past the nodes.
    ///
    /// # Specification
    /// trivial.
    fn arrows(
        &self,
        source: Node,
        target: Node,
    ) -> &[Arrow<'catalogue>]
    {
        let position = source
            .0
            .saturating_mul(self.nodes.len())
            .saturating_add(target.0);
        self.arrows.get(position).map_or(&[], Vec::as_slice)
    }

    /// The case naming `map` between two nodes.
    ///
    /// # Specification
    /// trivial.
    fn case(
        &self,
        (source, target): (Node, Node),
        map: &SiteMap,
    ) -> MapCase
    {
        let shape = |node: Node| {
            self.nodes
                .get(node.0)
                .map_or_else(Shape::default, |shape| (*shape).clone())
        };
        MapCase::new(shape(source), shape(target), map.clone())
    }

    /// Every ordered triple of nodes, least total size first.
    ///
    /// # Specification
    /// trivial.
    fn triples(&self) -> Vec<(Node, Node, Node)>
    {
        let count = self.nodes.len();
        let size = |node: Node| {
            self.nodes
                .get(node.0)
                .map_or(0, |shape| usize::from(shape.size()))
        };
        let mut triples: Vec<(Node, Node, Node)> = Vec::new();
        for first in 0 .. count {
            for second in 0 .. count {
                for third in 0 .. count {
                    triples.push((Node(first), Node(second), Node(third)));
                }
            }
        }
        triples.sort_by_key(|triple| {
            let total = size(triple.0)
                .saturating_add(size(triple.1))
                .saturating_add(size(triple.2));
            (total, triple.0, triple.1, triple.2)
        });
        triples
    }

    /// The map equal to `map` from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    fn find(
        &self,
        (source, target): (Node, Node),
        map: &SiteMap,
    ) -> Option<&Arrow<'catalogue>>
    {
        let arrows = self.arrows(source, target);
        let position = arrows.binary_search_by(|arrow| arrow.map.cmp(map)).ok()?;
        arrows.get(position)
    }

    /// The identity arrow of a node.
    ///
    /// # Specification
    /// trivial.
    fn identity(
        &self,
        node: Node,
    ) -> Option<SiteMap>
    {
        self.nodes.get(node.0).map(|shape| SiteMap::identity(shape))
    }
}

/// Which maps a closure check composes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Part
{
    /// Every map.
    Whole,
    /// The raising maps.
    Raising,
    /// The lowering maps.
    Lowering,
}

impl Part
{
    /// Whether `arrow` is in the part.
    ///
    /// # Specification
    /// trivial.
    const fn holds(
        self,
        arrow: &Arrow<'_>,
    ) -> Membership
    {
        match self {
            | Self::Whole => Membership::Inside,
            | Self::Raising => arrow.raising,
            | Self::Lowering => arrow.lowering,
        }
    }

    /// Whether `map`, read against `target`, is in the part.
    ///
    /// # Specification
    /// trivial.
    fn admits(
        self,
        map: &SiteMap,
        target: &Shape,
    ) -> Membership
    {
        match self {
            | Self::Whole => Membership::Inside,
            | Self::Raising => map.raising(),
            | Self::Lowering => map.lowering(target),
        }
    }
}

/// Whether composites of composable maps in `part` are maps in `part`.
///
/// # Specification
/// - ensures: holds exactly when for every triple of shapes and every `f`, `g`
///   in `part`, `g ∘ f` is a map of the class and lies in `part`; otherwise
///   fails at the first such pair, whose composite does not compose, is no map
///   or leaves `part`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome for each part is pinned at the bound with its
///   case count; L3 — the counter-example check rejects a witness whose
///   composite stays in the part.
/// - witness: `tests::reedy::the_class_is_a_category_with_two_classes`
/// - witness: `tests::maps::the_class_is_a_category_at_the_bound`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => match (witness.links().first(), witness.links().get(1)) {
        (Some(first), Some(second)) => first.map().then(second.map()).map_or(true, |composite| {
            composite.validate(first.source(), second.target()).is_err()
                || part.admits(&composite, second.target()) == Membership::Outside
        }),
        _ => false,
    },
})]
pub fn closure(
    site: &Site<'_>,
    part: Part,
) -> Outcome<Chain>
{
    let mut tally = Tally::default();
    for (first, second, third) in site.triples() {
        for left in site
            .arrows(first, second)
            .iter()
            .filter(|arrow| part.holds(arrow) == Membership::Inside)
        {
            for right in site
                .arrows(second, third)
                .iter()
                .filter(|arrow| part.holds(arrow) == Membership::Inside)
            {
                tally.count();
                let closed = left
                    .map
                    .then(right.map)
                    .ok()
                    .and_then(|composite| site.find((first, third), &composite))
                    .is_some_and(|arrow| part.holds(arrow) == Membership::Inside);
                if !closed {
                    return tally.fails(Chain::new(vec![
                        site.case((first, second), left.map),
                        site.case((second, third), right.map),
                    ]));
                }
            }
        }
    }
    tally.holds()
}

/// Whether every shape's identity is in both classes, invertible, and a unit
/// for composition on both sides.
///
/// # Specification
/// - ensures: holds exactly when each identity is a raising, lowering and
///   invertible map, and composing it before or after any map gives that map,
///   after one case per shape and one per map; the first failing map otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per shape and one per
///   map, are pinned at the bound.
/// - witness: `tests::reedy::the_class_is_a_category_with_two_classes`
/// - witness: `tests::maps::the_class_is_a_category_at_the_bound`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => usize::from(cases) == usize::from(site.node_count()).saturating_add(usize::from(site.map_count())),
    Outcome::Fails { ref witness, .. } => {
        let before = SiteMap::identity(witness.source());
        let after = SiteMap::identity(witness.target());
        before.then(witness.map()).as_ref() != Ok(witness.map())
            || witness.map().then(&after).as_ref() != Ok(witness.map())
            || (*witness.map() == before && (witness.map().raising() == Membership::Outside
                || witness.map().lowering(witness.target()) == Membership::Outside))
    },
})]
pub fn identities(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let (Some(before), Some(after)) = (site.identity(source), site.identity(target))
        else {
            continue;
        };
        if source == target {
            tally.count();
            let kept = site.find((source, source), &before).is_some_and(|arrow| {
                arrow.raising == Membership::Inside
                    && arrow.lowering == Membership::Inside
                    && arrow.invertibility == Invertibility::Invertible
            });
            if !kept {
                return tally.fails(site.case((source, source), &before));
            }
        }
        for arrow in site.arrows(source, target) {
            tally.count();
            let unit = before.then(arrow.map).is_ok_and(|map| map == *arrow.map)
                && arrow.map.then(&after).is_ok_and(|map| map == *arrow.map);
            if !unit {
                return tally.fails(site.case((source, target), arrow.map));
            }
        }
    }
    tally.holds()
}

/// Whether the maps in both classes are exactly the isomorphisms.
///
/// # Specification
/// - ensures: holds exactly when every map is raising and lowering if and only
///   if it is invertible, after one case per map; the first failing map
///   otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per map, are pinned
///   at the bound.
/// - witness: `tests::reedy::the_class_is_a_category_with_two_classes`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == site.map_count(),
    Outcome::Fails { ref witness, .. } => (witness.map().raising() == Membership::Inside
        && witness.map().lowering(witness.target()) == Membership::Inside)
        != (witness.map().invertibility(witness.target()) == Invertibility::Invertible),
})]
pub fn intersection(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        for arrow in site.arrows(source, target) {
            tally.count();
            let both = arrow.raising == Membership::Inside && arrow.lowering == Membership::Inside;
            if both != (arrow.invertibility == Invertibility::Invertible) {
                return tally.fails(site.case((source, target), arrow.map));
            }
        }
    }
    tally.holds()
}

/// Whether the class's own isomorphisms are its maps with two-sided
/// inverses.
///
/// # Specification
/// - ensures: holds exactly when a map is [`Invertibility::Invertible`] if and
///   only if some map composes with it to both identities, after one case per
///   map; the first failing map otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per map, are pinned
///   at the bound.
/// - witness: `tests::maps::invertibility_matches_two_sided_inverses`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == site.map_count(),
    Outcome::Fails { ref witness, .. } => witness.map().validate(witness.source(), witness.target()).is_ok(),
})]
pub fn invertibility(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let (Some(left_unit), Some(right_unit)) = (site.identity(source), site.identity(target))
        else {
            continue;
        };
        for arrow in site.arrows(source, target) {
            tally.count();
            let inverse = site.arrows(target, source).iter().any(|back| {
                arrow.map.then(back.map).is_ok_and(|map| map == left_unit)
                    && back.map.then(arrow.map).is_ok_and(|map| map == right_unit)
            });
            if inverse != (arrow.invertibility == Invertibility::Invertible) {
                return tally.fails(site.case((source, target), arrow.map));
            }
        }
    }
    tally.holds()
}

/// Which maps a degree check constrains.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Scope
{
    /// Raising maps only: the direct-category reading.
    Raising,
    /// Raising and lowering maps: the generalized Reedy reading.
    Both,
}

/// Whether the degree orders the maps in `scope`.
///
/// # Specification
/// - ensures: holds exactly when every invertible map preserves the degree,
///   every other raising map strictly raises it, and, under [`Scope::Both`],
///   every other lowering map strictly lowers it; the first failing map
///   otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome under both scopes is pinned at the bound; L3
///   — a contraction raising the degree from one to three while keeping
///   vertices plus wires at three, and a deletion lowering it, are asserted
///   pointwise.
/// - witness: `tests::reedy::the_degree_orders_both_classes`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => {
        let (low, high) = (Degree::of(witness.source()), Degree::of(witness.target()));
        match witness.map().invertibility(witness.target()) {
            Invertibility::Invertible => low != high,
            Invertibility::NotInvertible if witness.map().raising() == Membership::Inside => low >= high,
            Invertibility::NotInvertible => scope == Scope::Both && high >= low,
        }
    },
})]
pub fn degree_order(
    site: &Site<'_>,
    scope: Scope,
) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let (Some(from), Some(to)) = (site.nodes.get(source.0), site.nodes.get(target.0))
        else {
            continue;
        };
        let (low, high) = (Degree::of(from), Degree::of(to));
        for arrow in site.arrows(source, target) {
            let ordered = match (arrow.invertibility, arrow.raising, arrow.lowering, scope) {
                | (Invertibility::Invertible, ..) => low == high,
                | (Invertibility::NotInvertible, Membership::Inside, ..) => low < high,
                | (
                    Invertibility::NotInvertible,
                    Membership::Outside,
                    Membership::Inside,
                    Scope::Both,
                ) => high < low,
                | (
                    Invertibility::NotInvertible,
                    Membership::Outside,
                    Membership::Inside,
                    Scope::Raising,
                )
                | (Invertibility::NotInvertible, Membership::Outside, Membership::Outside, _) => {
                    continue;
                },
            };
            tally.count();
            if !ordered {
                return tally.fails(site.case((source, target), arrow.map));
            }
        }
    }
    tally.holds()
}

/// Whether the point-free core is a direct category: every map between
/// shapes without points is raising, and strictly raises the degree unless
/// it is an isomorphism, which preserves it.
///
/// # Specification
/// - ensures: holds exactly when every map whose source and target have no
///   point is raising, preserves the degree when invertible and strictly raises
///   it otherwise; the first failing map otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome is pinned at the bound with its case count
///   related to the maps between point-free shapes; L3 — the point-free
///   contraction `C(1,1) → p→q` raises the degree from one to three.
/// - witness: `tests::reedy::the_point_free_core_is_direct`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => {
        let (low, high) = (Degree::of(witness.source()), Degree::of(witness.target()));
        usize::from(witness.source().point_count()) == 0
            && usize::from(witness.target().point_count()) == 0
            && (witness.map().raising() == Membership::Outside
                || match witness.map().invertibility(witness.target()) {
                    Invertibility::Invertible => low != high,
                    Invertibility::NotInvertible => low >= high,
                })
    },
})]
pub fn direct_core(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let (Some(from), Some(to)) = (site.nodes.get(source.0), site.nodes.get(target.0))
        else {
            continue;
        };
        if usize::from(from.point_count()) != 0 || usize::from(to.point_count()) != 0 {
            continue;
        }
        let (low, high) = (Degree::of(from), Degree::of(to));
        for arrow in site.arrows(source, target) {
            tally.count();
            let ordered = match arrow.invertibility {
                | Invertibility::Invertible => low == high,
                | Invertibility::NotInvertible => low < high,
            };
            if arrow.raising == Membership::Outside || !ordered {
                return tally.fails(site.case((source, target), arrow.map));
            }
        }
    }
    tally.holds()
}

/// Whether the latching category at each shape is finite.
///
/// Every non-invertible raising map `f : G → K` has at most as many vertices
/// as `K` and at most as many wires as `K` has wires plus inner wires.
///
/// # Specification
/// - ensures: holds exactly when every non-invertible raising map satisfies
///   both bounds; the first failing map otherwise. The bounds put the latching
///   category at `K` among the finitely many shapes of size at most `size(K) +
///   inner(K)`: images are non-empty and disjoint, and a target wire has at
///   most two preimages, an output leg and an input leg fused into an inner
///   wire, because no source has a stick.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome is pinned at the bound; L3 — `p ⊔ q → p→q`, a
///   source corolla and a sink corolla fused, meets the wire bound with
///   equality, so a strict bound fails it.
/// - witness: `tests::reedy::the_latching_category_is_finite`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => witness.map().raising() == Membership::Inside
        && witness.map().invertibility(witness.target()) == Invertibility::NotInvertible
        && (witness.source().vertex_count() > witness.target().vertex_count()
            || usize::from(witness.source().wire_count()) > usize::from(witness.target().wire_count())
                .saturating_add(usize::from(witness.target().count_of(WireKind::Inner)))),
})]
pub fn latching(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let (Some(from), Some(to)) = (site.nodes.get(source.0), site.nodes.get(target.0))
        else {
            continue;
        };
        let wire_room =
            usize::from(to.wire_count()).saturating_add(usize::from(to.count_of(WireKind::Inner)));
        let bounded =
            from.vertex_count() <= to.vertex_count() && usize::from(from.wire_count()) <= wire_room;
        for arrow in site.arrows(source, target).iter().filter(|arrow| {
            arrow.raising == Membership::Inside
                && arrow.invertibility == Invertibility::NotInvertible
        }) {
            tally.count();
            if !bounded {
                return tally.fails(site.case((source, target), arrow.map));
            }
        }
    }
    tally.holds()
}

/// How a map's factorization fails.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FactorizationDefect
{
    /// No lowering map followed by a raising map composes to it.
    Missing,
    /// Factorizations pass through middles of different classes.
    SeveralMiddles,
    /// Two factorizations are not related by an isomorphism of the middle.
    Unrelated,
    /// Two factorizations are related by more than one isomorphism.
    NotUniquelyRelated,
}

impl fmt::Display for FactorizationDefect
{
    /// Names the defect.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Missing => "no factorization",
            | Self::SeveralMiddles => "middles of different classes",
            | Self::Unrelated => "two factorizations not related by an isomorphism",
            | Self::NotUniquelyRelated => "two factorizations related by several isomorphisms",
        })
    }
}

/// A map whose factorization fails, and how.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FactorizationFailure
{
    /// The map.
    pub case: MapCase,
    /// How its factorization fails.
    pub defect: FactorizationDefect,
}

impl fmt::Display for FactorizationFailure
{
    /// Writes the defect and the map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}: {}", self.defect, self.case)
    }
}

/// One factorization: the middle node, the lowering map and the raising map.
type Factorization<'catalogue> = (Node, &'catalogue SiteMap, &'catalogue SiteMap);

/// Whether every map is a point deletion followed by a raising map, unique
/// up to a unique isomorphism of the middle.
///
/// # Specification
/// - ensures: holds exactly when every map `f : G → K` has a factorization `f =
///   r ∘ d` with `d` lowering and `r` raising, every factorization passes
///   through one middle class, and any two are related by exactly one
///   isomorphism `θ` of the middle with `θ ∘ d = d'` and `r' ∘ θ = r`, after
///   one case per map; the first failing map otherwise.
/// - panics: none.
/// - intension: for each pair, every composite of a lowering map out of the
///   source and a raising map into the target is bucketed by the composite.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per map, are pinned
///   at the bound; L3 — the endomorphism of `•` deleting and re-including its
///   point factors through `∅` and nowhere else.
/// - witness: `tests::reedy::every_map_factors_through_a_point_deletion`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == site.map_count(),
    Outcome::Fails { ref witness, .. } => witness.case.map().validate(witness.case.source(), witness.case.target()).is_ok(),
})]
pub fn factorization(site: &Site<'_>) -> Outcome<FactorizationFailure>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let buckets = factorizations(site, (source, target));
        for arrow in site.arrows(source, target) {
            tally.count();
            let found = buckets.get(arrow.map).map_or(&[][..], Vec::as_slice);
            if let Some(defect) = factorization_defect(site, found) {
                return tally.fails(FactorizationFailure {
                    case: site.case((source, target), arrow.map),
                    defect,
                });
            }
        }
    }
    tally.holds()
}

/// Every lowering-then-raising composite from `source` to `target`,
/// bucketed by the composite.
///
/// # Specification
/// trivial.
fn factorizations<'catalogue>(
    site: &Site<'catalogue>,
    (source, target): (Node, Node),
) -> BTreeMap<SiteMap, Vec<Factorization<'catalogue>>>
{
    let mut buckets: BTreeMap<SiteMap, Vec<Factorization<'catalogue>>> = BTreeMap::new();
    for middle in (0 .. site.nodes.len()).map(Node) {
        for lower in site
            .arrows(source, middle)
            .iter()
            .filter(|arrow| arrow.lowering == Membership::Inside)
        {
            for raise in site
                .arrows(middle, target)
                .iter()
                .filter(|arrow| arrow.raising == Membership::Inside)
            {
                if let Ok(composite) = lower.map.then(raise.map) {
                    buckets
                        .entry(composite)
                        .or_default()
                        .push((middle, lower.map, raise.map));
                }
            }
        }
    }
    buckets
}

/// What is wrong with a map's factorizations, if anything.
///
/// # Specification
/// - ensures: [`FactorizationDefect::Missing`] for none, then
///   [`FactorizationDefect::SeveralMiddles`] when two middles differ, then,
///   comparing each factorization with the first, the defect of the first with
///   no or several connecting automorphisms; nothing when every one is
///   connected by exactly one.
/// - panics: none.
/// - executable: none — the defect's meaning is relative to the site's
///   automorphism sets, which a predicate would recompute exactly as the body
///   does.
///
/// # Adequacy
/// - hypothesis: L2 — the factorization outcome at the bound, where a map with
///   two factorizations related by the automorphism of `•⊔•` swapping its
///   points must pass.
/// - witness: `tests::reedy::every_map_factors_through_a_point_deletion`
fn factorization_defect(
    site: &Site<'_>,
    found: &[Factorization<'_>],
) -> Option<FactorizationDefect>
{
    let Some(&(middle, first_lower, first_raise)) = found.first()
    else {
        return Some(FactorizationDefect::Missing);
    };
    if found.iter().any(|entry| entry.0 != middle) {
        return Some(FactorizationDefect::SeveralMiddles);
    }
    let automorphisms: Vec<&SiteMap> = site
        .arrows(middle, middle)
        .iter()
        .filter(|arrow| arrow.invertibility == Invertibility::Invertible)
        .map(|arrow| arrow.map)
        .collect();
    for &(_, lower, raise) in found {
        let connecting = automorphisms
            .iter()
            .filter(|theta| {
                first_lower.then(theta).is_ok_and(|map| map == *lower)
                    && theta.then(raise).is_ok_and(|map| map == *first_raise)
            })
            .count();
        match connecting {
            | 0 => return Some(FactorizationDefect::Unrelated),
            | 1 => {},
            | _ => return Some(FactorizationDefect::NotUniquelyRelated),
        }
    }
    None
}

/// Whether an automorphism fixing a lowering map is the identity: axiom
/// (iv) of a generalized Reedy category.
///
/// # Specification
/// - ensures: holds exactly when for every lowering `δ : G → K` and every
///   automorphism `θ` of `K` with `θ ∘ δ = δ`, `θ` is the identity; the first
///   failing `δ` and `θ` otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome is pinned at the bound; the counter-example
///   check rejects a witness whose automorphism is the identity or does not fix
///   the map.
/// - witness: `tests::reedy::both_rigidity_axioms_hold`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => match (witness.links().first(), witness.links().get(1)) {
        (Some(lower), Some(theta)) => lower.map().lowering(lower.target()) == Membership::Inside
            && *theta.map() != SiteMap::identity(theta.source())
            && lower.map().then(theta.map()).as_ref() == Ok(lower.map()),
        _ => false,
    },
})]
pub fn rigidity(site: &Site<'_>) -> Outcome<Chain>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let Some(unit) = site.identity(target)
        else {
            continue;
        };
        for lower in site
            .arrows(source, target)
            .iter()
            .filter(|arrow| arrow.lowering == Membership::Inside)
        {
            for theta in site.arrows(target, target) {
                if theta.invertibility != Invertibility::Invertible {
                    continue;
                }
                tally.count();
                let fixes = lower.map.then(theta.map).is_ok_and(|map| map == *lower.map);
                if fixes && *theta.map != unit {
                    return tally.fails(Chain::new(vec![
                        site.case((source, target), lower.map),
                        site.case((target, target), theta.map),
                    ]));
                }
            }
        }
    }
    tally.holds()
}

/// Whether an automorphism of a raising map's source that the map absorbs
/// is the identity: axiom (iv) of the opposite category, which a Reedy
/// structure on presheaves needs.
///
/// # Specification
/// - ensures: holds exactly when for every raising `f : G → K` and every
///   automorphism `θ` of `G` with `f ∘ θ = f`, `θ` is the identity; the first
///   failing `θ` and `f` otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome is pinned at the bound; the counter-example
///   check rejects a witness whose automorphism is the identity or is not
///   absorbed.
/// - witness: `tests::reedy::both_rigidity_axioms_hold`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => match (witness.links().first(), witness.links().get(1)) {
        (Some(theta), Some(raise)) => raise.map().raising() == Membership::Inside
            && *theta.map() != SiteMap::identity(theta.source())
            && theta.map().then(raise.map()).as_ref() == Ok(raise.map()),
        _ => false,
    },
})]
pub fn dual_rigidity(site: &Site<'_>) -> Outcome<Chain>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let Some(unit) = site.identity(source)
        else {
            continue;
        };
        for raise in site
            .arrows(source, target)
            .iter()
            .filter(|arrow| arrow.raising == Membership::Inside)
        {
            for theta in site.arrows(source, source) {
                if theta.invertibility != Invertibility::Invertible {
                    continue;
                }
                tally.count();
                let absorbed = theta.map.then(raise.map).is_ok_and(|map| map == *raise.map);
                if absorbed && *theta.map != unit {
                    return tally.fails(Chain::new(vec![
                        site.case((source, source), theta.map),
                        site.case((source, target), raise.map),
                    ]));
                }
            }
        }
    }
    tally.holds()
}

/// Whether every lowering map has a section.
///
/// # Specification
/// - ensures: holds exactly when every lowering `δ : G → K` has a map `s : K →
///   G` with `δ ∘ s` the identity of `K`; the first failing `δ` otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome is pinned at the bound; L3 — the codegeneracy
///   `• → ∅` is split by `∅ → •`, whose other composite is not the identity.
/// - witness: `tests::point_count::the_codegeneracy_is_split`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => witness.map().lowering(witness.target()) == Membership::Inside,
})]
pub fn split_lowering(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let Some(unit) = site.identity(target)
        else {
            continue;
        };
        for lower in site
            .arrows(source, target)
            .iter()
            .filter(|arrow| arrow.lowering == Membership::Inside)
        {
            tally.count();
            let split = site
                .arrows(target, source)
                .iter()
                .any(|section| section.map.then(lower.map).is_ok_and(|map| map == unit));
            if !split {
                return tally.fails(site.case((source, target), lower.map));
            }
        }
    }
    tally.holds()
}

/// The two pushout conditions' outcomes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PushoutOutcomes
{
    /// Whether every span of a raising map and a deletion has a pushout.
    pub existence: Outcome<Chain>,
    /// Whether, where the pushout exists, the pushed-out map is raising.
    pub stability: Outcome<Chain>,
}

/// One cocone over a span: its vertex and its two legs.
type Cocone<'catalogue> = (Node, &'catalogue SiteMap, &'catalogue SiteMap);

/// Whether a raising map pushes out along a deletion, and stays raising.
///
/// # Specification
/// - ensures: existence holds exactly when every span of a raising `f : A → B`
///   and a non-invertible lowering `δ : A → C` has a cocone `(P, g, h)` through
///   which every cocone at the bound factors by exactly one map; stability
///   holds exactly when, for every span with a pushout, the pushed-out `h : C →
///   P` is raising. Each fails at its first span.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — both outcomes are pinned at the bound, with the span
///   without a pushout pinned by its shapes; the counter-example check rejects
///   a span that is not a raising map beside a deletion.
/// - witness: `tests::reedy::a_closed_substitution_has_no_pushout_with_a_deletion`
#[inline]
#[must_use]
#[spec(ensures: |ref outcomes| [
    match outcomes.existence {
        Outcome::Holds { .. } => true,
        Outcome::Fails { ref witness, .. } => match (witness.links().first(), witness.links().get(1)) {
            (Some(raise), Some(deletion)) => raise.map().raising() == Membership::Inside
                && deletion.map().lowering(deletion.target()) == Membership::Inside
                && deletion.map().invertibility(deletion.target()) == Invertibility::NotInvertible
                && raise.source() == deletion.source(),
            _ => false,
        },
    },
    match outcomes.stability {
        Outcome::Holds { .. } => true,
        Outcome::Fails { ref witness, .. } => witness.links().get(2).is_some_and(|pushed| pushed.map().raising() == Membership::Outside),
    },
])]
pub fn pushouts(site: &Site<'_>) -> PushoutOutcomes
{
    let (mut spans, mut pushed) = (Tally::default(), Tally::default());
    let (mut existence, mut stability) = (None, None);
    for (apex, left, right) in site.triples() {
        let raising = site
            .arrows(apex, left)
            .iter()
            .filter(|arrow| arrow.raising == Membership::Inside);
        for raise in raising {
            let deletions = site.arrows(apex, right).iter().filter(|arrow| {
                arrow.lowering == Membership::Inside
                    && arrow.invertibility == Invertibility::NotInvertible
            });
            for deletion in deletions {
                spans.count();
                let span = || {
                    vec![
                        site.case((apex, left), raise.map),
                        site.case((apex, right), deletion.map),
                    ]
                };
                let cocones = cocones(site, (left, right), (raise.map, deletion.map));
                let Some(&(vertex, _, pushed_out)) = universal(site, &cocones)
                else {
                    if existence.is_none() {
                        existence = Some(spans.fails(Chain::new(span())));
                    }
                    continue;
                };
                pushed.count();
                let stays = site
                    .find((right, vertex), pushed_out)
                    .is_some_and(|arrow| arrow.raising == Membership::Inside);
                if !stays && stability.is_none() {
                    let mut links = span();
                    links.push(site.case((right, vertex), pushed_out));
                    stability = Some(pushed.fails(Chain::new(links)));
                }
            }
        }
    }
    PushoutOutcomes {
        existence: existence.unwrap_or_else(|| spans.holds()),
        stability: stability.unwrap_or_else(|| pushed.holds()),
    }
}

/// Every cocone at the bound over the span `(f, δ)` with feet `left` and
/// `right`.
///
/// # Specification
/// trivial.
fn cocones<'catalogue>(
    site: &Site<'catalogue>,
    (left, right): (Node, Node),
    (raise, deletion): (&SiteMap, &SiteMap),
) -> Vec<Cocone<'catalogue>>
{
    let mut found: Vec<Cocone<'catalogue>> = Vec::new();
    for vertex in (0 .. site.nodes.len()).map(Node) {
        for upper in site.arrows(left, vertex) {
            let Ok(through_left) = raise.then(upper.map)
            else {
                continue;
            };
            for lower in site.arrows(right, vertex) {
                if deletion
                    .then(lower.map)
                    .is_ok_and(|map| map == through_left)
                {
                    found.push((vertex, upper.map, lower.map));
                }
            }
        }
    }
    found
}

/// The first cocone every cocone factors through by exactly one map.
///
/// # Specification
/// trivial.
fn universal<'cocones, 'catalogue>(
    site: &Site<'catalogue>,
    cocones: &'cocones [Cocone<'catalogue>],
) -> Option<&'cocones Cocone<'catalogue>>
{
    cocones.iter().find(|candidate| {
        let &(vertex, upper, lower) = *candidate;
        cocones.iter().all(|other| {
            let &(target, other_upper, other_lower) = other;
            let mediating = site
                .arrows(vertex, target)
                .iter()
                .filter(|arrow| {
                    upper.then(arrow.map).is_ok_and(|map| map == *other_upper)
                        && lower.then(arrow.map).is_ok_and(|map| map == *other_lower)
                })
                .count();
            mediating == 1
        })
    })
}

/// Whether deletions out of each shape are addressed by their kernels.
///
/// # Specification
/// - ensures: holds exactly when, for every shape `G` with `p` points, the
///   kernels of the deletions out of `G` (non-invertible lowering maps) are
///   exactly the `2ᵖ − 1` non-empty sets of points, deletions with one kernel
///   share their target and differ by an automorphism of it, and a deletion
///   followed by a deletion is the deletion whose kernel is the union of the
///   first kernel with the preimage of the second, after one case per shape;
///   the first failing shape otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per shape, are pinned
///   at the bound; L3 — the shape of two points has three kernel classes.
/// - witness: `tests::point_count::deletions_are_addressed_by_kernels`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == site.node_count(),
    Outcome::Fails { ref witness, .. } => usize::from(witness.point_count()) > 0,
})]
pub fn deletion_classes(site: &Site<'_>) -> Outcome<Shape>
{
    let mut tally = Tally::default();
    for (index, shape) in site.nodes.iter().enumerate() {
        tally.count();
        if deletions_addressed(site, Node(index), shape) == Verdict::Fails {
            return tally.fails((*shape).clone());
        }
    }
    tally.holds()
}

/// Every deletion out of `source`, with its target.
///
/// # Specification
/// trivial.
fn deletions_out<'catalogue>(
    site: &Site<'catalogue>,
    source: Node,
) -> Vec<(Node, &'catalogue SiteMap)>
{
    (0 .. site.nodes.len())
        .map(Node)
        .flat_map(|target| {
            site.arrows(source, target)
                .iter()
                .filter(|arrow| {
                    arrow.lowering == Membership::Inside
                        && arrow.invertibility == Invertibility::NotInvertible
                })
                .map(move |arrow| (target, arrow.map))
        })
        .collect()
}

/// The three clauses of [`deletion_classes`] at one shape.
///
/// # Specification
/// - ensures: [`Verdict::Holds`] exactly when the deletions out of `shape` are
///   addressed by their kernels, related within a kernel by an automorphism,
///   and composed by uniting kernels, as [`deletion_classes`] states.
/// - panics: none.
/// - executable: none — the three clauses are the computation; a predicate
///   would repeat it, and the outcome's case count and pinned class count
///   observe it instead.
///
/// # Adequacy
/// - hypothesis: L2 — as [`deletion_classes`].
/// - witness: `tests::point_count::deletions_are_addressed_by_kernels`
fn deletions_addressed(
    site: &Site<'_>,
    source: Node,
    shape: &Shape,
) -> Verdict
{
    let points = shape
        .points()
        .into_iter()
        .fold(VertexSet::EMPTY, |set, point| {
            set.union(VertexSet::single(point))
        });
    let deletions = deletions_out(site, source);
    let mut classes: BTreeMap<VertexSet, Vec<(Node, &SiteMap)>> = BTreeMap::new();
    for &(target, map) in &deletions {
        classes.entry(map.kernel()).or_default().push((target, map));
    }
    let subsets = 1_usize
        .checked_shl(u32::try_from(usize::from(shape.point_count())).unwrap_or(u32::MAX))
        .unwrap_or(0);
    let addressed = classes.len().saturating_add(1) == subsets
        && classes.keys().all(|kernel| {
            *kernel != VertexSet::EMPTY && kernel.without(points) == VertexSet::EMPTY
        });
    let related = classes.values().all(|class| {
        let Some(&(target, first)) = class.first()
        else {
            return false;
        };
        class.iter().all(|&(other_target, other)| {
            other_target == target
                && site.arrows(target, target).iter().any(|theta| {
                    theta.invertibility == Invertibility::Invertible
                        && first.then(theta.map).is_ok_and(|map| map == *other)
                })
        })
    });
    let unions = deletions.iter().all(|&(middle, first)| {
        deletions_out(site, middle).iter().all(|&(target, second)| {
            let preimage = (0 .. first.images().len()).map(Edge::from).fold(
                VertexSet::EMPTY,
                |set, vertex| {
                    let image = first.image(vertex);
                    if image != VertexSet::EMPTY
                        && image.without(second.kernel()) == VertexSet::EMPTY
                    {
                        set.union(VertexSet::single(vertex))
                    }
                    else {
                        set
                    }
                },
            );
            first.then(second).is_ok_and(|composite| {
                composite.kernel() == first.kernel().union(preimage)
                    && site
                        .find((source, target), &composite)
                        .is_some_and(|arrow| arrow.lowering == Membership::Inside)
            })
        })
    });
    if addressed && related && unions {
        Verdict::Holds
    }
    else {
        Verdict::Fails
    }
}

/// Whether every deletion behaves as the codegeneracy the point grade
/// expects.
///
/// # Specification
/// - ensures: holds exactly when every deletion `δ : G → K` with kernel of `k`
///   points leaves `K` with `k` fewer points, the same core as `G`, and a
///   degree lower by `k`; the first failing map otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome is pinned at the bound; the counter-example
///   check rejects a deletion that keeps all three facts.
/// - witness: `tests::point_count::the_codegeneracy_is_split`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => {
        let removed = witness.map().kernel().count();
        usize::from(witness.source().point_count()) != usize::from(witness.target().point_count()).saturating_add(usize::from(removed))
            || Degree::of(witness.source()) != Degree::of(witness.target()).raised_by(removed)
            || witness.source().core().map(|core| core.key()) != witness.target().core().map(|core| core.key())
    },
})]
pub fn codegeneracies(site: &Site<'_>) -> Outcome<MapCase>
{
    let mut tally = Tally::default();
    for &(source, target) in &site.pairs {
        let (Some(from), Some(to)) = (site.nodes.get(source.0), site.nodes.get(target.0))
        else {
            continue;
        };
        let deletions = site.arrows(source, target).iter().filter(|arrow| {
            arrow.lowering == Membership::Inside
                && arrow.invertibility == Invertibility::NotInvertible
        });
        for deletion in deletions {
            tally.count();
            let removed = usize::from(deletion.map.kernel().count());
            let points = usize::from(from.point_count())
                == usize::from(to.point_count()).saturating_add(removed);
            let cores = match (from.core(), to.core()) {
                | (Ok(left), Ok(right)) => left.key() == right.key(),
                | _ => false,
            };
            let lowered =
                Degree::of(from) == Degree::of(to).raised_by(deletion.map.kernel().count());
            if !(points && cores && lowered) {
                return tally.fails(site.case((source, target), deletion.map));
            }
        }
    }
    tally.holds()
}

/// Whether the point, the arity-zero corolla, has only its identity as a
/// raising endomorphism and reaches each point of a shape once.
///
/// # Specification
/// - ensures: holds exactly when `•` is a shape of the site, its only raising
///   endomorphism is its identity, and for every shape the raising maps from
///   `•` whose image is one vertex are one per point, each onto that point,
///   after one case per shape; the first failing shape otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the outcome and its case count, one per shape, are pinned
///   at the bound; L3 — of the two endomorphisms of `•`, only the identity is
///   raising.
/// - witness: `tests::units::the_point_reaches_each_point_once`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => cases == site.node_count(),
    Outcome::Fails { .. } => true,
})]
pub fn corolla(site: &Site<'_>) -> Outcome<Shape>
{
    let mut tally = Tally::default();
    let Some(point) = site
        .nodes
        .iter()
        .position(|shape| {
            usize::from(shape.vertex_count()) == 1 && usize::from(shape.wire_count()) == 0
        })
        .map(Node)
    else {
        tally.count();
        return tally.fails(Shape::default());
    };
    for (index, shape) in site.nodes.iter().enumerate() {
        tally.count();
        let raising: Vec<&Arrow<'_>> = site
            .arrows(point, Node(index))
            .iter()
            .filter(|arrow| arrow.raising == Membership::Inside)
            .collect();
        let inclusions: Vec<VertexSet> = raising
            .iter()
            .map(|arrow| arrow.map.image(Edge::from(0_usize)))
            .filter(|image| usize::from(image.count()) == 1)
            .collect();
        let expected: Vec<VertexSet> = shape.points().into_iter().map(VertexSet::single).collect();
        let mut sorted = inclusions.clone();
        sorted.sort_unstable();
        let endomorphisms = Node(index) != point
            || raising
                .iter()
                .all(|arrow| site.identity(point).is_some_and(|unit| *arrow.map == unit));
        if sorted != expected || !endomorphisms {
            return tally.fails((*shape).clone());
        }
    }
    tally.holds()
}
