//! The Leclerc–Mimram oracle: Θ₂ by Definition 1 of Leclerc and Mimram's
//! cellular type theory, set beside the chain restriction.
//!
//! Definition 1 builds Θₙ₊₁ as the wreath `Δ ≀ Θₙ`. A map `[P_1, …, P_n] →
//! [Q_1, …, Q_m]` is a monotone map `f` of the outer points `0 … n` into `0 …
//! m`. It carries one inner map `P_i → Q_k` for each target interval `k` that
//! lies inside the image of a source interval `i`. At Θ₂ each inner map is Δ's,
//! a monotone map of points. The enumeration here follows the definition as
//! the formalisation `pasting-schemes-agda` states it, and never reads the
//! site. The closed form `|Δ([p], [q])| = C(p + q + 1, p + 1)` checks it by
//! hand on small pairs.
//!
//! The site reads a map's points off its wires. An outer chain's wire `j` runs
//! between vertices `j - 1` and `j`, so it is the point `j`. An empty column is
//! Θ₁'s `[0]`, and the site's map out of it names no point.
//!
//! # References
//!
//! - `Leclerc-2026-cellular_type_theory` — exemplar: Definition 1, Θₙ₊₁ as `Δ ≀
//!   Θₙ` with its maps inductive; Lemma 5, the suspension keeps pushouts; §
//!   2.6.2, the Segal condition at the wedge of two suspensions.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::fmt;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Level;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::VertexSet;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathCocone;
use gandr_theory_sites::WreathMap;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::WreathStratum;

use crate::fixture::Length;
use crate::fixture::column;
use crate::fixture::index;
use crate::fixture::level_one;
use crate::fixture::restriction;
use crate::fixture::theta;

/// Level two over the chains.
type Two = Wreath<Catalogue>;

/// A map of level two.
type TwoMap = WreathMap<SiteMap>;

/// A monotone map of points: each source point's image, in order.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Points(Vec<usize>);

impl fmt::Display for Points
{
    /// Writes the images in parentheses, comma-separated.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let written: Vec<String> = self.0.iter().map(ToString::to_string).collect();
        write!(f, "({})", written.join(", "))
    }
}

/// A Θ₂ object `[n](m_1, …, m_n)`: one column length per outer vertex.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Theta(Vec<usize>);

impl fmt::Display for Theta
{
    /// Writes `[n](m_1, …, m_n)`.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let written: Vec<String> = self.0.iter().map(ToString::to_string).collect();
        write!(f, "[{}]({})", self.0.len(), written.join(", "))
    }
}

/// A target interval inside the image of a source interval.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Cover
{
    /// The target interval, numbered as the target's outer vertex.
    interval: usize,
    /// The source interval, numbered as the source's outer vertex.
    source: usize,
}

/// A Θ₂ map by Definition 1: the outer map of points, and the inner map of
/// points at each target interval the outer image covers, in interval order.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ThetaMap
{
    /// The outer map of points.
    outer: Points,
    /// Each cover with its inner map of points, in interval order.
    inner: Vec<(Cover, Points)>,
}

impl fmt::Display for ThetaMap
{
    /// Writes the outer points, then each covered interval's inner points.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "points {}", self.outer)?;
        for &(cover, ref points) in &self.inner {
            write!(f, ", interval {} by {points}", cover.interval)?;
        }
        Ok(())
    }
}

/// A site map as Definition 1 reads it: its outer points, and each cover
/// with the inner points. A map out of an empty column names no point.
#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Reading
{
    /// The outer wires, as points.
    outer: Points,
    /// Each image vertex with its source vertex, and the inner wires as
    /// points.
    inner: Vec<(Cover, Option<Points>)>,
}

/// Every map `Δ([from], [into])`: the monotone maps of the points `0 ..=
/// from` into `0 ..= into`, in lexicographic order.
///
/// # Specification
/// trivial.
fn monotone(
    Length(from): Length,
    Length(into): Length,
) -> Vec<Points>
{
    let mut found: Vec<Vec<usize>> = vec![Vec::new()];
    for _ in 0 ..= from {
        found = found
            .into_iter()
            .flat_map(|prefix| {
                let low = prefix.last().copied().unwrap_or(0);
                (low ..= into).map(move |next| {
                    let mut longer = prefix.clone();
                    longer.push(next);
                    longer
                })
            })
            .collect();
    }
    found.into_iter().map(Points).collect()
}

/// Each target interval below `targets` inside the image of a source
/// interval of `outer`, with that source interval.
///
/// # Specification
/// trivial.
fn covered(
    outer: &Points,
    Length(targets): Length,
) -> Vec<Cover>
{
    (0 .. targets)
        .filter_map(|interval| {
            outer
                .0
                .windows(2)
                .position(|pair| match *pair {
                    [low, high] => low <= interval && interval < high,
                    _ => false,
                })
                .map(|source| Cover { interval, source })
        })
        .collect()
}

/// Each of `partial`'s inner maps, extended at `cover` by each of `choices`.
///
/// # Specification
/// trivial.
fn widen(
    partial: Vec<Vec<(Cover, Points)>>,
    cover: Cover,
    choices: &[Points],
) -> Vec<Vec<(Cover, Points)>>
{
    partial
        .into_iter()
        .flat_map(|done| {
            choices.iter().map(move |choice| {
                let mut more = done.clone();
                more.push((cover, choice.clone()));
                more
            })
        })
        .collect()
}

/// Every Θ₂ map from `source` to `target` by Definition 1.
///
/// # Specification
/// trivial.
fn theta_maps(
    source: &Theta,
    target: &Theta,
) -> Vec<ThetaMap>
{
    let mut maps = Vec::new();
    for outer in monotone(Length(source.0.len()), Length(target.0.len())) {
        let mut partial: Vec<Vec<(Cover, Points)>> = vec![Vec::new()];
        for cover in covered(&outer, Length(target.0.len())) {
            let choices = monotone(
                Length(source.0[cover.source]),
                Length(target.0[cover.interval]),
            );
            partial = widen(partial, cover, &choices);
        }
        maps.extend(partial.into_iter().map(|inner| ThetaMap {
            outer: outer.clone(),
            inner,
        }));
    }
    maps
}

/// The wires as points.
///
/// # Specification
/// trivial.
fn points(wires: &[Wire]) -> Points
{
    Points(wires.iter().map(|wire| usize::from(*wire)).collect())
}

/// `map`, out of `source`, as Definition 1 reads it.
///
/// # Specification
/// trivial.
fn read(
    map: &TwoMap,
    source: &Theta,
) -> Reading
{
    let mut inner: Vec<(Cover, Option<Points>)> = (0 .. source.0.len())
        .flat_map(|vertex| {
            map.column(Edge::from(vertex))
                .iter()
                .map(move |&(image, ref column)| {
                    let named = (source.0[vertex] > 0).then(|| points(column.wires()));
                    let cover = Cover {
                        interval: usize::from(image),
                        source: vertex,
                    };
                    (cover, named)
                })
        })
        .collect();
    inner.sort_unstable();
    Reading {
        outer: points(map.outer().wires()),
        inner,
    }
}

/// Whether `reading`, from `source` to `target`, is a map of Definition 1
/// with its empty columns' points left open.
///
/// # Specification
/// trivial.
fn conforms(
    reading: &Reading,
    source: &Theta,
    target: &Theta,
) -> Membership
{
    let monotone_into = |points: &Points, count: usize, top: usize| {
        points.0.len() == count.saturating_add(1)
            && points.0.windows(2).all(|pair| pair.first() <= pair.last())
            && points.0.iter().all(|point| *point <= top)
    };
    let covers: Vec<Cover> = reading.inner.iter().map(|&(cover, _)| cover).collect();
    let conforming = monotone_into(&reading.outer, source.0.len(), target.0.len())
        && covered(&reading.outer, Length(target.0.len())) == covers
        && reading.inner.iter().all(|&(cover, ref named)| {
            named.as_ref().is_none_or(|points| {
                monotone_into(points, source.0[cover.source], target.0[cover.interval])
            })
        });
    if conforming {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// The maps of Definition 1 `reading` names into `target`: its outer map,
/// and at each cover its inner points, or each point where an empty column
/// names none.
///
/// # Specification
/// trivial.
fn named(
    reading: &Reading,
    target: &Theta,
) -> Vec<ThetaMap>
{
    let mut partial: Vec<Vec<(Cover, Points)>> = vec![Vec::new()];
    for &(cover, ref points) in &reading.inner {
        partial = match *points {
            Some(ref points) => widen(partial, cover, core::slice::from_ref(points)),
            None => widen(
                partial,
                cover,
                &monotone(Length(0), Length(target.0[cover.interval])),
            ),
        };
    }
    partial
        .into_iter()
        .map(|inner| ThetaMap {
            outer: reading.outer.clone(),
            inner,
        })
        .collect()
}

/// The restriction's pasting schemes as Θ₂ objects, in index order. Each
/// one's outer shape and columns are the chains themselves, so a wire's
/// number is its point.
///
/// # Specification
/// trivial.
fn schemes(restriction: &Two) -> Vec<(ShapeIndex, Theta)>
{
    restriction
        .objects()
        .iter()
        .enumerate()
        .filter(|&(_, object)| {
            usize::from(object.outer().vertex_count()) > 0
                && usize::from(object.outer().point_count()) == 0
                && object
                    .columns()
                    .iter()
                    .all(|column| usize::from(column.point_count()) == 0)
        })
        .map(|(at, object)| {
            let lengths: Vec<usize> = object
                .columns()
                .iter()
                .map(|shape| usize::from(shape.vertex_count()))
                .collect();
            assert_eq!(
                *object.outer(),
                column(Length(lengths.len())),
                "{object}'s outer chain"
            );
            for (shape, length) in object.columns().iter().zip(&lengths) {
                assert_eq!(*shape, column(Length(*length)), "{object}'s column");
            }
            (ShapeIndex::from(at), Theta(lengths))
        })
        .collect()
}

/// Definition 1's counts meet the closed form on six small pairs. `[1](0)` is
/// the 1-cell and `[1](1)` the 2-cell.
///
/// | Pair | Outer maps and inner factors | Maps |
/// | --- | --- | --- |
/// | `[1](0) → [1](0)` | two constants, and the identity by `C(1, 1)` | 3 |
/// | `[1](0) → [1](1)` | two constants, and the identity by `C(2, 1)` | 4 |
/// | `[1](1) → [1](1)` | two constants, and the identity by `C(3, 2)` | 5 |
/// | `[1](0) → [2](0, 0)` | six monotone maps, each inner factor `C(1, 1)` | 6 |
/// | `[2](0, 0) → [1](0)` | four monotone maps, each inner factor `C(1, 1)` | 4 |
/// | `[1](1) → [2](1, 1)` | three constants, two faces by `C(3, 2)`, the cover by `C(3, 2)²` | 18 |
#[test]
fn definition_one_meets_the_closed_form_on_small_pairs()
{
    let cases = [
        (vec![0], vec![0], 3_usize),
        (vec![0], vec![1], 4),
        (vec![1], vec![1], 5),
        (vec![0], vec![0, 0], 6),
        (vec![0, 0], vec![0], 4),
        (vec![1], vec![1, 1], 18),
    ];
    for (source, target, count) in cases {
        let (source, target) = (Theta(source), Theta(target));
        assert_eq!(
            theta_maps(&source, &target).len(),
            count,
            "{source} → {target}"
        );
    }
}

/// Over the restriction's 32 pasting schemes at total size thirteen, Θ₂ holds
/// 81,005 maps by Definition 1 and the site 733. Each site map is a map of
/// Definition 1 once its empty columns name a point, and no two read alike.
/// The site's maps name 1,044 of Definition 1's and lack 79,961. The first
/// lacked map runs from `[1](0)` to itself: the constant at point 0, a
/// degeneracy the faces-only site drops.
#[test]
fn the_site_names_a_part_of_definition_one()
{
    let restriction = restriction(ShapeSize::from(13_usize));
    let schemes = schemes(&restriction);
    assert_eq!(schemes.len(), 32);
    let (mut theta, mut site, mut lacked) = (0_usize, 0_usize, 0_usize);
    let mut names: BTreeSet<ThetaMap> = BTreeSet::new();
    let mut first: Option<String> = None;
    let mut readings: Vec<Reading> = Vec::new();
    for &(from, ref source) in &schemes {
        for &(to, ref target) in &schemes {
            let hom = restriction.hom(from, to);
            readings.clear();
            readings.extend(hom.iter().map(|map| read(map, source)));
            for (reading, map) in readings.iter().zip(hom) {
                assert_eq!(
                    conforms(reading, source, target),
                    Membership::Inside,
                    "{map} from {source} to {target} is a map of Definition 1"
                );
            }
            readings.sort_unstable();
            assert!(
                readings.windows(2).all(|pair| pair.first() != pair.last()),
                "no two maps from {source} to {target} read alike"
            );
            let maps = theta_maps(source, target);
            theta += maps.len();
            site += readings.len();
            names.clear();
            names.extend(readings.iter().flat_map(|reading| named(reading, target)));
            let mut found = 0_usize;
            for map in &maps {
                if names.contains(map) {
                    found += 1;
                }
                else {
                    lacked += 1;
                    first.get_or_insert_with(|| format!("{source} → {target}: {map}"));
                }
            }
            assert_eq!(
                found,
                names.len(),
                "each map the site names from {source} to {target} is one of Definition 1's"
            );
        }
    }
    assert_eq!(site, 733);
    assert_eq!(
        (theta, lacked, first.as_deref()),
        (81_005, 79_961, Some("[1](0) → [1](0): points (0, 0)"))
    );
}

/// A commuting square of a level: the span's apex and feet, the cocone's
/// vertex, the span's legs and the cocone's legs.
struct Square<Map>
{
    /// The apex, the two feet and the cocone's vertex.
    objects: [ShapeIndex; 4],
    /// The span's legs.
    span: [Map; 2],
    /// The cocone's legs.
    cocone: [Map; 2],
}

/// Whether `square` is a pushout at `level`'s bound: every compatible pair of
/// maps out of the feet factors through the cocone by exactly one map.
///
/// # Specification
/// trivial.
fn universal<L>(
    level: &L,
    square: &Square<&L::Map>,
) -> Membership
where
    L: Level,
{
    let [_, left, right, vertex] = square.objects;
    let [first, second] = square.span;
    let [upper, lower] = square.cocone;
    let pushout = (0 .. level.objects().len())
        .map(ShapeIndex::from)
        .all(|test| {
            let mediating = level.hom(vertex, test);
            level.hom(left, test).iter().all(|out_left| {
                level.hom(right, test).iter().all(|out_right| {
                    let compatible = L::then(first, out_left).is_ok_and(|through| {
                        L::then(second, out_right).is_ok_and(|other| through == other)
                    });
                    !compatible
                        || mediating
                            .iter()
                            .filter(|map| {
                                L::then(upper, map).is_ok_and(|through| through == *out_left)
                                    && L::then(lower, map)
                                        .is_ok_and(|through| through == *out_right)
                            })
                            .take(2)
                            .count()
                            == 1
                })
            })
        });
    if pushout {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Every commuting square of `level` at its bound.
///
/// # Specification
/// trivial.
fn squares<L>(level: &L) -> Vec<Square<&L::Map>>
where
    L: Level,
{
    let every: Vec<ShapeIndex> = (0 .. level.objects().len()).map(ShapeIndex::from).collect();
    let mut found = Vec::new();
    for &apex in &every {
        for &left in &every {
            for &right in &every {
                for first in level.hom(apex, left) {
                    for second in level.hom(apex, right) {
                        for &vertex in &every {
                            for upper in level.hom(left, vertex) {
                                for lower in level.hom(right, vertex) {
                                    let commutes = L::then(first, upper).is_ok_and(|through| {
                                        L::then(second, lower).is_ok_and(|other| through == other)
                                    });
                                    if commutes {
                                        found.push(Square {
                                            objects: [apex, left, right, vertex],
                                            span: [first, second],
                                            cocone: [upper, lower],
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    found
}

/// The suspension of `shape` at level two: the outer 1-chain carrying it.
///
/// # Specification
/// trivial.
fn suspend(
    wreath: &Two,
    shape: &Shape,
) -> ShapeIndex
{
    let object = WreathShape::new(column(Length(1)), vec![shape.clone()]).expect("one column");
    index(wreath, &object)
}

/// The suspension of `map` between the suspensions at `from` and `to`: the
/// outer identity carrying `map`.
///
/// # Specification
/// trivial.
fn suspend_map<'wreath>(
    wreath: &'wreath Two,
    (from, to): (ShapeIndex, ShapeIndex),
    map: &SiteMap,
) -> &'wreath TwoMap
{
    let identity = SiteMap::identity(&column(Length(1)));
    let zero = Edge::from(0_usize);
    let found: Vec<&TwoMap> = wreath
        .hom(from, to)
        .iter()
        .filter(|suspended| {
            *suspended.outer() == identity && *suspended.column(zero) == [(zero, map.clone())]
        })
        .collect();
    match *found {
        [suspended] => suspended,
        _ => panic!("{map} has {} suspensions", found.len()),
    }
}

/// Lemma 5 on the chains: the suspension keeps every pushout, and reflects
/// it. The chains at total size nine hold 3,087 commuting squares, 260 of
/// them pushouts at the bound. Each square's suspension is a pushout of the
/// restriction at total size twelve exactly when the square is one below.
/// That restriction holds every suspended object.
#[test]
fn the_suspension_keeps_and_reflects_the_chains_pushouts()
{
    let below = Catalogue::chains(ShapeSize::from(9_usize)).expect("the chain catalogue builds");
    let wreath = restriction(ShapeSize::from(12_usize));
    let squares = squares(&below);
    let mut pushouts = 0_usize;
    for square in &squares {
        let objects = square
            .objects
            .map(|at| suspend(&wreath, &below.objects()[usize::from(at)]));
        let [apex, left, right, vertex] = objects;
        let suspended = Square {
            objects,
            span: [
                suspend_map(&wreath, (apex, left), square.span[0]),
                suspend_map(&wreath, (apex, right), square.span[1]),
            ],
            cocone: [
                suspend_map(&wreath, (left, vertex), square.cocone[0]),
                suspend_map(&wreath, (right, vertex), square.cocone[1]),
            ],
        };
        let pushout = universal(&below, square);
        if pushout == Membership::Inside {
            pushouts += 1;
        }
        assert_eq!(
            universal(&wreath, &suspended),
            pushout,
            "the suspension of the square of {} and {} under {} at {}",
            square.span[0],
            square.span[1],
            below.objects()[usize::from(square.objects[0])],
            below.objects()[usize::from(square.objects[3])]
        );
    }
    assert_eq!((squares.len(), pushouts), (3087, 260));
}

/// The inclusion from `from` into `to` that shifts the outer vertices by
/// `outer` and each inner vertex by `inner`, one inner vertex to one.
///
/// # Specification
/// trivial.
fn inclusion(
    wreath: &Two,
    (from, to): (ShapeIndex, ShapeIndex),
    (Length(outer), Length(inner)): (Length, Length),
) -> &TwoMap
{
    let shifted = |images: &[VertexSet], by: usize| {
        images.iter().enumerate().all(|(vertex, image)| {
            *image == VertexSet::single(Edge::from(vertex.saturating_add(by)))
        })
    };
    let found: Vec<&TwoMap> = wreath
        .hom(from, to)
        .iter()
        .filter(|map| {
            shifted(map.outer().images(), outer)
                && (0 .. map.outer().images().len()).all(|vertex| {
                    match *map.column(Edge::from(vertex)) {
                        [(image, ref column)] => {
                            usize::from(image) == vertex.saturating_add(outer)
                                && shifted(column.images(), inner)
                        },
                        _ => false,
                    }
                })
        })
        .collect();
    match *found {
        [map] => map,
        _ => panic!("{} inclusions", found.len()),
    }
}

/// Whether precomposing `left` and `right` sends the maps out of `object` one
/// to one onto the pairs of maps out of their sources that `compatible`
/// admits, at every test object.
///
/// # Specification
/// trivial.
fn wedge(
    wreath: &Two,
    object: ShapeIndex,
    [(first, left), (second, right)]: [(ShapeIndex, &TwoMap); 2],
    compatible: impl Fn(&TwoMap, &TwoMap) -> Membership,
) -> Membership
{
    let mut restricted: BTreeSet<(TwoMap, TwoMap)> = BTreeSet::new();
    let mut pairs: BTreeSet<(TwoMap, TwoMap)> = BTreeSet::new();
    for test in (0 .. wreath.objects().len()).map(ShapeIndex::from) {
        let out = wreath.hom(object, test);
        restricted.clear();
        restricted.extend(out.iter().map(|map| {
            (
                Two::then(left, map).expect("the inclusion composes"),
                Two::then(right, map).expect("the inclusion composes"),
            )
        }));
        pairs.clear();
        for one in wreath.hom(first, test) {
            for other in wreath.hom(second, test) {
                if compatible(one, other) == Membership::Inside {
                    pairs.insert((one.clone(), other.clone()));
                }
            }
        }
        if restricted.len() != out.len() || restricted != pairs {
            return Membership::Outside;
        }
    }
    Membership::Inside
}

/// The two Segal conditions over the chain restriction at total size
/// thirteen. `WreathStratum`'s cover certifies every object of degree two to
/// eleven. The wedge-at-a-suspension map of § 2.6.2 is checked at each of 60
/// splits of a pasting scheme.
///
/// At `n = 0` an outer split glues at a point. The site holds no 0-cell, so
/// the point is the outer wire both halves send it to. All 54 outer splits
/// meet the cover's verdict.
///
/// At `n = 1` a column split glues along the 1-cell `[1](0)`. The site's one
/// map out of it names no endpoint, so the fibre product over it admits pairs
/// whose inner halves do not meet. The wedge then fails at all 6 column
/// splits, where the cover holds. Read at the shared inner wire, as the
/// cover's inner graft reads it, the wedge meets the cover at all 6.
#[test]
fn the_wedge_and_the_cover_give_one_verdict()
{
    let bound = ShapeSize::from(13_usize);
    let chains = Arc::new(Catalogue::chains(bound).expect("the chain catalogue builds"));
    let level: &Catalogue = &chains;
    let wreath = Arc::new(Wreath::build(level, level, bound));
    let below = level_one(&chains);
    let cover = WreathStratum::certify(Arc::clone(&wreath), Degree::from(11_usize), below)
        .expect("level two is certified at the bound's top");
    let colimits: BTreeSet<ShapeIndex> = cover.cocones().iter().map(WreathCocone::object).collect();
    let class = |lengths: &[usize]| {
        let columns: Vec<Length> = lengths.iter().copied().map(Length).collect();
        index(&*wreath, &theta(&columns))
    };
    let as_membership = |holds: bool| {
        if holds {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    };
    let (mut splits, mut failures, mut through_the_cell) = (0_usize, Vec::new(), Vec::new());
    for (at, scheme) in schemes(&wreath) {
        let lengths = &scheme.0;
        let covered = as_membership(colimits.contains(&at));
        for cut in 1 .. lengths.len() {
            let (left, right) = (class(&lengths[.. cut]), class(&lengths[cut ..]));
            let legs = [
                (left, inclusion(&wreath, (left, at), (Length(0), Length(0)))),
                (
                    right,
                    inclusion(&wreath, (right, at), (Length(cut), Length(0))),
                ),
            ];
            let glued = wedge(&wreath, at, legs, |one, other| {
                as_membership(one.outer().wires().last() == other.outer().wires().first())
            });
            splits += 1;
            if glued != covered {
                failures.push(format!("{scheme} at the outer point {cut}"));
            }
        }
        if let [length] = **lengths {
            let cell = class(&[0]);
            for cut in 1 .. length {
                let (left, right) = (class(&[cut]), class(&[length - cut]));
                let legs = [
                    (left, inclusion(&wreath, (left, at), (Length(0), Length(0)))),
                    (
                        right,
                        inclusion(&wreath, (right, at), (Length(0), Length(cut))),
                    ),
                ];
                let [ref into_left] = *wreath.hom(cell, left)
                else {
                    panic!("one map from the 1-cell");
                };
                let [ref into_right] = *wreath.hom(cell, right)
                else {
                    panic!("one map from the 1-cell");
                };
                let literal = wedge(&wreath, at, legs, |one, other| {
                    as_membership(
                        Two::then(into_left, one).ok() == Two::then(into_right, other).ok(),
                    )
                });
                let at_the_wire = wedge(&wreath, at, legs, |one, other| {
                    let zero = Edge::from(0_usize);
                    let (mine, theirs) = (one.column(zero), other.column(zero));
                    as_membership(
                        one.outer() == other.outer()
                            && mine.len() == theirs.len()
                            && mine.iter().zip(theirs).all(
                                |(&(image, ref inner), &(other_image, ref other_inner))| {
                                    let (end, start) =
                                        (inner.wires().last(), other_inner.wires().first());
                                    image == other_image && end == start
                                },
                            ),
                    )
                });
                splits += 1;
                if literal != covered {
                    through_the_cell.push(format!("{scheme} at the column point {cut}"));
                }
                if at_the_wire != covered {
                    failures.push(format!("{scheme} at the column point {cut}"));
                }
            }
        }
    }
    assert_eq!((splits, failures), (60, Vec::<String>::new()));
    assert_eq!(through_the_cell, [
        "[1](2) at the column point 1",
        "[1](3) at the column point 1",
        "[1](3) at the column point 2",
        "[1](4) at the column point 1",
        "[1](4) at the column point 2",
        "[1](4) at the column point 3",
    ]);
}
