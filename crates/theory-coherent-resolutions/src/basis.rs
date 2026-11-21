//! The homotopy basis of a convergent cell system, reduced by its critical
//! triples as a Morse collapse.
//!
//! The confluences of the critical pairs make a homotopy basis. A critical
//! triple gives a 4-cell, and the boundary of the 4-cell holds confluences.
//! [`Basis`] holds the confluences and the triples as the cells of one
//! complex, one dimension apart. A confluence is a face of a triple when it
//! occurs in the boundary of its 4-cell. A pair holds a confluence and a
//! triple when the confluence occurs there once, at the root, and with no
//! context. The 4-cell then defines the confluence by the other confluences,
//! and [`equivalence`](gandr_theory_discrete_morse::equivalence) removes it.
//!
//! The composites are the free (3,1)-category on the confluences, written as
//! words. A [`RewritePath`] is a 2-cell: steps along their cells or against
//! them. A [`Homotopy`] is a 3-cell: a path and the moves that deform it. A
//! move puts a confluence in place of its first path, in context, or
//! exchanges two steps that commute, or puts a word and its inverse in or
//! out. Two words are equal composites when they are equal words. The replay
//! never compares two different words for one composite: it checks each
//! witness by running its moves.
//!
//! The boundary of each triple comes from the normalisation strategy of
//! [`apply_once`](crate::apply_once), outermost first. Thus the boundaries
//! depend on the order of the cells, and so does the matching. A boundary
//! past the normalization budget is not built. Its triple stays outside the
//! complex, and [`Basis::unbuilt`] reports it.
//!
//! The basis admits only cells whose two sides hold each metavariable once.
//! A cell that duplicates or erases a variable is refused.
//!
//! # References
//!
//! - `Ara-2025-polygraphs_rewriting_higher_categories` — dependency: § 7.5, the
//!   reduction of a homotopy basis by its triple confluences — Theorem 7.3.5:
//!   the confluences of the critical branchings of a convergent presentation
//!   make a homotopy basis. § 7.5.4: a collapsible part and its well-founded
//!   relation. § 7.5.6: a triple confluence in which a confluence occurs once
//!   with no whiskers. Example 7.5.8: the reduction of the presentation of B₃⁺
//!   by two triple confluences, which the tests take.
//! - `Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras`
//!   — dependency: §§ 4–5 — the critical triples as the cells of dimension
//!   four of the resolution, through a collapsing scheme.

mod engine;
mod sphere;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_discrete_morse::Closure;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Composites;
use gandr_theory_discrete_morse::Definition;
use gandr_theory_discrete_morse::Images;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Invertibility;
use gandr_theory_discrete_morse::Matching;
use gandr_theory_discrete_morse::Standing;
use quenchant_shape::shape::Maybe;

use self::engine::forward;
use self::engine::inverted;
use self::engine::lone_variable;
use self::engine::run;
use self::sphere::Builder;
use self::sphere::Unbuilt;
use self::sphere::cut;
use crate::boundary::CertificateIndex;
use crate::boundary::MovePlace;
use crate::boundary::NormalizationBudget;
use crate::boundary::StepPlace;
use crate::boundary::TripleIndex;
use crate::rewrite::CellApp;
use crate::tracelet::Tracelet;
use crate::triple::CriticalTriple;
use crate::triple::critical_triples;

/// Whether a step runs along its cell or against it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sense
{
    /// From the left-hand side to the right-hand side.
    Forward,
    /// From the right-hand side to the left-hand side.
    Backward,
}

impl Sense
{
    /// The other sense.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flipped(self) -> Self
    {
        match self {
            Self::Forward => Self::Backward,
            Self::Backward => Self::Forward,
        }
    }
}

/// One step of a rewriting path: a cell fired at a position, along its cell
/// or against it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PathStep<A: CellAlphabet = SequentAlphabet>
{
    /// The cell and the position.
    pub app: CellApp<A>,
    /// Along the cell or against it.
    pub sense: Sense,
}

/// A rewriting path: a term, and the steps that run from it. A 2-cell of the
/// free (2,1)-category on the cells.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewritePath<A: CellAlphabet = SequentAlphabet>
{
    /// The term that the path starts at.
    pub start: A::Cmd,
    /// The steps, in order.
    pub steps: Vec<PathStep<A>>,
}

/// One move of a homotopy: a deformation of the path it reads.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Move<A: CellAlphabet = SequentAlphabet>
{
    /// A confluence in context. Its first path, moved below `at`, stands at
    /// `offset` in the path, and its second path takes its place. Against
    /// the confluence, the second path stands there and the first takes its
    /// place.
    Confluence
    {
        /// The confluence.
        certificate: CertificateIndex,
        /// Along the confluence or against it.
        sense: Sense,
        /// The place of the confluence's first step in the path.
        offset: StepPlace,
        /// The position of the confluence's peak in the term.
        at: A::Pos,
    },
    /// The two forward steps at `offset` swapped: they commute.
    Exchange
    {
        /// The place of the first step.
        offset: StepPlace,
    },
    /// A word and then its inverse, put in at `offset`.
    Expand
    {
        /// The place that the word takes.
        offset: StepPlace,
        /// The word.
        word: Vec<PathStep<A>>,
    },
    /// A word and then its inverse, taken out at `offset`.
    Contract
    {
        /// The place of the word.
        offset: StepPlace,
        /// The word.
        word: Vec<PathStep<A>>,
    },
}

/// The offset `by` steps past `offset`.
///
/// # Specification
/// trivial.
fn past(
    offset: StepPlace,
    by: StepPlace,
) -> StepPlace
{
    StepPlace::from(usize::from(offset).saturating_add(usize::from(by)))
}

impl<A: CellAlphabet> Move<A>
{
    /// The place in the path that the move reads first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> StepPlace
    {
        match *self {
            Self::Confluence { offset, .. }
            | Self::Exchange { offset }
            | Self::Expand { offset, .. }
            | Self::Contract { offset, .. } => offset,
        }
    }

    /// The move that undoes this move.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn inverse(&self) -> Self
    {
        match *self {
            Self::Confluence {
                certificate,
                sense,
                offset,
                ref at,
            } => Self::Confluence {
                certificate,
                sense: sense.flipped(),
                offset,
                at: at.clone(),
            },
            Self::Exchange { offset } => Self::Exchange { offset },
            Self::Expand { offset, ref word } => Self::Contract {
                offset,
                word: word.clone(),
            },
            Self::Contract { offset, ref word } => Self::Expand {
                offset,
                word: word.clone(),
            },
        }
    }

    /// The move on a path with `by` more steps before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn shifted(
        &self,
        by: StepPlace,
    ) -> Self
    {
        let mut moved = self.clone();
        match moved {
            Self::Confluence { ref mut offset, .. }
            | Self::Exchange { ref mut offset }
            | Self::Expand { ref mut offset, .. }
            | Self::Contract { ref mut offset, .. } => *offset = past(*offset, by),
        }
        moved
    }

    /// The move on a path with `by` more steps before it, in a term that
    /// holds the move's term at the position `at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn transported(
        &self,
        by: StepPlace,
        at: &A::Pos,
    ) -> Self
    {
        let below = |word: &[PathStep<A>]| -> Vec<PathStep<A>> {
            word.iter()
                .map(|step| PathStep {
                    app: CellApp {
                        at: engine::below::<A>(at, &step.app.at),
                        ..step.app.clone()
                    },
                    sense: step.sense,
                })
                .collect()
        };
        match *self {
            Self::Confluence {
                certificate,
                sense,
                offset,
                at: ref inner,
            } => Self::Confluence {
                certificate,
                sense,
                offset: past(offset, by),
                at: engine::below::<A>(at, inner),
            },
            Self::Exchange { offset } => Self::Exchange {
                offset: past(offset, by),
            },
            Self::Expand { offset, ref word } => Self::Expand {
                offset: past(offset, by),
                word: below(word),
            },
            Self::Contract { offset, ref word } => Self::Contract {
                offset: past(offset, by),
                word: below(word),
            },
        }
    }
}

/// A homotopy: a rewriting path, and the moves that deform it in turn. A
/// 3-cell of the free (3,1)-category on the confluences, as a word.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Homotopy<A: CellAlphabet = SequentAlphabet>
{
    /// The path that the first move reads.
    pub source: RewritePath<A>,
    /// The moves, in order.
    pub moves: Vec<Move<A>>,
}

/// A cell of the basis: a confluence, or a critical triple one dimension up.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BasisCell
{
    /// The confluence of a critical pair: a 3-cell.
    Confluence(CertificateIndex),
    /// The 4-cell of a critical triple.
    Triple(TripleIndex),
}

/// A composite of the basis: a homotopy, or the 4-cell of a triple with the
/// boundary that it fills.
///
/// The identity 4-cell on a homotopy is the homotopy itself, as the identity
/// path on a vertex is the vertex.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Composite<A: CellAlphabet = SequentAlphabet>
{
    /// A homotopy between two rewriting paths.
    Homotopy(Homotopy<A>),
    /// The 4-cell of a triple, which fills its boundary.
    Filler
    {
        /// The triple.
        triple: TripleIndex,
        /// The loop that the 4-cell fills, with each confluence that a
        /// collapse maps in the place of its image.
        boundary: Homotopy<A>,
    },
}

impl<A: CellAlphabet> Composite<A>
{
    /// The homotopy of the composite: itself, or the boundary of its 4-cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn homotopy(&self) -> &Homotopy<A>
    {
        match *self {
            Self::Homotopy(ref homotopy) => homotopy,
            Self::Filler { ref boundary, .. } => boundary,
        }
    }

    /// The composite with `homotopy` in the place of its homotopy.
    ///
    /// # Specification
    /// trivial.
    fn with(
        &self,
        homotopy: Homotopy<A>,
    ) -> Self
    {
        match *self {
            Self::Homotopy(_) => Self::Homotopy(homotopy),
            Self::Filler { triple, .. } => Self::Filler {
                triple,
                boundary: homotopy,
            },
        }
    }
}

/// One fill: a confluence at a move of a homotopy, replaced by its
/// definition through the 4-cell of a triple.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Fill
{
    /// The triple whose 4-cell defines the confluence.
    pub triple: TripleIndex,
    /// The move of the triple's boundary at which the confluence occurs.
    pub cut: MovePlace,
    /// The move of the homotopy that the confluence takes.
    pub at: MovePlace,
}

/// A cell between two composites of the basis: fills applied in turn to a
/// source. It runs from the source to the composite that the fills reach.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Witness<A: CellAlphabet = SequentAlphabet>
{
    /// The composite that the first fill reads.
    pub source: Composite<A>,
    /// The fills, in order.
    pub fills: Vec<Fill>,
}

/// Why the basis cannot answer.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BasisFault
{
    /// The cell lies outside the basis.
    Outside(BasisCell),
    /// A step of the source of a homotopy does not fire.
    Unfired,
    /// A move does not apply to the path it reads, or a fill to the
    /// homotopy it reads.
    Inapplicable(MovePlace),
    /// The partner defines nothing: the cell does not occur once in its
    /// boundary, at the root and with no context.
    Undefined(BasisCell),
    /// An image of the wrong dimension: a 4-cell in the place of a
    /// confluence, or an identity on a 4-cell.
    Dimension,
    /// A witness of the cell that does not start at the cell's own
    /// composite.
    Unrooted(BasisCell),
    /// A fill whose triple or confluence the images map. A collapse sends
    /// the 4-cell of a partner to an identity only up to its boundary, which
    /// the fill does not hold.
    Uncarried(TripleIndex),
}

/// Why the basis refuses a cell system.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BasisRefusal
{
    /// A cell duplicates or erases a variable, or writes a wire.
    Nonlinear(CellId),
    /// A certificate does not replay against the store.
    Unreplayed(CertificateIndex),
    /// No certificate joins a branching that the boundary of the triple
    /// resolves.
    Unjoined(TripleIndex),
    /// The boundary of the triple does not close.
    Unclosed(TripleIndex),
}

/// A confluence that occurs once in the boundary of a triple, at the root
/// and with no context, and its definition by the rest of the boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Cut<A>
where
    A: CellAlphabet,
{
    /// The confluence.
    certificate: CertificateIndex,
    /// The move of the boundary at which it occurs.
    place: MovePlace,
    /// A homotopy from its first path to its second.
    replacement: Homotopy<A>,
}

/// The homotopy basis of a convergent cell system: its confluences and its
/// critical triples as a complex, with the matching of its reduction.
///
/// # Specification
/// - ensures: each built boundary closes, and each cut's replacement runs from
///   its confluence's first path to its second.
/// - provides: the confluences, the triples whose boundary the budget builds,
///   and the matching that pairs each triple with its first cut whose
///   confluence no earlier triple pairs.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Basis::new`]'s,
///   which runs each boundary and each replacement.
#[derive(Clone, Debug)]
pub struct Basis<'basis, A: CellAlphabet = SequentAlphabet>
{
    /// The cells.
    store: &'basis CellStore<A>,
    /// The confluences, by their index.
    certificates: &'basis [Tracelet<A>],
    /// The critical triples, by their index.
    triples: Vec<CriticalTriple<A>>,
    /// The boundary of each triple's 4-cell, or nothing past the budget.
    spheres: Vec<Option<Homotopy<A>>>,
    /// The cuts of each triple's boundary.
    cuts: Vec<Vec<Cut<A>>>,
    /// The triples whose boundary passes the budget.
    unbuilt: Vec<TripleIndex>,
}

/// The metavariables of `term`, ascending, when each occurs once as a lone
/// command; otherwise nothing.
///
/// # Specification
/// trivial.
fn variables<A>(term: &A::Cmd) -> Option<Vec<A::Var>>
where
    A: CellAlphabet,
{
    let mut found: Vec<A::Var> = A::command_positions(term)
        .iter()
        .filter_map(|at| match A::subterm_cmd_at(term, at) {
            Maybe::Present(ref sub) => lone_variable::<A>(sub),
            Maybe::Absent(_) => None,
        })
        .collect();
    found.sort();
    let distinct = found.windows(2).all(|pair| pair.first() != pair.get(1));
    let mut named = A::metavariables(term);
    named.sort();
    named.dedup();
    (distinct && named == found).then_some(found)
}

/// Whether `cell` holds each metavariable once on each side, the same ones on
/// both, and writes no wire.
///
/// # Specification
/// trivial.
fn linear<A>(cell: &Cell<A>) -> Option<()>
where
    A: CellAlphabet,
{
    let left = variables::<A>(cell.lhs())?;
    let right = variables::<A>(cell.rhs())?;
    (left == right && cell.wires().is_empty()).then_some(())
}

/// Whether `left` and `right` are equal up to a renaming of their
/// metavariables: each matches the other.
///
/// # Specification
/// trivial.
fn renames<A>(
    left: &A::Cmd,
    right: &A::Cmd,
) -> Option<()>
where
    A: CellAlphabet,
{
    let both = bool::from(A::match_cmd(left, right, &mut A::Subst::default()))
        && bool::from(A::match_cmd(right, left, &mut A::Subst::default()));
    both.then_some(())
}

/// The cuts of `sphere`: each confluence that occurs once in it, at the root,
/// on a renaming of its peak, with its definition. `trace` holds the term at
/// each move's offset. Nothing where a replacement does not run.
///
/// # Specification
/// trivial.
fn cuts_of<A>(
    store: &CellStore<A>,
    certificates: &[Tracelet<A>],
    sphere: &Homotopy<A>,
    trace: &[A::Cmd],
) -> Option<Vec<Cut<A>>>
where
    A: CellAlphabet,
{
    let root = A::root_position();
    let occurrences = |certificate: CertificateIndex| {
        sphere
            .moves
            .iter()
            .filter(|each| matches!(**each, Move::Confluence { certificate: held, .. } if held == certificate))
            .count()
    };
    let mut scratch = Vec::new();
    let mut out = Vec::new();
    for (place, each) in sphere.moves.iter().enumerate() {
        let Move::Confluence {
            certificate,
            ref at,
            ..
        } = *each
        else {
            continue;
        };
        if *at != root || occurrences(certificate) != 1 {
            continue;
        }
        let tracelet = certificates.get(usize::from(certificate))?;
        if renames::<A>(&tracelet.overlap.peak, trace.get(place)?).is_none() {
            continue;
        }
        scratch.clear();
        let path = run(
            store,
            certificates,
            &sphere.source,
            sphere.moves.get(.. place)?,
            &mut scratch,
        )
        .ok()?;
        let replacement = cut(sphere, MovePlace::from(place), &path, tracelet)?;
        scratch.clear();
        let end = run(
            store,
            certificates,
            &replacement.source,
            &replacement.moves,
            &mut scratch,
        )
        .ok()?;
        if !end.iter().map(|step| &step.app).eq(tracelet.path_b.iter())
            || end.iter().any(|step| step.sense != Sense::Forward)
        {
            return None;
        }
        out.push(Cut {
            certificate,
            place: MovePlace::from(place),
            replacement,
        });
    }
    Some(out)
}

impl<'basis, A: CellAlphabet> Basis<'basis, A>
{
    /// The basis of `store` with its confluences `certificates`: the boundary
    /// of each critical triple, its cuts, and the reduction.
    ///
    /// # Specification
    /// - requires: `certificates` joins each critical pair of `store` that a
    ///   triple's boundary resolves.
    /// - ensures: each built boundary closes, each cut's replacement runs from
    ///   its confluence's first path to its second, and a boundary past
    ///   `budget` is listed in [`Basis::unbuilt`].
    /// - fails: with the refusal of the first cell, certificate or triple that
    ///   does not hold.
    /// - panics: none.
    /// - executable: none — the body is the predicate: it runs each boundary
    ///   and each replacement.
    /// - intension: one boundary for each triple, built within `budget`, and
    ///   one run of each boundary and of each cut.
    ///
    /// # Errors
    /// - [`BasisRefusal::Nonlinear`]: a cell duplicates or erases a variable.
    /// - [`BasisRefusal::Unreplayed`]: a certificate does not replay.
    /// - [`BasisRefusal::Unjoined`]: no certificate joins a branching.
    /// - [`BasisRefusal::Unclosed`]: a boundary does not close.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the presentation of B₃⁺ keeps A and B and removes C
    ///   and D. A budget of one leaves each triple unbuilt.
    /// - witness: `tests::basis::the_braid_monoid_keeps_two_confluences`
    /// - witness: `tests::basis::a_triple_past_the_budget_pairs_nothing`
    #[inline]
    pub fn new(
        store: &'basis CellStore<A>,
        certificates: &'basis [Tracelet<A>],
        budget: NormalizationBudget,
    ) -> Result<Self, BasisRefusal>
    {
        for (id, cell) in store.iter() {
            if linear::<A>(cell).is_none() {
                return Err(BasisRefusal::Nonlinear(id));
            }
        }
        for (place, tracelet) in certificates.iter().enumerate() {
            if !bool::from(tracelet.replay(store)) {
                return Err(BasisRefusal::Unreplayed(CertificateIndex::from(place)));
            }
        }
        let triples = critical_triples(store);
        let builder = Builder::new(store, certificates, budget);
        let mut spheres = Vec::with_capacity(triples.len());
        let mut cuts = Vec::with_capacity(triples.len());
        let mut unbuilt = Vec::new();
        let mut trace = Vec::new();
        for (place, triple) in triples.iter().enumerate() {
            let index = TripleIndex::from(place);
            match builder.sphere(triple) {
                Ok(sphere) => {
                    trace.clear();
                    let end = run(
                        store,
                        certificates,
                        &sphere.source,
                        &sphere.moves,
                        &mut trace,
                    )
                    .map_err(|_unreplayed| BasisRefusal::Unclosed(index))?;
                    if end != sphere.source.steps {
                        return Err(BasisRefusal::Unclosed(index));
                    }
                    cuts.push(
                        cuts_of(store, certificates, &sphere, &trace)
                            .ok_or(BasisRefusal::Unclosed(index))?,
                    );
                    spheres.push(Some(sphere));
                },
                Err(Unbuilt::Exhausted) => {
                    unbuilt.push(index);
                    spheres.push(None);
                    cuts.push(Vec::new());
                },
                Err(Unbuilt::Unjoined | Unbuilt::Unfired) => {
                    return Err(BasisRefusal::Unjoined(index));
                },
            }
        }
        Ok(Self {
            store,
            certificates,
            triples,
            spheres,
            cuts,
            unbuilt,
        })
    }

    /// The cells of the basis: each confluence, then each triple whose
    /// boundary is built.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> Vec<BasisCell>
    {
        let confluences = (0 .. self.certificates.len())
            .map(|place| BasisCell::Confluence(CertificateIndex::from(place)));
        let triples = self
            .spheres
            .iter()
            .enumerate()
            .filter(|&(_, sphere)| sphere.is_some())
            .map(|(place, _)| BasisCell::Triple(TripleIndex::from(place)));
        confluences.chain(triples).collect()
    }

    /// The critical triples, by their index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn triples(&self) -> &[CriticalTriple<A>]
    {
        &self.triples
    }

    /// The triples whose boundary passes the budget: they lie outside the
    /// complex, and pair nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unbuilt(&self) -> &[TripleIndex]
    {
        &self.unbuilt
    }

    /// The matching of the reduction: each triple, in order, with its first
    /// cut whose confluence no earlier triple pairs. Every other cell is
    /// critical. [`Matching::on`] reads it over the basis, so that a collapse
    /// or an equivalence reads the basis through it.
    ///
    /// # Specification
    /// - ensures: each confluence pairs with one triple at most, and a cut of
    ///   its triple holds it.
    /// - panics: none.
    /// - executable: none — the collapse of the basis checks the matching, and
    ///   the tests run it.
    /// - intension: one pass over the cuts, and O(p log p) for `p` pairs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the presentation of B₃⁺ keeps A and B and removes C
    ///   and D. A budget of one leaves each triple unbuilt and pairs nothing.
    /// - witness: `tests::basis::the_braid_monoid_keeps_two_confluences`
    /// - witness: `tests::basis::a_triple_past_the_budget_pairs_nothing`
    #[inline]
    #[must_use]
    pub fn matching(&self) -> Matching<BasisCell>
    {
        let mut paired = BTreeSet::new();
        Matching::stated(self.cuts.iter().enumerate().filter_map(|(place, held)| {
            let certificate = held
                .iter()
                .map(|each| each.certificate)
                .find(|certificate| !paired.contains(certificate))?;
            let _fresh = paired.insert(certificate);
            Some((
                BasisCell::Confluence(certificate),
                BasisCell::Triple(TripleIndex::from(place)),
            ))
        }))
    }

    /// The boundary of the 4-cell of `triple`, or nothing where it is not
    /// built.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sphere(
        &self,
        triple: TripleIndex,
    ) -> Option<&Homotopy<A>>
    {
        self.spheres
            .get(usize::from(triple))
            .and_then(Option::as_ref)
    }

    /// The boundary of `triple`, or the fault of a triple outside the basis.
    ///
    /// # Specification
    /// trivial.
    fn boundary(
        &self,
        triple: TripleIndex,
    ) -> Result<&Homotopy<A>, BasisFault>
    {
        self.sphere(triple)
            .ok_or(BasisFault::Outside(BasisCell::Triple(triple)))
    }

    /// The homotopy of the confluence `certificate` alone: its first path at
    /// its peak, deformed into its second.
    ///
    /// # Specification
    /// trivial.
    fn own(
        &self,
        certificate: CertificateIndex,
    ) -> Result<Homotopy<A>, BasisFault>
    {
        let tracelet = self
            .certificates
            .get(usize::from(certificate))
            .ok_or(BasisFault::Outside(BasisCell::Confluence(certificate)))?;
        Ok(Homotopy {
            source: RewritePath {
                start: tracelet.overlap.peak.clone(),
                steps: tracelet.path_a.iter().cloned().map(forward).collect(),
            },
            moves: vec![Move::Confluence {
                certificate,
                sense: Sense::Forward,
                offset: StepPlace::default(),
                at: A::root_position(),
            }],
        })
    }

    /// The cut of `triple` at which `certificate` occurs, or nothing.
    ///
    /// # Specification
    /// trivial.
    fn cut_of(
        &self,
        certificate: CertificateIndex,
        triple: TripleIndex,
    ) -> Option<&Cut<A>>
    {
        self.cuts
            .get(usize::from(triple))?
            .iter()
            .find(|each| each.certificate == certificate)
    }

    /// The cut that `fill` names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Undefined`]: the triple has no cut at that move.
    fn cut_at(
        &self,
        fill: &Fill,
    ) -> Result<&Cut<A>, BasisFault>
    {
        self.cuts
            .get(usize::from(fill.triple))
            .and_then(|held| held.iter().find(|each| each.place == fill.cut))
            .ok_or(BasisFault::Undefined(BasisCell::Triple(fill.triple)))
    }

    /// `homotopy` with the confluence at the move of `fill` replaced by the
    /// definition of its cut, in its context.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Undefined`]: the fill names no cut.
    /// - [`BasisFault::Inapplicable`]: the move is not that cut's confluence.
    fn fill(
        &self,
        homotopy: &Homotopy<A>,
        fill: &Fill,
    ) -> Result<Homotopy<A>, BasisFault>
    {
        let cut = self.cut_at(fill)?;
        let at = usize::from(fill.at);
        let refused = BasisFault::Inapplicable(fill.at);
        let Some(&Move::Confluence {
            certificate,
            sense,
            offset,
            at: ref position,
        }) = homotopy.moves.get(at)
        else {
            return Err(refused);
        };
        if certificate != cut.certificate {
            return Err(refused);
        }
        let (before, after) = (
            homotopy.moves.get(.. at).ok_or(refused)?,
            homotopy.moves.get(at.saturating_add(1) ..).ok_or(refused)?,
        );
        let block = match sense {
            Sense::Forward => cut.replacement.moves.clone(),
            Sense::Backward => inverted(&cut.replacement.moves),
        };
        let mut moves = Vec::with_capacity(
            before
                .len()
                .saturating_add(block.len())
                .saturating_add(after.len()),
        );
        moves.extend(before.iter().cloned());
        moves.extend(block.iter().map(|each| each.transported(offset, position)));
        moves.extend(after.iter().cloned());
        Ok(Homotopy {
            source: homotopy.source.clone(),
            moves,
        })
    }

    /// The composite that the fills of `witness` reach from its source.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Basis::fill`].
    fn end(
        &self,
        witness: &Witness<A>,
    ) -> Result<Composite<A>, BasisFault>
    {
        let mut reached = witness.source.homotopy().clone();
        for each in &witness.fills {
            reached = self.fill(&reached, each)?;
        }
        Ok(witness.source.with(reached))
    }

    /// The moves that `each` takes once `images` puts each mapped confluence
    /// in its place.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Dimension`]: a confluence maps to a 4-cell.
    fn spread(
        each: &Move<A>,
        images: &Images<'_, BasisCell, Composite<A>>,
    ) -> Result<Option<Vec<Move<A>>>, BasisFault>
    {
        let Move::Confluence {
            certificate,
            sense,
            offset,
            ref at,
        } = *each
        else {
            return Ok(None);
        };
        match images.of(&BasisCell::Confluence(certificate)) {
            None => Ok(None),
            Some(&Composite::Filler { .. }) => Err(BasisFault::Dimension),
            Some(&Composite::Homotopy(ref image)) => {
                let block = match sense {
                    Sense::Forward => image.moves.clone(),
                    Sense::Backward => inverted(&image.moves),
                };
                Ok(Some(
                    block
                        .iter()
                        .map(|moved| moved.transported(offset, at))
                        .collect(),
                ))
            },
        }
    }
}

impl<A: CellAlphabet> Complex for Basis<'_, A>
{
    type Cell = BasisCell;
    type Fault = BasisFault;

    /// Inside for each confluence and each built triple.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn standing(
        &mut self,
        cell: &BasisCell,
    ) -> Result<Standing, BasisFault>
    {
        let inside = match *cell {
            BasisCell::Confluence(certificate) => {
                usize::from(certificate) < self.certificates.len()
            },
            BasisCell::Triple(triple) => self.sphere(triple).is_some(),
        };
        Ok(if inside {
            Standing::Inside
        }
        else {
            Standing::Outside
        })
    }

    /// No face for a confluence. For a triple, each confluence in its
    /// boundary, with the number of its forward occurrences less the number of
    /// its backward ones.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn faces(
        &mut self,
        cell: &BasisCell,
        faces: &mut Vec<(BasisCell, Incidence)>,
    ) -> Result<(), BasisFault>
    {
        let triple = match *cell {
            BasisCell::Confluence(certificate) => {
                return if usize::from(certificate) < self.certificates.len() {
                    Ok(())
                }
                else {
                    Err(BasisFault::Outside(*cell))
                };
            },
            BasisCell::Triple(triple) => triple,
        };
        let mut counts: BTreeMap<CertificateIndex, i64> = BTreeMap::new();
        for each in &self.boundary(triple)?.moves {
            if let Move::Confluence {
                certificate, sense, ..
            } = *each
            {
                let count = counts.entry(certificate).or_insert(0);
                *count = match sense {
                    Sense::Forward => count.saturating_add(1),
                    Sense::Backward => count.saturating_sub(1),
                };
            }
        }
        faces.extend(counts.into_iter().map(|(certificate, count)| {
            (BasisCell::Confluence(certificate), Incidence::from(count))
        }));
        Ok(())
    }

    /// Whether `face` occurs once in the boundary of `cell`, at the root and
    /// with no context. The incidence alone does not show it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pairing(
        &mut self,
        face: &BasisCell,
        cell: &BasisCell,
        incidence: Incidence,
    ) -> Result<Invertibility, BasisFault>
    {
        let _ = incidence;
        Ok(match (*face, *cell) {
            (BasisCell::Confluence(certificate), BasisCell::Triple(triple))
                if self.cut_of(certificate, triple).is_some() =>
            {
                Invertibility::Invertible
            },
            _ => Invertibility::NotInvertible,
        })
    }
}

impl<A: CellAlphabet> Composites for Basis<'_, A>
{
    type Composite = Composite<A>;
    type Witness = Witness<A>;

    /// The homotopy of a confluence alone, or the 4-cell of a triple with its
    /// boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &BasisCell,
    ) -> Result<Composite<A>, BasisFault>
    {
        match *cell {
            BasisCell::Confluence(certificate) => Ok(Composite::Homotopy(self.own(certificate)?)),
            BasisCell::Triple(triple) => Ok(Composite::Filler {
                triple,
                boundary: self.boundary(triple)?.clone(),
            }),
        }
    }

    /// The homotopy itself, which stands for the identity 4-cell on it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Dimension`]: the composite is a 4-cell.
    #[inline]
    fn identity(
        &mut self,
        composite: &Composite<A>,
    ) -> Result<Composite<A>, BasisFault>
    {
        match *composite {
            Composite::Homotopy(_) => Ok(composite.clone()),
            Composite::Filler { .. } => Err(BasisFault::Dimension),
        }
    }

    /// The triple of a 4-cell, then each confluence that a move takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generators(
        &mut self,
        composite: &Composite<A>,
        cells: &mut Vec<BasisCell>,
    ) -> Result<(), BasisFault>
    {
        if let Composite::Filler { triple, .. } = *composite {
            cells.push(BasisCell::Triple(triple));
        }
        cells.extend(
            composite
                .homotopy()
                .moves
                .iter()
                .filter_map(|each| match *each {
                    Move::Confluence { certificate, .. } => {
                        Some(BasisCell::Confluence(certificate))
                    },
                    Move::Exchange { .. } | Move::Expand { .. } | Move::Contract { .. } => None,
                }),
        );
        Ok(())
    }

    /// Each mapped confluence replaced by its image in its context, against
    /// the image where the move runs against the confluence. A mapped 4-cell
    /// goes to its image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn substitute(
        &mut self,
        composite: &Composite<A>,
        images: &Images<'_, BasisCell, Composite<A>>,
    ) -> Result<Composite<A>, BasisFault>
    {
        if let Composite::Filler { triple, .. } = *composite
            && let Some(image) = images.of(&BasisCell::Triple(triple))
        {
            return Ok(image.clone());
        }
        let homotopy = composite.homotopy();
        let mut moves = Vec::with_capacity(homotopy.moves.len());
        for each in &homotopy.moves {
            match Self::spread(each, images)? {
                Some(block) => moves.extend(block),
                None => moves.push(each.clone()),
            }
        }
        Ok(composite.with(Homotopy {
            source: homotopy.source.clone(),
            moves,
        }))
    }

    /// The source substituted, and each fill at the image of its move. A
    /// fill whose triple, confluence or replacement the images map is not
    /// carried.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Uncarried`]: the images reach a fill.
    #[inline]
    fn carry(
        &mut self,
        witness: &Witness<A>,
        images: &Images<'_, BasisCell, Composite<A>>,
    ) -> Result<Witness<A>, BasisFault>
    {
        let mapped = |certificate: CertificateIndex| {
            images.of(&BasisCell::Confluence(certificate)).is_some()
        };
        if let Composite::Filler { triple, .. } = witness.source
            && images.of(&BasisCell::Triple(triple)).is_some()
        {
            return Err(BasisFault::Uncarried(triple));
        }
        let source = self.substitute(&witness.source, images)?;
        let mut reached = witness.source.homotopy().clone();
        let mut fills = Vec::with_capacity(witness.fills.len());
        for each in &witness.fills {
            let uncarried = BasisFault::Uncarried(each.triple);
            let cut = self.cut_at(each)?;
            let reaches = images.of(&BasisCell::Triple(each.triple)).is_some()
                || mapped(cut.certificate)
                || cut.replacement.moves.iter().any(|moved| {
                    matches!(*moved, Move::Confluence { certificate, .. } if mapped(certificate))
                });
            if reaches {
                return Err(uncarried);
            }
            let mut at = 0_usize;
            for before in reached
                .moves
                .get(.. usize::from(each.at))
                .ok_or(uncarried)?
            {
                let length = Self::spread(before, images)?.map_or(1, |block| block.len());
                at = at.saturating_add(length);
            }
            fills.push(Fill {
                at: MovePlace::from(at),
                ..*each
            });
            reached = self.fill(&reached, each)?;
        }
        Ok(Witness { source, fills })
    }

    /// The fills of `first`, then those of `second`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        first: &Witness<A>,
        second: &Witness<A>,
    ) -> Result<Witness<A>, BasisFault>
    {
        let mut fills = Vec::with_capacity(first.fills.len().saturating_add(second.fills.len()));
        fills.extend_from_slice(&first.fills);
        fills.extend_from_slice(&second.fills);
        Ok(Witness {
            source: first.source.clone(),
            fills,
        })
    }

    /// The fills of each witnessed confluence of `composite`, moved to its
    /// place, against its fills where the move runs against the confluence.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Unrooted`]: a witness does not start at its cell's own
    ///   composite.
    #[inline]
    fn whisker(
        &mut self,
        composite: &Composite<A>,
        witnesses: &Images<'_, BasisCell, Witness<A>>,
    ) -> Result<Option<Witness<A>>, BasisFault>
    {
        let mut fills = Vec::new();
        let mut growth = 0_usize;
        for (place, each) in composite.homotopy().moves.iter().enumerate() {
            let Move::Confluence {
                certificate, sense, ..
            } = *each
            else {
                continue;
            };
            let cell = BasisCell::Confluence(certificate);
            let Some(witness) = witnesses.of(&cell)
            else {
                continue;
            };
            if witness.source != Composite::Homotopy(self.own(certificate)?) {
                return Err(BasisFault::Unrooted(cell));
            }
            let base = place.saturating_add(growth);
            let mut length = 1_usize;
            for inner in &witness.fills {
                let added = self.cut_at(inner)?.replacement.moves.len();
                let local = match sense {
                    Sense::Forward => usize::from(inner.at),
                    Sense::Backward => length
                        .saturating_sub(1)
                        .checked_sub(usize::from(inner.at))
                        .ok_or(BasisFault::Inapplicable(inner.at))?,
                };
                fills.push(Fill {
                    at: MovePlace::from(base.saturating_add(local)),
                    ..*inner
                });
                length = length.saturating_add(added).saturating_sub(1);
            }
            growth = growth.saturating_add(length.saturating_sub(1));
        }
        Ok((!fills.is_empty()).then(|| Witness {
            source: composite.clone(),
            fills,
        }))
    }

    /// The cut of the partner at the redundant confluence: its replacement,
    /// and the fill of the confluence's own homotopy through it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`BasisFault::Undefined`]: the confluence does not occur once in the
    ///   partner's boundary, at the root and with no context.
    #[inline]
    fn definition(
        &mut self,
        redundant: &BasisCell,
        partner: &BasisCell,
    ) -> Result<Definition<Composite<A>, Witness<A>>, BasisFault>
    {
        let undefined = BasisFault::Undefined(*redundant);
        let (BasisCell::Confluence(certificate), BasisCell::Triple(triple)) =
            (*redundant, *partner)
        else {
            return Err(undefined);
        };
        let cut = self.cut_of(certificate, triple).ok_or(undefined)?;
        let fill = Fill {
            triple,
            cut: cut.place,
            at: MovePlace::default(),
        };
        let replacement = Composite::Homotopy(cut.replacement.clone());
        Ok(Definition {
            replacement,
            witness: Witness {
                source: Composite::Homotopy(self.own(certificate)?),
                fills: vec![fill],
            },
        })
    }

    /// Whether the witness starts at `source`, each fill applies, the
    /// homotopy reached runs, and it is `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn replays(
        &mut self,
        witness: &Witness<A>,
        source: &Composite<A>,
        target: &Composite<A>,
    ) -> Result<Closure, BasisFault>
    {
        if witness.source != *source {
            return Ok(Closure::Open);
        }
        let Ok(reached) = self.end(witness)
        else {
            return Ok(Closure::Open);
        };
        let homotopy = reached.homotopy();
        let runs = run(
            self.store,
            self.certificates,
            &homotopy.source,
            &homotopy.moves,
            &mut Vec::new(),
        )
        .is_ok();
        Ok(if runs && reached == *target {
            Closure::Closes
        }
        else {
            Closure::Open
        })
    }

    /// A confluence alone, or the 4-cell of a triple with each witnessed
    /// confluence of its boundary carried to its witness's end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn conjugate(
        &mut self,
        cell: &BasisCell,
        witnesses: &Images<'_, BasisCell, Witness<A>>,
    ) -> Result<Composite<A>, BasisFault>
    {
        let own = self.generator(cell)?;
        self.whisker(&own, witnesses)?
            .as_ref()
            .map_or_else(|| Ok(own), |witness| self.end(witness))
    }
}
