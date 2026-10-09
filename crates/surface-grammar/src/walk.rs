//! The walk index of a grammar: the theory-graphs walk machine instantiated
//! over a [`Pbg`]'s molds.
//!
//! 1. **Vertices.** Every [`MoldId`] is an [`End::Node`], beside [`End::Root`].
//! 2. **Reachability rows.** Every form is enterable through some unbounded
//!    hole, so every mold is reachable from the root; one flat root row per
//!    mold keeps each tile a closure sink, and [`WalkIndex::molds`] is the
//!    label-to-mold projection.
//! 3. **Comparison rows.** The operator-precedence relation (Moon, Blinn,
//!    Porter and Omar 2025, Fig. 15), read off [`PrecDag`] comparisons only.
//!    The relation is a matrix over `(sort, precedence)` groups, so it is
//!    carried on one representative mold per group: `t_L ⋖ t_R` when `t_R`'s
//!    group is tighter in the shared sort, `t_L ⋗ t_R` dually. The `≐` face is
//!    the grammar's same-form adjacency, read by [`comparison_table`] directly
//!    rather than built into the index. Grout sits at `⊥`, comparable to
//!    everything, so an incomparable pair has no row and repair routes through
//!    grout.
//!
//! The comparison is carried per group, not per tile: per-tile rows feed the
//! walk machine's transitive closure a layered graph with many tiles per band
//! across deep bands, and the closure's path count grows exponentially with
//! the depth. Per-group rows bound it by the precedence bands instead.
//!
//! [`PrecDag`]: gandr_theory_graphs::PrecDag

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::End;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::SeenKeyVerdict;
use gandr_theory_graphs::StanceTileSorted;
use gandr_theory_graphs::Swing;
use gandr_theory_graphs::Walk;
use gandr_theory_graphs::WalkChainLength;
use gandr_theory_graphs::WalkIndex;
use gandr_theory_graphs::WalkSpec;
use gandr_theory_graphs::WalkSym;
use gandr_theory_graphs::WalkSymbolKey;

use crate::model::Pbg;
use crate::model::PbgError;
use crate::model::Sort;
use crate::model::TileLabel;

/// The longest alternating chain the walk index materialises.
///
/// The generated rows are single-swing; the closure combines them through the
/// shallow precedence bands. A walk past the ceiling is refused as
/// [`WalkBuildError::ChainLengthExceeded`](gandr_theory_graphs::WalkBuildError::ChainLengthExceeded),
/// never truncated.
pub const MAX_WALK_CHAIN_LEN: u32 = 64;

/// The grammar's symbol vocabulary for the walk machine.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GrammarWalkSym;

/// A grammar nonterminal: a form group.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GrammarNonterminal
{
    /// The group's sort.
    pub sort: Sort,
    /// The group's precedence.
    pub prec: Prec,
}

impl GrammarNonterminal
{
    /// Names a form group.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        sort: Sort,
        prec: Prec,
    ) -> Self
    {
        Self { sort, prec }
    }
}

/// A walk stance: one mold.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GrammarTile
{
    /// The mold's label.
    pub label: TileLabel,
    /// The mold.
    pub mold_id: MoldId,
    /// The sort of the mold's form.
    pub sort: Sort,
}

impl GrammarTile
{
    /// Names a mold as a stance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        label: TileLabel,
        mold_id: MoldId,
        sort: Sort,
    ) -> Self
    {
        Self {
            label,
            mold_id,
            sort,
        }
    }
}

impl WalkSym for GrammarWalkSym
{
    type Bounds = Prec;
    type Label = TileLabel;
    type Mold = MoldId;
    type Nonterminal = GrammarNonterminal;
    type Sort = Sort;
    type Stance = GrammarTile;

    /// The group's sort.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn nonterminal_sort(nonterminal: &Self::Nonterminal) -> Self::Sort
    {
        nonterminal.sort
    }

    /// The group's precedence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn nonterminal_bounds(nonterminal: &Self::Nonterminal) -> Self::Bounds
    {
        nonterminal.prec
    }

    /// The sort of the mold's form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stance_sort(stance: &Self::Stance) -> Self::Sort
    {
        stance.sort
    }

    /// Every stance is a molded tile, so every stance is tile-sorted and the
    /// minimality filter masks no shorter same-level walk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stance_tile_sorted(_stance: &Self::Stance) -> StanceTileSorted
    {
        StanceTileSorted::from(true)
    }

    /// The mold's label and id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn label_mold(stance: &Self::Stance) -> Option<(Self::Label, Self::Mold)>
    {
        Some((stance.label, stance.mold_id))
    }

    /// Mixes the group's sort tag and precedence index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn nonterminal_key(nonterminal: &Self::Nonterminal) -> WalkSymbolKey
    {
        let sort = StableHash(u64::from(u16::from(nonterminal.sort.grout_sort())));
        let prec = StableHash(u64::from(u16::from(nonterminal.prec.index())));
        WalkSymbolKey::from(stable_mix(stable_mix(StableHash(FNV_OFFSET), sort), prec).0)
    }

    /// Mixes the form's sort tag, the mold id and each label byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stance_key(stance: &Self::Stance) -> WalkSymbolKey
    {
        let mut hash = stable_mix(
            StableHash(FNV_OFFSET),
            StableHash(u64::from(u16::from(stance.sort.grout_sort()))),
        );
        hash = stable_mix(hash, StableHash(u64::from(u32::from(stance.mold_id))));
        for &byte in stance.label.as_ref().as_bytes() {
            hash = stable_mix(hash, StableHash(u64::from(byte)));
        }
        WalkSymbolKey::from(hash.0)
    }
}

/// One operator-precedence comparison (Moon, Blinn, Porter and Omar 2025,
/// Fig. 15).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Comparison
{
    /// `t_L ⋖ t_R`: the left tile yields; the right tile's form nests to the
    /// right.
    Yields,
    /// `t_L ≐ t_R`: the tiles are consecutive in one form.
    Equal,
    /// `t_L ⋗ t_R`: the left tile takes precedence; its form nests to the
    /// left.
    Takes,
}

/// One row of the comparison table.
///
/// The sort is the nonterminal `ρ` at which the two tiles' forms are
/// compared; keying the relation on it is what makes it sound where Floyd's
/// unindexed relation is not.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ComparisonRow
{
    /// The left mold.
    pub left: MoldId,
    /// The right mold.
    pub right: MoldId,
    /// The relation.
    pub cmp: Comparison,
    /// The sort the comparison is made at.
    pub sort: Sort,
}

/// One mold as the walk machine sees it.
#[derive(Clone, Copy, Debug)]
struct MoldFacts
{
    /// The mold as a stance.
    stance: GrammarTile,
    /// The mold's form group.
    nonterminal: GrammarNonterminal,
}

/// Builds the walk index of `pbg`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every mold is reachable from [`End::Root`] and projects under its
///   label through [`WalkIndex::molds`]; the `lt` and `gt` faces carry the
///   precedence relation between form groups of one sort, read off the
///   precedence DAG.
/// - fails: a walk the machine refuses, a chain past [`MAX_WALK_CHAIN_LEN`]
///   included.
/// - panics: none.
/// - intension: molds in id order; comparison rows over group representatives
///   in `(sort, precedence)` order.
///
/// # Errors
/// [`PbgError::Walk`] for a refused walk.
///
/// # Adequacy
/// - hypothesis: L3 generative — over the built-in surface and a synthetic
///   infix grammar: every mold reachable exactly once, the three comparison
///   faces present, every row coherent with the DAG, and no pair related two
///   ways.
/// - witness: `tests::walk::walk_index_projects_every_mold_once`
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
/// - witness: `tests::walk::comparison_table_is_conflict_free`
#[inline]
pub fn walk_index(pbg: &Pbg) -> Result<WalkIndex<GrammarWalkSym>, PbgError>
{
    let spec = build_spec(pbg)?;
    WalkIndex::build(&spec).map_err(PbgError::from)
}

/// Compares the walk index built with `(sort, bounds)` seen-keys against one
/// built with sort-only keys.
///
/// The index has explicit direct rows and no swing seeds or arcs, so there is
/// no swing closure for the two keyings to diverge on.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the machine's verdict for `pbg`'s walk specification.
/// - fails: a walk the machine refuses.
/// - panics: none.
///
/// # Errors
/// [`PbgError::Walk`] for a refused walk.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — the built-in surface's verdict is
///   [`SeenKeyVerdict::Equivalent`].
/// - witness: `tests::walk::seen_key_verdict_is_recorded`
#[inline]
pub fn seen_key_verdict(pbg: &Pbg) -> Result<SeenKeyVerdict, PbgError>
{
    let spec = build_spec(pbg)?;
    WalkIndex::compare_seen_keys(&spec).map_err(PbgError::from)
}

/// The walk specification of `pbg`: one root row per mold, and one comparison
/// row per related pair of form groups of one sort.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`walk_index`] describes.
/// - fails: a walk the machine refuses.
/// - panics: none.
///
/// # Errors
/// [`PbgError::Walk`] for a refused walk.
fn build_spec(pbg: &Pbg) -> Result<WalkSpec<GrammarWalkSym>, PbgError>
{
    let facts = mold_facts(pbg);
    let mut spec = WalkSpec::<GrammarWalkSym>::new(WalkChainLength::from(MAX_WALK_CHAIN_LEN))
        .map_err(PbgError::from)?;

    if let Some(first) = facts.first() {
        spec.set_root_entry(first.nonterminal);
    }

    // One direct root row per mold keeps the closure flat. The same-form
    // adjacency is dense with alternation fan-out, so the comparison table
    // reads it directly instead of the index chaining it.
    for fact in &facts {
        let walk = level_walk(fact.nonterminal)?;
        spec.insert_direct(Dir::Left, End::Root, End::Node(fact.stance), walk);
    }

    // Every comparable pair of same-sort groups is a direct row, so the `lt`
    // and `gt` faces are complete without deep transitive combination.
    let reps = group_reps(&facts);
    let dag = pbg.dag();
    for left in reps.values() {
        for right in reps.values() {
            if left.stance.sort != right.stance.sort {
                continue;
            }
            let p_l = left.nonterminal.prec;
            let p_r = right.nonterminal.prec;
            if bool::from(dag.lt(p_l, p_r, Assoc::Non)) {
                let walk = descent_walk(left.nonterminal, right.nonterminal)?;
                spec.insert_direct(
                    Dir::Left,
                    End::Node(left.stance),
                    End::Node(right.stance),
                    walk,
                );
            }
            else if bool::from(dag.gt(p_l, p_r, Assoc::Non)) {
                let walk = descent_walk(right.nonterminal, left.nonterminal)?;
                spec.insert_direct(
                    Dir::Right,
                    End::Node(right.stance),
                    End::Node(left.stance),
                    walk,
                );
            }
        }
    }

    Ok(spec)
}

/// The comparison table of a grammar's walk index.
///
/// `⋖` and `⋗` relate group representatives and are read off the index's
/// `lt` and `gt` faces, at the shared form sort. `≐` relates consecutive
/// tiles of one form and is read off [`Pbg::adjacencies`]: it is a grammar
/// fact, not a precedence walk.
///
/// # Specification
/// - requires: `index` is the [`walk_index`] of `pbg`.
/// - ensures: rows are ascending, every ordered pair has at most one row, and
///   only same-sort pairs appear.
/// - panics: none.
/// - intension: each ordered pair of same-sort representatives is probed
///   against `lt`, then `gt`.
///
/// # Adequacy
/// - hypothesis: L3 generative — over the built-in surface, every face is
///   present and every row agrees with the precedence DAG.
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
/// - witness: `tests::walk::comparison_table_is_conflict_free`
#[inline]
#[must_use]
pub fn comparison_table(
    pbg: &Pbg,
    index: &WalkIndex<GrammarWalkSym>,
) -> Vec<ComparisonRow>
{
    let facts = mold_facts(pbg);
    let reps = group_reps(&facts);
    let mut rows = Vec::new();

    for left in reps.values() {
        let left_end = End::Node(left.stance);
        for right in reps.values() {
            if left.stance.sort != right.stance.sort {
                continue;
            }
            let right_end = End::Node(right.stance);
            let cmp = if !index.lt(&left_end, &right_end).is_empty() {
                Some(Comparison::Yields)
            }
            else if !index.gt(&left_end, &right_end).is_empty() {
                Some(Comparison::Takes)
            }
            else {
                None
            };
            if let Some(cmp) = cmp {
                rows.push(ComparisonRow {
                    left: left.stance.mold_id,
                    right: right.stance.mold_id,
                    cmp,
                    sort: left.stance.sort,
                });
            }
        }
    }

    for &(left, right) in pbg.adjacencies() {
        if let Some(left_fact) = fact_at(&facts, left) {
            rows.push(ComparisonRow {
                left,
                right,
                cmp: Comparison::Equal,
                sort: left_fact.stance.sort,
            });
        }
    }

    rows.sort_unstable();
    rows
}

/// Every mold of `pbg` as the walk machine sees it, in id order.
///
/// # Specification
/// trivial.
fn mold_facts(pbg: &Pbg) -> Vec<MoldFacts>
{
    pbg.iter_molds()
        .map(|(mold_id, def)| MoldFacts {
            stance: GrammarTile::new(TileLabel(def.label), mold_id, def.sort),
            nonterminal: GrammarNonterminal::new(def.sort, def.prec),
        })
        .collect()
}

/// Every label with the molds the walk index projects under it.
///
/// # Specification
/// - requires: `index` is the [`walk_index`] of `pbg`.
/// - ensures: one entry per declared label that projects a mold, ascending by
///   label, molds ascending.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 generative — over the built-in surface, the projection is
///   exactly the mold table grouped by label.
/// - witness: `tests::walk::walk_index_projects_every_mold_once`
#[inline]
#[must_use]
pub fn reachable_molds(
    pbg: &Pbg,
    index: &WalkIndex<GrammarWalkSym>,
) -> BTreeMap<TileLabel, BTreeSet<MoldId>>
{
    let labels: BTreeSet<TileLabel> = pbg
        .iter_molds()
        .map(|(_mold_id, def)| TileLabel(def.label))
        .collect();
    let mut out: BTreeMap<TileLabel, BTreeSet<MoldId>> = BTreeMap::new();
    for label in labels {
        let molds: BTreeSet<MoldId> = index.molds(&label).iter().map(|&(_, mold)| mold).collect();
        if !molds.is_empty() {
            out.insert(label, molds);
        }
    }
    out
}

/// A walk that stays in one form group.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one swing through `nonterminal` and no stances.
/// - fails: never for one nonterminal; the machine's refusal is forwarded.
/// - panics: none.
///
/// # Errors
/// [`PbgError::Walk`].
fn level_walk(
    nonterminal: GrammarNonterminal
) -> Result<Walk<GrammarNonterminal, GrammarTile>, PbgError>
{
    let swing = Swing::new(vec![nonterminal]).map_err(PbgError::from)?;
    Walk::new(vec![swing], Vec::new()).map_err(PbgError::from)
}

/// One representative mold per form group: the group's smallest id.
///
/// # Specification
/// trivial.
fn group_reps(facts: &[MoldFacts]) -> BTreeMap<(Sort, Prec), MoldFacts>
{
    let mut reps: BTreeMap<(Sort, Prec), MoldFacts> = BTreeMap::new();
    for fact in facts {
        reps.entry((fact.stance.sort, fact.nonterminal.prec))
            .or_insert(*fact);
    }
    reps
}

/// The facts of mold `id`; none past the table.
///
/// # Specification
/// trivial.
fn fact_at(
    facts: &[MoldFacts],
    id: MoldId,
) -> Option<&MoldFacts>
{
    let index = usize::try_from(u32::from(id)).ok()?;
    facts.get(index)
}

/// A one-level descent from an outer form group into a nested one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one swing through `outer` then `inner`, and no stances.
/// - fails: never for two nonterminals; the machine's refusal is forwarded.
/// - panics: none.
///
/// # Errors
/// [`PbgError::Walk`].
fn descent_walk(
    outer: GrammarNonterminal,
    inner: GrammarNonterminal,
) -> Result<Walk<GrammarNonterminal, GrammarTile>, PbgError>
{
    let swing = Swing::new(vec![outer, inner]).map_err(PbgError::from)?;
    Walk::new(vec![swing], Vec::new()).map_err(PbgError::from)
}

/// The FNV offset basis the walk keys start from.
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

/// The FNV prime the walk keys mix with.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// A walk-key hash state, or one value to mix into it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StableHash(u64);

/// Mixes one whole value into a walk key: xor, then multiply by the prime.
///
/// Unlike [`Fnv64`](gandr_theory_graphs::Fnv64) it absorbs a 64-bit word at
/// once, not byte by byte.
///
/// # Specification
/// trivial.
fn stable_mix(
    hash: StableHash,
    value: StableHash,
) -> StableHash
{
    StableHash((hash.0 ^ value.0).wrapping_mul(FNV_PRIME))
}
