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

use anodized::spec;
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
    /// - requires: nothing.
    /// - ensures: the sort tag then precedence index are mixed as whole words
    ///   from the FNV offset.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For fixed compatibility vectors and one-field changes, L3
    ///   exact keys catch changed word order, omitted fields and truncated
    ///   indices; hash collision freedom is not claimed.
    /// - witness: `walk::tests::whole_word_keys_keep_their_fields_and_framing`
    #[spec(ensures: |ret| u64::from(ret) == stable_mix(stable_mix(StableHash(FNV_OFFSET), StableHash(u64::from(u16::from(nonterminal.sort.grout_sort())))), StableHash(u64::from(u16::from(nonterminal.prec.index())))).0)]
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
    /// - requires: nothing.
    /// - ensures: the sort tag, mold id and label bytes are mixed in that
    ///   order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For fixed compatibility vectors and one-field changes, L3
    ///   exact keys catch omitted sort, mold or label data and changed byte
    ///   order; arbitrary hash collisions remain possible.
    /// - witness: `walk::tests::whole_word_keys_keep_their_fields_and_framing`
    #[spec(ensures: |ret| u64::from(ret) == stance.label.as_ref().as_bytes().iter().fold(stable_mix(stable_mix(StableHash(FNV_OFFSET), StableHash(u64::from(u16::from(stance.sort.grout_sort())))), StableHash(u64::from(u32::from(stance.mold_id)))), |hash, &byte| stable_mix(hash, StableHash(u64::from(byte)))).0)]
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
/// - hypothesis: For the built-in surface, empty grammar and independent
///   groups, L3 exact root projections and comparison observations catch
///   dropped molds, duplicate projections, false comparisons and sort leakage;
///   arbitrary DAGs and chain-cap refusals are not exhausted.
/// - witness: `tests::walk::walk_index_projects_every_mold_once`
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
/// - witness: `tests::walk::comparison_table_is_conflict_free`
/// - witness: `walk::tests::empty_grammar_has_only_the_root`
/// - witness: `walk::tests::incomparable_forms_project_without_comparisons`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::Walk(_)), |index| index.ends().len() == pbg.mold_count().0.saturating_add(1) && index.ends().binary_search(&End::Root).is_ok() && pbg.iter_molds().all(|(id, def)| index.molds(&TileLabel(def.label)).binary_search(&(End::Node(GrammarTile::new(TileLabel(def.label), id, def.sort)), id)).is_ok())))]
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
/// - hypothesis: For the built-in surface, empty grammar and independent
///   groups, L3 verdict observations catch a divergent keying introduced into
///   this direct-row adapter; arbitrary machine swing closures are not
///   represented.
/// - witness: `tests::walk::seen_key_verdict_is_recorded`
/// - witness: `walk::tests::empty_grammar_has_only_the_root`
/// - witness: `walk::tests::incomparable_forms_project_without_comparisons`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::Walk(_)), |verdict| *verdict == SeenKeyVerdict::Equivalent))]
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
///
/// # Adequacy
/// - hypothesis: For the built-in surface, empty grammar and independent
///   groups, L3 cap and built-index observations catch a wrong cap, missing
///   root projections and false comparisons; private direct rows are observed
///   through the index, not rebuilt in the predicate.
/// - witness: `walk::tests::empty_grammar_has_only_the_root`
/// - witness: `walk::tests::incomparable_forms_project_without_comparisons`
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|spec| spec.max_chain_len() == WalkChainLength::from(MAX_WALK_CHAIN_LEN)))]
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
/// - hypothesis: The complete built-in table supplies L3 soundness and
///   completeness observations against DAG comparisons and same-form adjacency;
///   empty and independent-group fixtures catch spurious rows. The predicate
///   checks row order, uniqueness and soundness, not all arbitrary DAG
///   pairings.
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
/// - witness: `tests::walk::comparison_table_is_conflict_free`
/// - witness: `walk::tests::empty_grammar_has_only_the_root`
/// - witness: `walk::tests::incomparable_forms_project_without_comparisons`
#[spec(ensures: |ret| ret.iter().is_sorted() && ret.iter().zip(ret.iter().skip(1)).all(|(left, right)| (left.left, left.right) != (right.left, right.right)) && ret.iter().all(|row| pbg.mold(row.left).ok().zip(pbg.mold(row.right).ok()).is_some_and(|(left, right)| left.sort == row.sort && right.sort == row.sort && match row.cmp { Comparison::Yields => bool::from(pbg.dag().lt(left.prec, right.prec, Assoc::Non)), Comparison::Takes => bool::from(pbg.dag().gt(left.prec, right.prec, Assoc::Non)), Comparison::Equal => pbg.adjacencies().binary_search(&(row.left, row.right)).is_ok() })) && ret.iter().filter(|row| row.cmp == Comparison::Equal).count() == pbg.adjacencies().len())]
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
/// - requires: nothing.
/// - ensures: one stance and nonterminal per mold, preserving id, label, sort
///   and precedence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in mold inventory, L3 exact projection and DAG
///   coherence observations catch omitted molds, changed identities and wrong
///   groups; arbitrary grammars are not exhausted.
/// - witness: `tests::walk::walk_index_projects_every_mold_once`
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
#[spec(ensures: |ret| ret.len() == pbg.mold_count().0 && ret.iter().zip(pbg.iter_molds()).all(|(fact, (id, def))| fact.stance == GrammarTile::new(TileLabel(def.label), id, def.sort) && fact.nonterminal == GrammarNonterminal::new(def.sort, def.prec)))]
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
/// - hypothesis: Over every built-in mold and finite empty and
///   independent-group grammars, L3 exact label partitions catch missing
///   labels, foreign ids and duplicate projection; arbitrary caller-supplied
///   indexes remain outside the required matching-index domain.
/// - witness: `tests::walk::walk_index_projects_every_mold_once`
/// - witness: `walk::tests::empty_grammar_has_only_the_root`
/// - witness: `walk::tests::incomparable_forms_project_without_comparisons`
#[spec(ensures: |ret| ret.iter().all(|(label, molds)| !pbg.candidates(*label).is_empty() && !molds.is_empty() && molds.iter().all(|id| index.molds(label).iter().any(|&(_, projected)| projected == *id)) && index.molds(label).iter().all(|&(_, id)| molds.contains(&id))) && pbg.iter_molds().all(|(_, def)| { let label = TileLabel(def.label); index.molds(&label).is_empty() || ret.contains_key(&label) }))]
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
///
/// # Adequacy
/// - hypothesis: For equal and distinct groups including the largest precedence
///   index, L3 exact swing and stance observations catch reversed, duplicated
///   or missing nonterminals; allocation failure is outside the contract.
/// - witness: `walk::tests::single_swings_preserve_nonterminal_order`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|walk| walk.stances().is_empty() && walk.swings().len() == 1 && walk.swings().first().is_some_and(|swing| swing.nonterminals() == [nonterminal])))]
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
/// - requires: facts are ascending by mold id.
/// - ensures: one complete fact per sort and precedence group, retaining its
///   first identity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For ordered repeated groups, distinct sorts and precedence
///   indices, L3 representative identities catch last-wins selection and
///   grouping by only one coordinate; all table sizes are not exhausted.
/// - witness: `walk::tests::representatives_and_slots_keep_the_first_identity`
#[spec(requires: facts.iter().is_sorted_by(|left, right| left.stance.mold_id <= right.stance.mold_id), ensures: |ret| facts.iter().all(|fact| ret.get(&(fact.stance.sort, fact.nonterminal.prec)).is_some_and(|kept| kept.stance.mold_id <= fact.stance.mold_id)) && ret.iter().all(|(&(sort, prec), kept)| facts.iter().find(|fact| fact.stance.sort == sort && fact.nonterminal.prec == prec).is_some_and(|first| first.stance == kept.stance && first.nonterminal == kept.nonterminal)))]
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
/// - requires: nothing.
/// - ensures: borrows the slot at the mold index, or returns none outside the
///   slice.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For a four-slot table, L3 first, last, first-invalid and
///   maximal identities catch wrong indexing and invalid acceptance; wider
///   target pointer sizes are not separately modeled.
/// - witness: `walk::tests::representatives_and_slots_keep_the_first_identity`
#[spec(ensures: |ret| { let expected = usize::try_from(u32::from(id)).ok().and_then(|index| facts.get(index)); ret.map_or_else(|| expected.is_none(), |fact| expected.is_some_and(|held| core::ptr::eq(core::ptr::from_ref(fact), core::ptr::from_ref(held)))) })]
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
///
/// # Adequacy
/// - hypothesis: For equal and distinct groups including the largest precedence
///   index, L3 exact ordered swing observations catch swapped or dropped
///   endpoints and extra stances; the general walk machine is outside this
///   adapter witness.
/// - witness: `walk::tests::single_swings_preserve_nonterminal_order`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|walk| walk.stances().is_empty() && walk.swings().len() == 1 && walk.swings().first().is_some_and(|swing| swing.nonterminals() == [outer, inner])))]
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
/// - requires: nothing.
/// - ensures: returns the low 64 bits of the xor value multiplied by the FNV
///   prime.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the published one-byte FNV vector and zero, cancellation
///   and maximal-word boundaries, L3 exact outputs catch wrong xor order,
///   multiplication and overflow behavior; arbitrary word pairs are not
///   exhausted.
/// - witness: `walk::tests::whole_word_keys_keep_their_fields_and_framing`
#[spec(ensures: |ret| ret.0 == (hash.0 ^ value.0).wrapping_mul(FNV_PRIME))]
fn stable_mix(
    hash: StableHash,
    value: StableHash,
) -> StableHash
{
    StableHash((hash.0 ^ value.0).wrapping_mul(FNV_PRIME))
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::vec;

    use gandr_surface_syntax::MoldId;
    use gandr_theory_graphs::Assoc;
    use gandr_theory_graphs::End;
    use gandr_theory_graphs::Prec;
    use gandr_theory_graphs::PrecDag;
    use gandr_theory_graphs::PrecIndex;
    use gandr_theory_graphs::PrecSpec;
    use gandr_theory_graphs::SeenKeyVerdict;
    use gandr_theory_graphs::WalkChainLength;
    use gandr_theory_graphs::WalkSym as _;

    use super::FNV_OFFSET;
    use super::GrammarNonterminal;
    use super::GrammarTile;
    use super::GrammarWalkSym;
    use super::MAX_WALK_CHAIN_LEN;
    use super::MoldFacts;
    use super::StableHash;
    use super::build_spec;
    use super::comparison_table;
    use super::descent_walk;
    use super::fact_at;
    use super::group_reps;
    use super::level_walk;
    use super::reachable_molds;
    use super::seen_key_verdict;
    use super::stable_mix;
    use super::walk_index;
    use crate::model::Pbg;
    use crate::model::Regex;
    use crate::model::Rule;
    use crate::model::RuleName;
    use crate::model::Sort;
    use crate::model::TileLabel;

    #[test]
    fn whole_word_keys_keep_their_fields_and_framing()
    {
        for (hash, value, expected) in [
            (FNV_OFFSET, 97_u64, 0xaf63_dc4c_8601_ec8c_u64),
            (0, 0, 0),
            (u64::MAX, u64::MAX, 0),
            (u64::MAX, 0, 0xffff_feff_ffff_fe4d),
        ] {
            assert_eq!(expected, stable_mix(StableHash(hash), StableHash(value)).0);
        }
        let group = GrammarNonterminal::new(Sort::Expression, Prec::new(PrecIndex::from(7)));
        assert_eq!(
            0x0839_5107_b4f1_3126_u64,
            u64::from(GrammarWalkSym::nonterminal_key(&group))
        );
        for changed in [
            GrammarNonterminal::new(Sort::Type, group.prec),
            GrammarNonterminal::new(group.sort, Prec::new(PrecIndex::from(0x0107))),
        ] {
            assert_ne!(
                GrammarWalkSym::nonterminal_key(&group),
                GrammarWalkSym::nonterminal_key(&changed)
            );
        }
        let tile = GrammarTile::new(TileLabel("on"), MoldId::from(7), Sort::Expression);
        assert_eq!(
            0x7395_a990_3be7_389f_u64,
            u64::from(GrammarWalkSym::stance_key(&tile))
        );
        for changed in [
            GrammarTile::new(tile.label, tile.mold_id, Sort::Type),
            GrammarTile::new(tile.label, MoldId::from(0x0107), tile.sort),
            GrammarTile::new(TileLabel("no"), tile.mold_id, tile.sort),
            GrammarTile::new(TileLabel("o"), tile.mold_id, tile.sort),
        ] {
            assert_ne!(
                GrammarWalkSym::stance_key(&tile),
                GrammarWalkSym::stance_key(&changed)
            );
        }
    }

    #[test]
    fn single_swings_preserve_nonterminal_order()
    {
        let outer = GrammarNonterminal::new(Sort::Expression, Prec::new(PrecIndex::from(0)));
        for inner in [
            outer,
            GrammarNonterminal::new(Sort::Type, Prec::new(PrecIndex::from(u16::MAX))),
        ] {
            let level = level_walk(inner).expect("one nonterminal is a valid swing");
            assert_eq!(
                [inner],
                level.swings().first().expect("one swing").nonterminals()
            );
            assert_eq!(1, level.swings().len());
            assert!(level.stances().is_empty());
            let descent = descent_walk(outer, inner).expect("two nonterminals are a valid swing");
            assert_eq!(
                [outer, inner],
                descent.swings().first().expect("one swing").nonterminals()
            );
            assert_eq!(1, descent.swings().len());
            assert!(descent.stances().is_empty());
        }
    }

    #[test]
    fn representatives_and_slots_keep_the_first_identity()
    {
        let low = Prec::new(PrecIndex::from(0));
        let high = Prec::new(PrecIndex::from(1));
        let facts = [
            (0_u32, Sort::Expression, low, "a"),
            (1, Sort::Expression, low, "b"),
            (2, Sort::Type, low, "T"),
            (3, Sort::Expression, high, "c"),
        ]
        .map(|(id, sort, prec, label)| MoldFacts {
            stance: GrammarTile::new(TileLabel(label), MoldId::from(id), sort),
            nonterminal: GrammarNonterminal::new(sort, prec),
        });
        let observed: BTreeMap<_, _> = group_reps(&facts)
            .into_iter()
            .map(|(key, fact)| (key, fact.stance.mold_id))
            .collect();
        assert_eq!(
            BTreeMap::from([
                ((Sort::Expression, low), MoldId::from(0)),
                ((Sort::Type, low), MoldId::from(2)),
                ((Sort::Expression, high), MoldId::from(3)),
            ]),
            observed
        );
        assert!(group_reps(&[]).is_empty());
        for (id, label) in [(0_u32, "a"), (3, "c")] {
            assert_eq!(
                Some(TileLabel(label)),
                fact_at(&facts, MoldId::from(id)).map(|fact| fact.stance.label)
            );
        }
        for id in [4_u32, u32::MAX] {
            assert!(fact_at(&facts, MoldId::from(id)).is_none());
        }
        assert!(fact_at(&[], MoldId::from(0)).is_none());
    }

    #[test]
    fn empty_grammar_has_only_the_root()
    {
        let mut spec = PrecSpec::new();
        spec.insert("base", Assoc::Non).expect("one group");
        let pbg = Pbg::build(PrecDag::build(&spec).expect("acyclic"), vec![]).expect("no rules");
        assert_eq!(
            WalkChainLength::from(MAX_WALK_CHAIN_LEN),
            build_spec(&pbg).expect("valid cap").max_chain_len()
        );
        let index = walk_index(&pbg).expect("empty grammar");
        assert_eq!([End::Root], index.ends());
        assert!(reachable_molds(&pbg, &index).is_empty());
        assert!(comparison_table(&pbg, &index).is_empty());
        assert_eq!(Ok(SeenKeyVerdict::Equivalent), seen_key_verdict(&pbg));
    }

    #[test]
    fn incomparable_forms_project_without_comparisons()
    {
        let mut spec = PrecSpec::new();
        let first = spec.insert("first", Assoc::Non).expect("first group");
        let second = spec.insert("second", Assoc::Non).expect("second group");
        let pbg = Pbg::build(PrecDag::build(&spec).expect("no edges"), vec![
            Rule::new(
                RuleName("x"),
                Sort::Expression,
                first,
                Regex::tile(TileLabel("x")),
            ),
            Rule::new(
                RuleName("T"),
                Sort::Type,
                first,
                Regex::tile(TileLabel("T")),
            ),
            Rule::new(
                RuleName("y"),
                Sort::Expression,
                second,
                Regex::tile(TileLabel("y")),
            ),
        ])
        .expect("distinct forms");
        let index = walk_index(&pbg).expect("independent groups");
        let projected: BTreeMap<_, _> = reachable_molds(&pbg, &index)
            .into_iter()
            .map(|(label, ids)| (label, ids.into_iter().collect::<alloc::vec::Vec<_>>()))
            .collect();
        assert_eq!(
            BTreeMap::from([
                (TileLabel("x"), vec![MoldId::from(0)]),
                (TileLabel("T"), vec![MoldId::from(1)]),
                (TileLabel("y"), vec![MoldId::from(2)]),
            ]),
            projected
        );
        assert!(comparison_table(&pbg, &index).is_empty());
        assert_eq!(Ok(SeenKeyVerdict::Equivalent), seen_key_verdict(&pbg));
    }
}
