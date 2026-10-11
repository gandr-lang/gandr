//! The mold table and the interned regex-context table.
//!
//! A mold is a tile occurrence's zipper into the grammar — its label, the
//! interned context of its position in its rule's form, the form's precedence
//! and the form's sort — never an opaque shape code. The table holds one
//! [`MoldDef`] per tile occurrence with its precedence bounds and zipper steps
//! precomputed; the [`MoldId`] a tree carries indexes it.
//!
//! Ids are assigned at build in canonical order: rules in input order, each
//! rule's form left to right. Two occurrences that intern to the same label
//! and context are redundant and refused as [`PbgError::DuplicateTile`];
//! occurrences at structurally distinct positions receive distinct contexts.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::EdgeSource;
use gandr_theory_graphs::Fnv64;
use gandr_theory_graphs::NodeCount;
use gandr_theory_graphs::NodeId;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::condensation;

use crate::model::CandidateCount;
use crate::model::MoldCount;
use crate::model::PbgError;
use crate::model::RegexShape;
use crate::model::RegexView;
use crate::model::Rule;
use crate::model::Sort;
use crate::model::Sym;
use crate::model::TileLabel;

/// The frame byte that opens the mold-table region of the grammar
/// fingerprint.
const FRAME_MOLD: u8 = b'M';

/// An interned regex-zipper context: a position in one rule's form.
///
/// Occurrences at structurally identical positions (identical branches of an
/// alternation) share an id; occurrences at distinct positions do not. A
/// context is scoped to the rule whose form it indexes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RCtxId(u32);

impl From<u32> for RCtxId
{
    /// Reads a table position as a context id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<RCtxId> for u32
{
    /// Reads the table position back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: RCtxId) -> Self
    {
        id.0
    }
}

/// One symbol the zipper crosses stepping out of a context.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StepSym
{
    /// A hole of this sort faces the context on that side.
    Sort(Sort),
    /// A tile with this label faces the context on that side.
    Tile(&'static str),
}

/// One precomputed zipper step: the symbol crossed.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct RCtxStep
{
    /// The symbol crossed.
    pub crossed: StepSym,
}

/// One mold: a tile occurrence's zipper into the grammar.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MoldDef
{
    /// The tile's label.
    pub label: &'static str,
    /// The interned context of the occurrence in its rule's form.
    pub rctx: RCtxId,
    /// The precedence of the occurrence's form.
    pub prec: Prec,
    /// The sort of the occurrence's form.
    pub sort: Sort,
}

/// Precomputed properties of one interned context.
#[derive(Clone, Debug, Eq, PartialEq)]
struct RCtxData
{
    /// Whether a hole can face the context on the left.
    left_faces_sort: bool,
    /// Whether a hole can face the context on the right.
    right_faces_sort: bool,
    /// The symbols crossed stepping left, ascending.
    left_steps: Vec<RCtxStep>,
    /// The symbols crossed stepping right, ascending.
    right_steps: Vec<RCtxStep>,
}

/// Defines a transparent boolean answer with `From` conversions both ways.
macro_rules! mold_flag {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(bool);

        impl From<bool> for $name
        {
            /// Wraps the answer.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: bool) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for bool
        {
            /// Unwraps the answer.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

mold_flag! {
    /// Whether a mold has a same-form predecessor.
    MoldHasPredecessor
}

mold_flag! {
    /// Whether a mold has a same-form successor.
    MoldHasSuccessor
}

mold_flag! {
    /// Whether a mold can end its form only once a trailing hole is filled.
    MoldHasRequiredTail
}

mold_flag! {
    /// Whether a mold can open a form.
    MoldIsFormFirst
}

mold_flag! {
    /// Whether a mold can complete its form with no hole still required.
    MoldIsFormLast
}

mold_flag! {
    /// Whether two molds are same-form adjacent, left then right.
    MoldsAdjacent
}

/// The mold and context tables of a checked grammar.
#[derive(Clone, Debug)]
pub struct MoldTable
{
    /// The molds, by id.
    molds: Vec<MoldDef>,
    /// The interned contexts, by id.
    rctxs: Vec<RCtxData>,
    /// Each mold's precedence bounds, by id.
    bounds: Vec<(Bound<Prec>, Bound<Prec>)>,
    /// Each mold's rule, by id: its position in the rules the table was built
    /// from.
    owners: Vec<usize>,
    /// Each label's molds, ascending.
    candidates: BTreeMap<&'static str, Vec<MoldId>>,
    /// Each label's molds admissible where no form is open, ascending: those
    /// without a same-form predecessor, and the form-first ones.
    fresh: BTreeMap<&'static str, Vec<MoldId>>,
    /// The same-form adjacency, ascending and unique.
    adjacencies: Vec<(MoldId, MoldId)>,
    /// Where each mold's run of [`adjacencies`](Self::adjacencies) starts, by
    /// id, with the table's adjacency count last: the pairs whose left is
    /// mold `m` are `adjacencies[successor_starts[m] .. successor_starts[m +
    /// 1]]`.
    successor_starts: Vec<usize>,
    /// Whether each mold has a same-form predecessor, by id.
    has_pred: Vec<bool>,
    /// Whether each mold has a same-form successor, by id.
    has_succ: Vec<bool>,
    /// The molds that can open a form, ascending.
    form_first: Vec<MoldId>,
    /// Whether each mold is in [`form_first`](Self::form_first), by id.
    is_first: Vec<bool>,
    /// The molds that can end a form, ascending.
    form_last: Vec<MoldId>,
    /// The form-last molds whose remainder needs no hole, ascending.
    complete_last: Vec<MoldId>,
    /// Whether each mold is in [`complete_last`](Self::complete_last), by id.
    is_complete_last: Vec<bool>,
    /// The form-last molds whose remainder needs a hole, ascending.
    required_tail: Vec<MoldId>,
    /// Whether each mold is in [`required_tail`](Self::required_tail), by id.
    is_required_tail: Vec<bool>,
    /// Each mold's closing class, by id; derived within the mold's own rule.
    closing: Vec<Option<ClosingClass>>,
    /// The precedence DAG's fingerprint folded with these tables.
    fingerprint: GrammarFingerprint,
}

impl MoldTable
{
    /// Builds the mold and context tables of `rules`.
    ///
    /// # Specification
    /// - requires: `rules` passed the header and Operator Form gates.
    /// - ensures: one mold per tile occurrence, numbered in rule order and left
    ///   to right within a rule; contexts are interned in first-seen order; the
    ///   fingerprint folds `dag_fingerprint` with both tables.
    /// - fails: two occurrences that intern to one label and context, or a
    ///   table past the 32-bit id.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::DuplicateTile`] for the first redundant occurrence, or
    /// [`PbgError::MoldOverflow`].
    ///
    /// # Adequacy
    /// - hypothesis: For finite checked rule lists, L3 duplicate-context and
    ///   ordered-owner observations plus a built-in finite inventory catch
    ///   misaligned tables, invalid context ids and wrong ownership. The
    ///   predicate checks adjacency order, same-owner edges, exact incoming and
    ///   outgoing flags, the dense form-membership flags against their lists
    ///   and each mold's successor run against the pair list once at
    ///   construction; every built-in mold's flags and run, and the first id
    ///   past the table, are compared with the lists through the public
    ///   queries. 32-bit exhaustion is outside the allocated fixtures.
    /// - witness: `tests::pbg::pbg_rejects_duplicate_rctx_tile`
    /// - witness: `tests::pbg::pbg_accepts_same_label_at_distinct_contexts`
    /// - witness: `tests::surface::every_mold_resolves_to_its_rule_and_named_kind`
    /// - witness: `tests::walk::declared_mold_candidate_inventory_is_exact`
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |error| matches!(error, PbgError::DuplicateTile { .. } | PbgError::MoldOverflow),
        |table| {
            let count = table.molds.len();
            table.bounds.len() == count && table.owners.len() == count && table.closing.len() == count && table.has_pred.len() == count && table.has_succ.len() == count && table.is_first.len() == count && table.is_complete_last.len() == count && table.is_required_tail.len() == count && table.successor_starts.len() == count.saturating_add(1)
                && table.owners.is_sorted()
                && table.molds.iter().zip(&table.owners).all(|(mold, &owner)| rules.get(owner).is_some_and(|rule| mold.sort == rule.sort && mold.prec == rule.prec) && usize::try_from(mold.rctx.0).is_ok_and(|index| index < table.rctxs.len()))
                && table.adjacencies.iter().is_sorted_by(|left, right| left < right)
                && {
                    let mut incidence = vec![(false, false); count];
                    for &(left, right) in &table.adjacencies {
                        let Some((left_index, right_index)) = usize::try_from(u32::from(left)).ok().zip(usize::try_from(u32::from(right)).ok()) else { return false; };
                        if table.owners.get(left_index).zip(table.owners.get(right_index)).is_none_or(|(left_owner, right_owner)| left_owner != right_owner) { return false; }
                        let Some(left_flags) = incidence.get_mut(left_index) else { return false; };
                        left_flags.1 = true;
                        let Some(right_flags) = incidence.get_mut(right_index) else { return false; };
                        right_flags.0 = true;
                    }
                    incidence.iter().zip(&table.has_pred).zip(&table.has_succ).all(|((&(incoming, outgoing), &has_pred), &has_succ)| incoming == has_pred && outgoing == has_succ)
                }
                && [(&table.form_first, &table.is_first), (&table.complete_last, &table.is_complete_last), (&table.required_tail, &table.is_required_tail)].into_iter().all(|(list, flags)| flags.iter().enumerate().all(|(position, &flag)| flag == MoldId::try_from(position).is_ok_and(|mold| list.contains(&mold))))
                && table.successor_starts.first().is_none_or(|&start| start == 0)
                && table.successor_starts.last().is_none_or(|&end| end == table.adjacencies.len())
                && table.successor_starts.windows(2).enumerate().all(|(position, pair)| match *pair { [start, end] => table.adjacencies.get(start .. end).is_some_and(|run| run.iter().all(|&(left, _)| usize::try_from(u32::from(left)) == Ok(position))), _ => false })
        }))]
    pub(crate) fn build(
        rules: &[Rule],
        dag_fingerprint: GrammarFingerprint,
    ) -> Result<Self, PbgError>
    {
        let mut interner = ContextInterner::new();
        let mut molds: Vec<MoldDef> = Vec::new();
        let mut identity: BTreeMap<TileKey, &'static str> = BTreeMap::new();
        let mut candidates: BTreeMap<&'static str, Vec<MoldId>> = BTreeMap::new();
        let mut adjacent_keys: BTreeSet<(TileKey, TileKey)> = BTreeSet::new();
        let mut first_keys: BTreeSet<TileKey> = BTreeSet::new();
        let mut form_last_keys: BTreeSet<TileKey> = BTreeSet::new();
        let mut complete_last_keys: BTreeSet<TileKey> = BTreeSet::new();
        let mut required_tail_keys: BTreeSet<TileKey> = BTreeSet::new();
        let mut closing: Vec<Option<ClosingClass>> = Vec::new();
        let mut owners: Vec<usize> = Vec::new();

        for (owner, rule) in rules.iter().enumerate() {
            let mut occurrences = Vec::new();
            let facet = collect_occurrences(rule, &mut interner, &mut occurrences);
            first_keys.extend(facet.first.iter().copied());
            form_last_keys.extend(facet.last.iter().copied());
            complete_last_keys.extend(facet.complete_last.iter().copied());
            required_tail_keys.extend(facet.last.difference(&facet.complete_last).copied());
            // Derived per rule, not table-wide: the class is a property of this
            // form's completions, and a table-wide walk would cross into other
            // rules.
            closing.extend(closing_classes(&occurrences, &facet));
            adjacent_keys.extend(facet.adjacent);
            for occurrence in occurrences {
                let key = TileKey::new(TileLabel(occurrence.label), occurrence.rctx);
                if let Some(first_rule) = identity.get(&key) {
                    return Err(PbgError::DuplicateTile {
                        label: occurrence.label,
                        sort: rule.sort,
                        prec: rule.prec,
                        first_rule,
                        second_rule: rule.name,
                    });
                }
                let mold_id =
                    MoldId::try_from(molds.len()).map_err(|_error| PbgError::MoldOverflow)?;
                identity.insert(key, rule.name);
                molds.push(MoldDef {
                    label: occurrence.label,
                    rctx: occurrence.rctx,
                    prec: rule.prec,
                    sort: rule.sort,
                });
                owners.push(owner);
                candidates
                    .entry(occurrence.label)
                    .or_default()
                    .push(mold_id);
            }
        }

        let rctxs = interner.finish();
        let bounds = molds
            .iter()
            .map(|mold| bounds_for(mold, &rctxs))
            .collect::<Vec<_>>();
        let index = tile_index(&molds);
        let adjacencies = resolve_adjacencies(&index, &adjacent_keys);
        let form_first = resolve_keys(&index, &first_keys);
        let form_last = resolve_keys(&index, &form_last_keys);
        let complete_last = resolve_keys(&index, &complete_last_keys);
        let required_tail = resolve_keys(&index, &required_tail_keys);
        // Dense per-mold flags: the fresh-menu filter probes them once per
        // mold, and the form-membership queries read them directly.
        let mut has_pred = vec![false; molds.len()];
        let mut has_succ = vec![false; molds.len()];
        for &(left, right) in &adjacencies {
            if let Ok(raw) = usize::try_from(u32::from(left))
                && let Some(slot) = has_succ.get_mut(raw)
            {
                *slot = true;
            }
            if let Ok(raw) = usize::try_from(u32::from(right))
                && let Some(slot) = has_pred.get_mut(raw)
            {
                *slot = true;
            }
        }
        let mut is_first = vec![false; molds.len()];
        let mut is_complete_last = vec![false; molds.len()];
        let mut is_required_tail = vec![false; molds.len()];
        for (list, flags) in [
            (&form_first, &mut is_first),
            (&complete_last, &mut is_complete_last),
            (&required_tail, &mut is_required_tail),
        ] {
            for &mold in list {
                if let Ok(raw) = usize::try_from(u32::from(mold))
                    && let Some(slot) = flags.get_mut(raw)
                {
                    *slot = true;
                }
            }
        }
        // Where each mold's run of the ascending pair list starts, the pair
        // count last: count each mold's pairs one slot past it, then
        // accumulate.
        let mut successor_starts = vec![0_usize; molds.len().saturating_add(1)];
        for &(left, _right) in &adjacencies {
            if let Some(slot) = usize::try_from(u32::from(left))
                .ok()
                .and_then(|raw| raw.checked_add(1))
                .and_then(|next| successor_starts.get_mut(next))
            {
                *slot = slot.saturating_add(1);
            }
        }
        let mut running = 0_usize;
        for start in &mut successor_starts {
            running = running.saturating_add(*start);
            *start = running;
        }
        let fresh = candidates
            .iter()
            .map(|(&label, label_molds)| {
                let fresh = label_molds
                    .iter()
                    .copied()
                    .filter(|mold| {
                        let at = usize::try_from(u32::from(*mold)).unwrap_or(usize::MAX);
                        let pred = has_pred.get(at).copied().unwrap_or(true);
                        let first = is_first.get(at).copied().unwrap_or(false);
                        !pred || first
                    })
                    .collect::<Vec<_>>();
                (label, fresh)
            })
            .collect();
        let fingerprint = fold_fingerprint(dag_fingerprint, &molds, &rctxs);
        Ok(Self {
            molds,
            rctxs,
            bounds,
            owners,
            candidates,
            fresh,
            adjacencies,
            successor_starts,
            has_pred,
            has_succ,
            form_first,
            is_first,
            form_last,
            complete_last,
            is_complete_last,
            required_tail,
            is_required_tail,
            closing,
            fingerprint,
        })
    }

    /// The mold `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the mold at `id`.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For a finite table, L3 first, last and first-invalid mold
    ///   observations catch wrong indexing, a copied or substituted entry and
    ///   incorrect refusal identity; very large identities are not exhaustively
    ///   exercised.
    /// - witness: `tests::walk::mold_lookup_checks_bounds`
    #[spec(ensures: |ret| {
        let expected = usize::try_from(u32::from(id)).ok().and_then(|index| self.molds.get(index));
        ret.as_ref().map_or_else(|error| expected.is_none() && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id), |mold| expected.is_some_and(|held| core::ptr::eq(core::ptr::from_ref(*mold), core::ptr::from_ref(held))))
    })]
    #[inline]
    pub(crate) fn mold(
        &self,
        id: MoldId,
    ) -> Result<&MoldDef, PbgError>
    {
        let index =
            usize::try_from(u32::from(id)).map_err(|_error| PbgError::UnknownMold { id })?;
        self.molds.get(index).ok_or(PbgError::UnknownMold { id })
    }

    /// The rule mold `id` belongs to, among the `rules` the table was built
    /// from.
    ///
    /// # Specification
    /// - requires: `rules` are the rules this table was built from, in the
    ///   order it was built from them.
    /// - ensures: returns the rule whose occurrence the mold was numbered for.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For the rules used to build the table, L2 built-in owner
    ///   census and L3 invalid-id observations catch shifted owners, cross-rule
    ///   aliases and lost refusal identity; the original-rule provenance
    ///   requirement is not reconstructed from unrelated rule lists.
    /// - witness: `tests::surface::every_mold_resolves_to_its_rule_and_named_kind`
    #[spec(ensures: |ret| {
        let expected = usize::try_from(u32::from(id)).ok().and_then(|index| self.owners.get(index)).and_then(|&owner| rules.get(owner));
        ret.as_ref().map_or_else(|error| expected.is_none() && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id), |rule| expected.is_some_and(|held| core::ptr::eq(core::ptr::from_ref(*rule), core::ptr::from_ref(held))))
    })]
    #[inline]
    pub(crate) fn rule_of<'rules>(
        &self,
        rules: &'rules [Rule],
        id: MoldId,
    ) -> Result<&'rules Rule, PbgError>
    {
        let index =
            usize::try_from(u32::from(id)).map_err(|_error| PbgError::UnknownMold { id })?;
        let owner = self
            .owners
            .get(index)
            .copied()
            .ok_or(PbgError::UnknownMold { id })?;
        rules.get(owner).ok_or(PbgError::UnknownMold { id })
    }

    /// The precedence bounds of mold `id`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the bounds precomputed for `id`.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For valid infix, prefix and atom molds and the first
    ///   invalid id, L3 side-specific observations catch swapped or misindexed
    ///   bounds and mistaken acceptance; the fixtures do not enumerate every
    ///   form.
    /// - witness: `tests::walk::mold_bounds_follow_context_nullability`
    /// - witness: `tests::walk::mold_lookup_checks_bounds`
    #[spec(ensures: |ret| {
        let expected = usize::try_from(u32::from(id)).ok().and_then(|index| self.bounds.get(index));
        ret.as_ref().map_or_else(|error| expected.is_none() && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id), |bounds| expected == Some(bounds))
    })]
    #[inline]
    pub(crate) fn bounds(
        &self,
        id: MoldId,
    ) -> Result<(Bound<Prec>, Bound<Prec>), PbgError>
    {
        let index =
            usize::try_from(u32::from(id)).map_err(|_error| PbgError::UnknownMold { id })?;
        self.bounds
            .get(index)
            .copied()
            .ok_or(PbgError::UnknownMold { id })
    }

    /// The symbols crossed stepping out of `rctx` in direction `dir`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the steps precomputed for that side.
    /// - fails: a context id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownRCtx`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For both sides of an infix context and an unknown id, L3
    ///   exact step and refusal observations catch direction reversal,
    ///   truncation and incorrect error payloads; arbitrary context languages
    ///   are outside the finite witness.
    /// - witness: `tests::walk::rctx_steps_cross_adjacent_symbols`
    /// - witness: `tests::walk::unknown_context_preserves_its_identity`
    #[spec(ensures: |ret| {
        let expected = usize::try_from(rctx.0).ok().and_then(|index| self.rctxs.get(index)).map(|data| match dir { Dir::Left => data.left_steps.as_slice(), Dir::Right => data.right_steps.as_slice() });
        ret.as_ref().map_or_else(|error| expected.is_none() && matches!(error, PbgError::UnknownRCtx { rctx: missing } if *missing == rctx), |steps| expected == Some(*steps))
    })]
    #[inline]
    pub(crate) fn step(
        &self,
        rctx: RCtxId,
        dir: Dir,
    ) -> Result<&[RCtxStep], PbgError>
    {
        let index =
            usize::try_from(u32::from(rctx)).map_err(|_error| PbgError::UnknownRCtx { rctx })?;
        let data = self
            .rctxs
            .get(index)
            .ok_or(PbgError::UnknownRCtx { rctx })?;
        Ok(match dir {
            | Dir::Left => &data.left_steps,
            | Dir::Right => &data.right_steps,
        })
    }

    /// Every mold `label` can take, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn candidates(
        &self,
        label: TileLabel,
    ) -> &[MoldId]
    {
        self.candidates
            .get(label.as_ref())
            .map_or(&[], Vec::as_slice)
    }

    /// The molds `label` can take where no form is open, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn fresh_candidates(
        &self,
        label: TileLabel,
    ) -> &[MoldId]
    {
        self.fresh.get(label.as_ref()).map_or(&[], Vec::as_slice)
    }

    /// Every declared label with its mold count, ascending by label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn candidate_counts(&self) -> Vec<(TileLabel, CandidateCount)>
    {
        self.candidates
            .iter()
            .map(|(&label, molds)| (TileLabel(label), CandidateCount(molds.len())))
            .collect()
    }

    /// The same-form adjacency, ascending and unique.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn adjacencies(&self) -> &[(MoldId, MoldId)]
    {
        &self.adjacencies
    }

    /// The adjacency pairs whose left is `mold`, ascending; empty past the
    /// table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the pairs of [`adjacencies`](Self::adjacencies) whose
    ///   left is `mold`, in their order; empty for an id outside the table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every built-in mold's run compares with a filter of
    ///   the whole adjacency, and the first id past the table reads empty; an
    ///   off-by-one start or a neighbor's run changes a comparison.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.adjacencies.iter().copied().filter(|&(left, _)| left == mold)))]
    #[inline]
    #[must_use]
    pub(crate) fn successors(
        &self,
        mold: MoldId,
    ) -> &[(MoldId, MoldId)]
    {
        let raw = usize::try_from(u32::from(mold)).ok();
        let start = raw.and_then(|raw| self.successor_starts.get(raw)).copied();
        let end = raw
            .and_then(|raw| raw.checked_add(1))
            .and_then(|next| self.successor_starts.get(next))
            .copied();
        start
            .zip(end)
            .and_then(|(start, end)| self.adjacencies.get(start .. end))
            .unwrap_or_default()
    }

    /// Whether `left` then `right` are same-form adjacent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when `(left, right)` is in
    ///   [`adjacencies`](Self::adjacencies).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every built-in adjacency pair and every mold's
    ///   reversed and absent pairs compare with the whole list; a search in the
    ///   wrong run changes a comparison.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.0 == self.adjacencies.contains(&(left, right)))]
    #[inline]
    #[must_use]
    pub(crate) fn adjacent(
        &self,
        left: MoldId,
        right: MoldId,
    ) -> MoldsAdjacent
    {
        MoldsAdjacent::from(self.successors(left).binary_search(&(left, right)).is_ok())
    }

    /// Whether `mold` has a same-form predecessor; false past the table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stored predecessor flag, false for an id outside the
    ///   table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   finite adjacency and L3 boundary observations catch direction swaps
    ///   and out-of-range truth; unrelated malformed internal tables are
    ///   excluded.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.0 == usize::try_from(u32::from(mold)).ok().and_then(|index| self.has_pred.get(index)).copied().unwrap_or(false))]
    #[inline]
    #[must_use]
    pub(crate) fn has_predecessor(
        &self,
        mold: MoldId,
    ) -> MoldHasPredecessor
    {
        let held = usize::try_from(u32::from(mold))
            .ok()
            .and_then(|raw| self.has_pred.get(raw))
            .copied()
            .unwrap_or(false);
        MoldHasPredecessor::from(held)
    }

    /// Whether `mold` has a same-form successor; false past the table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stored successor flag, false for an id outside the table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   finite adjacency and L3 boundary observations catch direction swaps
    ///   and out-of-range truth; unrelated malformed internal tables are
    ///   excluded.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.0 == usize::try_from(u32::from(mold)).ok().and_then(|index| self.has_succ.get(index)).copied().unwrap_or(false))]
    #[inline]
    #[must_use]
    pub(crate) fn has_successor(
        &self,
        mold: MoldId,
    ) -> MoldHasSuccessor
    {
        let held = usize::try_from(u32::from(mold))
            .ok()
            .and_then(|raw| self.has_succ.get(raw))
            .copied()
            .unwrap_or(false);
        MoldHasSuccessor::from(held)
    }

    /// Whether `mold` can open a form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly for membership in the first-mold list.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   membership and L3 boundary observations catch missed or invented form
    ///   openers.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.0 == self.form_first.contains(&mold))]
    #[inline]
    #[must_use]
    pub(crate) fn is_form_first(
        &self,
        mold: MoldId,
    ) -> MoldIsFormFirst
    {
        let held = usize::try_from(u32::from(mold))
            .ok()
            .and_then(|raw| self.is_first.get(raw))
            .copied()
            .unwrap_or(false);
        MoldIsFormFirst::from(held)
    }

    /// Whether `mold` can complete its form with no hole still required.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly for membership in the complete-last list.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For built-in molds, L2 membership and L3 prefix/infix
    ///   observations catch premature or lost clean completion.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    /// - witness: `tests::surface::infix_type_operator_keeps_clean_completion`
    #[spec(ensures: |ret| ret.0 == self.complete_last.contains(&mold))]
    #[inline]
    #[must_use]
    pub(crate) fn is_form_last(
        &self,
        mold: MoldId,
    ) -> MoldIsFormLast
    {
        let held = usize::try_from(u32::from(mold))
            .ok()
            .and_then(|raw| self.is_complete_last.get(raw))
            .copied()
            .unwrap_or(false);
        MoldIsFormLast::from(held)
    }

    /// Whether `mold` can end its form only once a trailing hole is filled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly for membership in the required-tail list.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For built-in molds and the first invalid id, L2 membership
    ///   and L3 prefix observations catch missing required operands and
    ///   invented tails; arbitrary form languages are not enumerated.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    /// - witness: `tests::surface::prefix_formers_keep_required_type_tails_unclosed`
    #[spec(ensures: |ret| ret.0 == self.required_tail.contains(&mold))]
    #[inline]
    #[must_use]
    pub(crate) fn has_required_tail(
        &self,
        mold: MoldId,
    ) -> MoldHasRequiredTail
    {
        let held = usize::try_from(u32::from(mold))
            .ok()
            .and_then(|raw| self.is_required_tail.get(raw))
            .copied()
            .unwrap_or(false);
        MoldHasRequiredTail::from(held)
    }

    /// The molds that can open a form, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn form_first(&self) -> &[MoldId]
    {
        &self.form_first
    }

    /// The molds that can end a form, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn form_last(&self) -> &[MoldId]
    {
        &self.form_last
    }

    /// The closing class of mold `id`; `None` past the table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stored closing class for a valid id, otherwise none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For paired, divergent and unpaired forms and the first
    ///   invalid id, L3 class observations catch wrong lookup offsets and
    ///   accidental fallback pairing; derivation of every possible form is not
    ///   exhausted.
    /// - witness: `tests::closing_class::closing_class_is_form_level`
    /// - witness: `tests::closing_class::closing_class_repeat_with_exit_shares_its_component_answer`
    #[spec(ensures: |ret| ret == usize::try_from(u32::from(id)).ok().and_then(|index| self.closing.get(index)).copied().flatten())]
    #[inline]
    pub(crate) fn closing_class(
        &self,
        id: MoldId,
    ) -> Option<ClosingClass>
    {
        let index = usize::try_from(u32::from(id)).ok()?;
        self.closing.get(index).copied().flatten()
    }

    /// How many molds the table holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn len(&self) -> MoldCount
    {
        MoldCount(self.molds.len())
    }

    /// Every mold with its id, ascending.
    ///
    /// # Specification
    /// - requires: every stored position fits a mold id.
    /// - ensures: yields each mold once with its position, in ascending order.
    /// - panics: none.
    /// - executable: none — the specification macro cannot name this opaque
    ///   iterator return; the caller owns its cursor.
    ///
    /// # Adequacy
    /// - hypothesis: For the finite built-in table, L2 projection observations
    ///   catch missing and duplicate mold ids; arbitrary huge tables and cursor
    ///   interleavings are outside the witness.
    /// - witness: `tests::walk::walk_index_projects_every_mold_once`
    #[inline]
    pub(crate) fn iter(&self) -> impl Iterator<Item = (MoldId, &MoldDef)>
    {
        self.molds
            .iter()
            .enumerate()
            .filter_map(|(index, def)| MoldId::try_from(index).ok().map(|id| (id, def)))
    }

    /// The precedence DAG's fingerprint folded with these tables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn fingerprint(&self) -> GrammarFingerprint
    {
        self.fingerprint
    }
}

/// One tile occurrence found walking a rule's form.
struct Occurrence
{
    /// The tile's label.
    label: &'static str,
    /// The occurrence's interned context.
    rctx: RCtxId,
}

/// Assigns dense context ids to canonical context paths, first seen first.
struct ContextInterner
{
    /// Each path's id. Lookup only; the id order is the insertion order.
    keys: BTreeMap<String, u32>,
    /// Each context's data, by id.
    data: Vec<RCtxData>,
}

impl ContextInterner
{
    /// An empty interner.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            keys: BTreeMap::new(),
            data: Vec::new(),
        }
    }

    /// Interns `key`, recording `data` the first time it is seen.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a key seen before returns its id and discards `data`; a new
    ///   key takes the next dense id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For repeated and distinct canonical keys, L3 interning
    ///   transitions observe stable identity, first-data retention and dense
    ///   insertion order, catching accidental replacement and gaps; the
    ///   saturating conversion past the 32-bit domain is not allocated by the
    ///   witness.
    /// - witness: `mold::tests::context_interning_keeps_first_data_and_dense_ids`
    #[spec(captures: before = (self.keys.get(&key).copied(), self.data.len()), ensures: |ret| match before.0 {
        Some(existing) => ret.0 == existing && self.data.len() == before.1,
        None => ret.0 == u32::try_from(before.1).unwrap_or(u32::MAX) && self.data.len() == before.1.saturating_add(1),
    })]
    fn intern(
        &mut self,
        key: String,
        data: RCtxData,
    ) -> RCtxId
    {
        if let Some(existing) = self.keys.get(&key) {
            return RCtxId::from(*existing);
        }
        let raw = u32::try_from(self.data.len()).unwrap_or(u32::MAX);
        self.keys.insert(key, raw);
        self.data.push(data);
        RCtxId::from(raw)
    }

    /// Releases the context table.
    ///
    /// # Specification
    /// trivial.
    fn finish(self) -> Vec<RCtxData>
    {
        self.data
    }
}

/// The symbols a form can begin and end with, and whether it can be empty.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FaceCtx
{
    /// Whether the form derives the empty sequence.
    nullable: bool,
    /// The symbols that can come first.
    first: BTreeSet<StepSym>,
    /// The symbols that can come last.
    last: BTreeSet<StepSym>,
}

impl FaceCtx
{
    /// The empty sequence's face.
    ///
    /// # Specification
    /// trivial.
    const fn empty() -> Self
    {
        Self {
            nullable: true,
            first: BTreeSet::new(),
            last: BTreeSet::new(),
        }
    }

    /// One symbol's face.
    ///
    /// # Specification
    /// trivial.
    fn leaf(sym: StepSym) -> Self
    {
        let set = BTreeSet::from([sym]);
        Self {
            nullable: false,
            first: set.clone(),
            last: set,
        }
    }
}

/// Walks one rule's form, collecting its tile occurrences and its adjacency
/// facet.
///
/// # Specification
/// trivial.
fn collect_occurrences(
    rule: &Rule,
    interner: &mut ContextInterner,
    out: &mut Vec<Occurrence>,
) -> TileFacet
{
    walk_regex(
        rule.regex().view(),
        &FaceCtx::empty(),
        &FaceCtx::empty(),
        RegexPath(rule.name),
        interner,
        out,
    )
}

/// A component's folded ending verdict in the closing-class derivation.
///
/// Three shapes for the three ways to be unsure or sure: no ending, endings
/// that agree, endings that do not. Both unsure answers surface as `None`.
#[derive(Clone, Copy, Eq, PartialEq)]
enum EndingVerdict
{
    /// No reachable ending.
    Empty,
    /// Every reachable ending closes this family.
    Agree(ClosingClass),
    /// Some reachable ending closes nothing the rule opened, or two disagree.
    Divergent,
}

impl EndingVerdict
{
    /// Folds one more ending's family in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: empty becomes agreement on `class`; agreement on `class`
    ///   stays; anything else is divergent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For empty, agreeing and divergent verdicts across bracket
    ///   families, L2 finite fold laws observe identity, absorption and
    ///   disagreement, catching an invented agreement or failure to retain a
    ///   matching class; this finite algebra does not establish graph
    ///   reachability.
    /// - witness: `mold::tests::ending_verdict_fold_has_identity_absorption_and_agreement`
    #[spec(ensures: |ret| ret == if self == Self::Empty || self == Self::Agree(class) { Self::Agree(class) } else { Self::Divergent })]
    fn merge_class(
        self,
        class: ClosingClass,
    ) -> Self
    {
        match self {
            | Self::Empty => Self::Agree(class),
            | Self::Agree(held) if held == class => self,
            | Self::Agree(_) | Self::Divergent => Self::Divergent,
        }
    }

    /// Folds a successor component's final verdict in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an empty successor changes nothing, an agreeing one folds its
    ///   family in, a divergent one makes this divergent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For all finite verdict pairs, L2 identity, absorption,
    ///   commutativity and associativity observations catch losing a successor
    ///   conflict or inventing an ending; graph condensation is witnessed
    ///   separately.
    /// - witness: `mold::tests::ending_verdict_fold_has_identity_absorption_and_agreement`
    #[spec(ensures: |ret| match successor { Self::Empty => ret == self, Self::Agree(class) => ret == self.merge_class(class), Self::Divergent => ret == Self::Divergent })]
    fn merge_successor(
        self,
        successor: Self,
    ) -> Self
    {
        match successor {
            | Self::Empty => self,
            | Self::Agree(class) => self.merge_class(class),
            | Self::Divergent => Self::Divergent,
        }
    }
}

/// One rule's tile-adjacency graph as dense successor rows.
#[repr(transparent)]
struct TileGraph
{
    /// Each node's successors.
    rows: Vec<Vec<NodeId>>,
}

impl EdgeSource for TileGraph
{
    type Successors<'successors>
        = core::iter::Copied<core::slice::Iter<'successors, NodeId>>
    where
        Self: 'successors;

    /// One node per row.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the row count, capped at the largest representable graph
    ///   count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For empty and multi-row adapters, L3 graph observations
    ///   catch off-by-one counts and dropped rows; the unallocatable capacity
    ///   boundary is checked by the conversion predicate rather than the
    ///   fixture.
    /// - witness: `mold::tests::tile_graph_preserves_successor_order_and_refuses_unknown_nodes`
    #[spec(ensures: |ret| u32::from(ret) == u32::try_from(self.rows.len()).unwrap_or(u32::MAX))]
    #[inline]
    fn node_count(&self) -> NodeCount
    {
        NodeCount::from(u32::try_from(self.rows.len()).unwrap_or(u32::MAX))
    }

    /// The node's row; none past the graph.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields exactly the selected row in its order, or nothing for
    ///   an unknown node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For a row with ordered repeated edges, an empty row and an
    ///   invalid node, L3 cursor observations catch sorting, deduplication or
    ///   wrong-row selection; larger graphs are outside the witness.
    /// - witness: `mold::tests::tile_graph_preserves_successor_order_and_refuses_unknown_nodes`
    #[spec(ensures: |ret| ret.clone().eq(usize::try_from(u32::from(node)).ok().and_then(|index| self.rows.get(index)).into_iter().flatten().copied()))]
    #[inline]
    fn successors(
        &self,
        node: NodeId,
    ) -> Self::Successors<'_>
    {
        let empty: &[NodeId] = &[];
        usize::try_from(u32::from(node))
            .ok()
            .and_then(|index| self.rows.get(index))
            .map_or_else(|| empty.iter().copied(), |row| row.iter().copied())
    }
}

/// Derives each occurrence's closing class within one rule.
///
/// `Some(c)` exactly when every completion path from the occurrence ends at a
/// closer of family `c`; `None` otherwise. `None` is the safe answer: a minted
/// close that names no family pairs with nothing, so its cost is a suppression
/// not applied rather than one applied wrongly.
///
/// - **Terminals, not neighbours.** An occurrence's completions are the rule's
///   LAST tiles it reaches through the rule's own adjacency. A repeat is
///   interior by construction: going round a member list changes nothing about
///   where the paths end, so a member's `=` inside `module M { … }` still
///   reaches only `}`.
/// - **Alternatives intersect.** Reaching two families, or a terminal that
///   closes nothing, is divergence. This keeps `def name = E ;` unclassed: its
///   completions end at `;`.
/// - **Paired, not merely closing.** A terminal `}` counts only when the rule
///   also writes an opener of that family.
///
/// The derivation runs on the rule's condensation. Every node in one
/// strongly connected component reaches the same endings, so each component is
/// folded once, sinks first, and every occurrence inside it shares the answer.
/// A per-node memo with a visiting set is not equivalent: on a repeat with an
/// exit (`a → b`, `b → a`, `b → )`), a search entering the cycle at `a` would
/// memoize `b` before the exit's family is known, and a later query from `b`
/// would read the incomplete entry.
///
/// # Specification
/// - requires: `occurrences` and `facet` come from one [`collect_occurrences`]
///   call.
/// - ensures: element `i` is `Some(c)` exactly when every completion path from
///   occurrence `i` ends at a closer of family `c` that the rule opens.
/// - panics: none.
/// - intension: one condensation and one sinks-first fold, linear in the rule's
///   tiles and adjacencies; a graph the condensation refuses gives every
///   occurrence `None`.
///
/// # Adequacy
/// - hypothesis: For paired, unpaired, divergent and cyclic-with-exit forms, L3
///   per-occurrence class observations catch pairing without an opener and
///   premature memoization; the predicate checks cardinality and family
///   provenance, not arbitrary reachability or the linear-time cost.
/// - witness: `tests::closing_class::closing_class_is_form_level`
/// - witness: `tests::closing_class::closing_class_repeat_with_exit_shares_its_component_answer`
#[spec(ensures: |ret| ret.len() == occurrences.len() && ret.iter().flatten().all(|&class| occurrences.iter().any(|occurrence| ClosingClass::opening(DelimSpelling::from(occurrence.label)) == Some(class)) && occurrences.iter().any(|occurrence| ClosingClass::closing(DelimSpelling::from(occurrence.label)) == Some(class))))]
fn closing_classes(
    occurrences: &[Occurrence],
    facet: &TileFacet,
) -> Vec<Option<ClosingClass>>
{
    // The families the rule opens; a closer of any other family is unpaired.
    let opened: BTreeSet<ClosingClass> = occurrences
        .iter()
        .filter_map(|occurrence| ClosingClass::opening(DelimSpelling::from(occurrence.label)))
        .collect();

    // The rule's tile graph, dense: every key the adjacency names, and every
    // occurrence, since an isolated occurrence is its own ending.
    let mut all: BTreeSet<TileKey> = BTreeSet::new();
    for &(left, right) in &facet.adjacent {
        all.insert(left);
        all.insert(right);
    }
    for occurrence in occurrences {
        all.insert(TileKey::new(TileLabel(occurrence.label), occurrence.rctx));
    }
    let keys: Vec<TileKey> = all.into_iter().collect();
    let dense: BTreeMap<TileKey, u32> = keys
        .iter()
        .copied()
        .enumerate()
        .map(|(index, key)| (key, u32::try_from(index).unwrap_or(u32::MAX)))
        .collect();
    let mut rows: Vec<Vec<NodeId>> = Vec::new();
    rows.resize_with(keys.len(), Vec::new);
    for &(left, right) in &facet.adjacent {
        let (Some(&source), Some(&target)) = (dense.get(&left), dense.get(&right))
        else {
            continue;
        };
        let Ok(index) = usize::try_from(source)
        else {
            continue;
        };
        if let Some(row) = rows.get_mut(index) {
            row.push(NodeId::from(target));
        }
    }
    let graph = TileGraph { rows };

    let Ok(condensed) = condensation(&graph)
    else {
        return vec![None; occurrences.len()];
    };

    // Successor and predecessor lists over the condensation.
    let component_count = condensed.components.len();
    let mut successors: Vec<Vec<usize>> = Vec::new();
    let mut predecessors: Vec<Vec<usize>> = Vec::new();
    successors.resize_with(component_count, Vec::new);
    predecessors.resize_with(component_count, Vec::new);
    for edge in &condensed.edges {
        let Ok(source) = usize::try_from(u32::from(edge.source))
        else {
            continue;
        };
        let Ok(target) = usize::try_from(u32::from(edge.target))
        else {
            continue;
        };
        if let Some(row) = successors.get_mut(source) {
            row.push(target);
        }
        if let Some(row) = predecessors.get_mut(target) {
            row.push(source);
        }
    }

    // Sinks first (Kahn's algorithm from the sink side): a component is folded
    // only once every successor's verdict is final.
    let mut out_degree: Vec<usize> = successors.iter().map(Vec::len).collect();
    let mut sinks: Vec<usize> = out_degree
        .iter()
        .enumerate()
        .filter_map(|(index, &degree)| (degree == 0).then_some(index))
        .collect();
    let mut order: Vec<usize> = Vec::new();
    while let Some(component) = sinks.pop() {
        order.push(component);
        let Some(row) = predecessors.get(component)
        else {
            continue;
        };
        for &predecessor in row {
            let Some(degree) = out_degree.get_mut(predecessor)
            else {
                continue;
            };
            *degree = degree.saturating_sub(1);
            if *degree == 0 {
                sinks.push(predecessor);
            }
        }
    }

    // Fold each component: its own endings, then its successors' verdicts. A
    // member is an ending when it has no successor or is in the rule's LAST
    // set.
    let mut verdicts: Vec<EndingVerdict> = vec![EndingVerdict::Empty; component_count];
    for &component in &order {
        let mut verdict = EndingVerdict::Empty;
        if let Some(members) = condensed.components.get(component) {
            for &node in members {
                let Ok(index) = usize::try_from(u32::from(node))
                else {
                    continue;
                };
                let Some(&key) = keys.get(index)
                else {
                    continue;
                };
                let has_successors = graph.rows.get(index).is_some_and(|row| !row.is_empty());
                if has_successors && !facet.last.contains(&key) {
                    continue;
                }
                verdict = match ClosingClass::closing(DelimSpelling::from(key.label().0))
                    .filter(|reached| opened.contains(reached))
                {
                    | Some(class) => verdict.merge_class(class),
                    | None => EndingVerdict::Divergent,
                };
            }
        }
        if let Some(row) = successors.get(component) {
            for &successor in row {
                if let Some(&found) = verdicts.get(successor) {
                    verdict = verdict.merge_successor(found);
                }
            }
        }
        if let Some(slot) = verdicts.get_mut(component) {
            *slot = verdict;
        }
    }

    // Every occurrence takes the answer of the component it starts in.
    let mut component_of: Vec<usize> = vec![usize::MAX; keys.len()];
    for (component, members) in condensed.components.iter().enumerate() {
        for &node in members {
            if let Ok(index) = usize::try_from(u32::from(node))
                && let Some(slot) = component_of.get_mut(index)
            {
                *slot = component;
            }
        }
    }
    occurrences
        .iter()
        .map(|occurrence| {
            let start = TileKey::new(TileLabel(occurrence.label), occurrence.rctx);
            let verdict = dense
                .get(&start)
                .and_then(|&node| usize::try_from(node).ok())
                .and_then(|index| component_of.get(index))
                .and_then(|&component| verdicts.get(component));
            match verdict {
                | Some(&EndingVerdict::Agree(class)) => Some(class),
                | Some(&(EndingVerdict::Empty | EndingVerdict::Divergent)) | None => None,
            }
        })
        .collect()
}

/// One pending step of [`walk_regex`].
enum WalkFrame<'regex>
{
    /// Visit a subtree with its surrounding faces and its context path.
    Enter
    {
        /// The subtree.
        regex: RegexView<'regex>,
        /// What can stand to its left.
        left: FaceCtx,
        /// What can stand to its right.
        right: FaceCtx,
        /// Its canonical context path.
        path: String,
    },
    /// Fold the last `count` facets as a sequence.
    FinishSeq
    {
        /// How many facets.
        count: usize,
    },
    /// Fold the last `count` facets as an alternation.
    FinishAlt
    {
        /// How many facets.
        count: usize,
    },
    /// Make the last facet optional.
    FinishOptional,
    /// Make the last facet a repetition.
    FinishRepeat,
}

/// Walks a form, interning each tile occurrence's context, and returns the
/// form's tile-adjacency facet.
///
/// Holes are tile-transparent: two tiles separated only by holes are
/// consecutive within their form, so `( E )` yields the pair `( ≐ )`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every tile occurrence is pushed to `out` in left-to-right order
///   with the context interned for its canonical path; the returned facet is
///   the form's.
/// - panics: none.
/// - intension: an explicit frame stack, so nesting depth costs heap rather
///   than call stack.
///
/// # Adequacy
/// - hypothesis: For sequences with optional and repeated tiles, L3 exact
///   occurrence and edge observations catch reordering, lost repetition seams
///   and wrong context identities; the predicate checks new references and
///   facet provenance without copying the existing output prefix.
/// - witness: `mold::tests::occurrence_order_and_nullable_seams_are_exact`
/// - witness: `tests::pbg::pbg_rejects_duplicate_rctx_tile`
#[spec(captures: start = out.len(), ensures: |ret| out.len() >= start
    && out.iter().skip(start).all(|occurrence| usize::try_from(occurrence.rctx.0).is_ok_and(|index| index < interner.data.len()))
    && ret.first.iter().chain(&ret.last).chain(&ret.complete_last).all(|key| out.iter().skip(start).any(|occurrence| key.0.0.0 == occurrence.label && key.0.1 == occurrence.rctx)))]
fn walk_regex(
    regex: RegexView<'_>,
    left: &FaceCtx,
    right: &FaceCtx,
    path: RegexPath<'_>,
    interner: &mut ContextInterner,
    out: &mut Vec<Occurrence>,
) -> TileFacet
{
    let mut frames = vec![WalkFrame::Enter {
        regex,
        left: left.clone(),
        right: right.clone(),
        path: String::from(path.0),
    }];
    let mut values = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            | WalkFrame::Enter {
                regex: node,
                left: node_left,
                right: node_right,
                path: node_path,
            } => match node.shape() {
                | RegexShape::Empty => values.push(TileFacet::empty()),
                | RegexShape::Sym(Sym::Sort(_)) => values.push(TileFacet::required_hole()),
                | RegexShape::Sym(Sym::Tile(tile)) => {
                    let data = context_data(&node_left, &node_right);
                    let rctx = interner.intern(node_path, data);
                    out.push(Occurrence {
                        label: tile.label,
                        rctx,
                    });
                    values.push(TileFacet::leaf(TileKey::new(TileLabel(tile.label), rctx)));
                },
                | RegexShape::Seq(items) => {
                    frames.push(WalkFrame::FinishSeq { count: items.len() });
                    // Each child's face and canonical form once, up front;
                    // recomputing them per position is quadratic in the
                    // sequence length.
                    let child_faces = items.iter().map(|&item| face_of(item)).collect::<Vec<_>>();
                    let child_canons = items.iter().map(|&item| canon(item)).collect::<Vec<_>>();
                    // Entry `i` of each table folds the faces before and after
                    // child `i`; composition is associative with the empty
                    // face as identity, so prefixes and suffixes are shared.
                    let capacity = items.len().saturating_add(1);
                    let mut before_face = Vec::with_capacity(capacity);
                    before_face.push(FaceCtx::empty());
                    for face in &child_faces {
                        let previous = before_face.last().cloned().unwrap_or_else(FaceCtx::empty);
                        before_face.push(compose_seq(&previous, face));
                    }
                    let mut after_face = Vec::with_capacity(capacity);
                    after_face.push(FaceCtx::empty());
                    for face in child_faces.iter().rev() {
                        let previous = after_face.last().cloned().unwrap_or_else(FaceCtx::empty);
                        after_face.push(compose_seq(face, &previous));
                    }
                    after_face.reverse();
                    for (index, &item) in items.iter().enumerate().rev() {
                        let before = before_face
                            .get(index)
                            .cloned()
                            .unwrap_or_else(FaceCtx::empty);
                        let after = after_face
                            .get(index.saturating_add(1))
                            .cloned()
                            .unwrap_or_else(FaceCtx::empty);
                        let child_left = compose_seq(&node_left, &before);
                        let child_right = compose_seq(&after, &node_right);
                        let frame_tag = format!(
                            "Q{}\x1e{}",
                            child_canons.get(.. index).unwrap_or(&[]).join(","),
                            child_canons
                                .get(index.saturating_add(1) ..)
                                .unwrap_or(&[])
                                .join(",")
                        );
                        frames.push(WalkFrame::Enter {
                            regex: item,
                            left: child_left,
                            right: child_right,
                            path: format!("{node_path}\x1f{frame_tag}"),
                        });
                    }
                },
                | RegexShape::Alt(items) => {
                    frames.push(WalkFrame::FinishAlt { count: items.len() });
                    // A branch's tag is the sorted join of its siblings'
                    // canonical forms: branches are unordered.
                    let child_canons = items.iter().map(|&item| canon(item)).collect::<Vec<_>>();
                    for (index, &item) in items.iter().enumerate().rev() {
                        let mut siblings: Vec<&str> = child_canons
                            .iter()
                            .enumerate()
                            .filter(|&(other_index, _)| other_index != index)
                            .map(|(_, child)| child.as_str())
                            .collect();
                        siblings.sort_unstable();
                        let frame_tag = format!("A{}", siblings.join("\x1d"));
                        frames.push(WalkFrame::Enter {
                            regex: item,
                            left: node_left.clone(),
                            right: node_right.clone(),
                            path: format!("{node_path}\x1f{frame_tag}"),
                        });
                    }
                },
                | RegexShape::Optional(inner) => {
                    frames.push(WalkFrame::FinishOptional);
                    frames.push(WalkFrame::Enter {
                        regex: inner,
                        left: node_left,
                        right: node_right,
                        path: format!("{node_path}\x1fO"),
                    });
                },
                | RegexShape::Repeat(inner) => {
                    frames.push(WalkFrame::FinishRepeat);
                    frames.push(WalkFrame::Enter {
                        regex: inner,
                        left: node_left,
                        right: node_right,
                        path: format!("{node_path}\x1fR"),
                    });
                },
            },
            | WalkFrame::FinishSeq { count } => {
                let split = values.len().saturating_sub(count);
                let children = values.split_off(split);
                let mut acc = TileFacet::empty();
                for child in children {
                    acc = seq_facet(&acc, &child);
                }
                values.push(acc);
            },
            | WalkFrame::FinishAlt { count } => {
                let split = values.len().saturating_sub(count);
                let children = values.split_off(split);
                let mut acc = TileFacet::void();
                for child in children {
                    acc = alt_facet(&acc, &child);
                }
                values.push(acc);
            },
            | WalkFrame::FinishOptional => {
                let mut child = values.pop().unwrap_or_else(TileFacet::empty);
                child.flags.set_nullable(FacetFlag::from(true));
                child.flags.set_form_nullable(FacetFlag::from(true));
                child.flags.set_required_first(FacetFlag::from(false));
                child.flags.set_required_last(FacetFlag::from(false));
                values.push(child);
            },
            | WalkFrame::FinishRepeat => {
                let child = values.pop().unwrap_or_else(TileFacet::empty);
                values.push(repeat_facet(&child));
            },
        }
    }

    values.pop().unwrap_or_else(TileFacet::empty)
}

/// Resolves tile keys to their molds, ascending and unique.
///
/// # Specification
/// - requires: nothing.
/// - ensures: resolves known keys to ascending distinct mold ids; unknown keys
///   contribute nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For reversed identities, aliases and a missing key, L3 exact
///   output observations catch key-order leakage, duplicate ids and accidental
///   inclusion of missing keys; arbitrary large indexes are not enumerated.
/// - witness: `mold::tests::resolutions_sort_deduplicate_and_skip_missing_keys`
#[spec(ensures: |ret| {
    if !ret.iter().is_sorted_by(|left, right| left < right) { return false; }
    let mut covered = vec![false; ret.len()];
    for value in keys.iter().filter_map(|key| index.get(key).copied()) {
        let Ok(position) = ret.binary_search(&value) else { return false; };
        let Some(slot) = covered.get_mut(position) else { return false; };
        *slot = true;
    }
    covered.into_iter().all(core::convert::identity)
})]
fn resolve_keys(
    index: &BTreeMap<TileKey, MoldId>,
    keys: &BTreeSet<TileKey>,
) -> Vec<MoldId>
{
    let mut ids: Vec<MoldId> = keys
        .iter()
        .filter_map(|key| index.get(key).copied())
        .collect();
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// Resolves tile-key pairs to mold pairs, ascending and unique.
///
/// # Specification
/// - requires: nothing.
/// - ensures: resolves fully known key pairs to ascending distinct mold pairs;
///   a missing endpoint drops the pair.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For alias keys, reversed ids and missing endpoints, L3 exact
///   edge observations catch half-resolved pairs, duplicate edges and wrong
///   ordering; arbitrary large indexes are outside the fixture.
/// - witness: `mold::tests::resolutions_sort_deduplicate_and_skip_missing_keys`
#[spec(ensures: |ret| {
    if !ret.iter().is_sorted_by(|left, right| left < right) { return false; }
    let mut covered = vec![false; ret.len()];
    for value in keys.iter().filter_map(|&(left, right)| index.get(&left).copied().zip(index.get(&right).copied())) {
        let Ok(position) = ret.binary_search(&value) else { return false; };
        let Some(slot) = covered.get_mut(position) else { return false; };
        *slot = true;
    }
    covered.into_iter().all(core::convert::identity)
})]
fn resolve_adjacencies(
    index: &BTreeMap<TileKey, MoldId>,
    keys: &BTreeSet<(TileKey, TileKey)>,
) -> Vec<(MoldId, MoldId)>
{
    let mut pairs: Vec<(MoldId, MoldId)> = keys
        .iter()
        .filter_map(|&(left, right)| index.get(&left).copied().zip(index.get(&right).copied()))
        .collect();
    pairs.sort_unstable();
    pairs.dedup();
    pairs
}

/// Indexes molds by tile key.
///
/// # Specification
/// - requires: mold keys are unique and every position fits a mold id.
/// - ensures: every key maps to its position, with no omitted or additional
///   entries.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For distinct ordered molds, L3 index inversion and built-in
///   adjacency observations catch shifted positions and omitted keys; duplicate
///   keys and unrepresentable positions are outside this caller-established
///   domain.
/// - witness: `mold::tests::resolutions_sort_deduplicate_and_skip_missing_keys`
/// - witness: `tests::walk::same_form_adjacency_is_the_eq_relation`
#[spec(ensures: |ret| ret.len() == molds.len() && ret.iter().all(|(key, &id)| usize::try_from(u32::from(id)).ok().and_then(|index| molds.get(index)).is_some_and(|mold| key.0.0.0 == mold.label && key.0.1 == mold.rctx)))]
fn tile_index(molds: &[MoldDef]) -> BTreeMap<TileKey, MoldId>
{
    molds
        .iter()
        .enumerate()
        .filter_map(|(position, mold)| {
            MoldId::try_from(position)
                .ok()
                .map(|id| (TileKey::new(TileLabel(mold.label), mold.rctx), id))
        })
        .collect()
}

/// A context's precomputed data from the faces either side of it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a side faces a sort exactly when a hole is among the symbols that
///   can stand there; the steps are those symbols, ascending.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For asymmetric faces containing both sorts and tiles, L3 exact
///   step observations catch using FIRST on the left, LAST on the right or
///   dropping sort-facing flags; arbitrary face sets are not exhausted.
/// - witness: `mold::tests::context_data_uses_left_last_and_right_first`
/// - witness: `tests::walk::rctx_steps_cross_adjacent_symbols`
#[spec(ensures: |ret| ret.left_faces_sort == left.last.iter().any(|symbol| matches!(symbol, StepSym::Sort(_))) && ret.right_faces_sort == right.first.iter().any(|symbol| matches!(symbol, StepSym::Sort(_))) && ret.left_steps.iter().map(|step| step.crossed).eq(left.last.iter().copied()) && ret.right_steps.iter().map(|step| step.crossed).eq(right.first.iter().copied()))]
fn context_data(
    left: &FaceCtx,
    right: &FaceCtx,
) -> RCtxData
{
    RCtxData {
        left_faces_sort: left.last.iter().any(|sym| matches!(sym, StepSym::Sort(_))),
        right_faces_sort: right
            .first
            .iter()
            .any(|sym| matches!(sym, StepSym::Sort(_))),
        left_steps: left
            .last
            .iter()
            .copied()
            .map(|crossed| RCtxStep { crossed })
            .collect(),
        right_steps: right
            .first
            .iter()
            .copied()
            .map(|crossed| RCtxStep { crossed })
            .collect(),
    }
}

/// A tile occurrence before mold ids exist: its label and context.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TileKey((TileLabel, RCtxId));

impl TileKey
{
    /// Pairs a label with a context.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        label: TileLabel,
        rctx: RCtxId,
    ) -> Self
    {
        Self((label, rctx))
    }

    /// The key's label.
    ///
    /// # Specification
    /// trivial.
    const fn label(self) -> TileLabel
    {
        self.0.0
    }
}

/// A rule's name as the root of its context paths.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RegexPath<'path>(&'path str);

/// Whether a hole can face a context on one side.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SortFacing(bool);

/// One of a [`FacetFlags`]' four answers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct FacetFlag(bool);

impl From<bool> for FacetFlag
{
    /// Wraps the answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: bool) -> Self
    {
        Self(value)
    }
}

impl From<FacetFlag> for bool
{
    /// Unwraps the answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: FacetFlag) -> Self
    {
        value.0
    }
}

/// A [`TileFacet`]'s four boolean answers, packed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct FacetFlags(u8);

/// One bit of a [`FacetFlags`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FacetBit(u8);

impl FacetFlags
{
    /// The subtree can be tile-empty.
    const NULLABLE: FacetBit = FacetBit(0b0001);
    /// The subtree can complete with no hole required.
    const FORM_NULLABLE: FacetBit = FacetBit(0b0010);
    /// A required hole can stand at the subtree's first edge.
    const REQUIRED_FIRST: FacetBit = FacetBit(0b0100);
    /// A required hole can stand at the subtree's last edge.
    const REQUIRED_LAST: FacetBit = FacetBit(0b1000);

    /// Packs the four answers, in field order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the four named answers read back in field order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For all sixteen input answer tuples and single-field
    ///   updates, L2 finite state observations catch exchanged fields and
    ///   interference; unused upper bits are checked separately through masked
    ///   updates.
    /// - witness: `mold::tests::facet_flag_updates_preserve_other_answers`
    #[spec(ensures: |ret| { let [nullable, form_nullable, required_first, required_last] = parts; ret.nullable().0 == nullable.0 && ret.form_nullable().0 == form_nullable.0 && ret.required_first().0 == required_first.0 && ret.required_last().0 == required_last.0 })]
    fn from_parts(parts: [FacetFlag; 4]) -> Self
    {
        let [nullable, form_nullable, required_first, required_last] = parts;
        let mut flags = Self::default();
        flags.set_nullable(nullable);
        flags.set_form_nullable(form_nullable);
        flags.set_required_first(required_first);
        flags.set_required_last(required_last);
        flags
    }

    /// Reads one bit.
    ///
    /// # Specification
    /// - requires: the mask is one of the four named bits.
    /// - ensures: reads exactly the selected bit.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every byte state and each named mask, L2 exhaustive
    ///   bit observations catch reading the wrong field; unnamed masks are
    ///   outside the precondition, and a constant-evaluation witness covers the
    ///   const path.
    /// - witness: `mold::tests::facet_flag_updates_preserve_other_answers`
    #[spec(requires: matches!(bit.0, 1 | 2 | 4 | 8), ensures: |ret| ret.0 == (self.0 & bit.0 != 0))]
    const fn get(
        self,
        bit: FacetBit,
    ) -> FacetFlag
    {
        FacetFlag(self.0 & bit.0 != 0)
    }

    /// Sets or clears one bit.
    ///
    /// # Specification
    /// - requires: the mask is one of the four named bits.
    /// - ensures: sets that answer and preserves every other bit.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every byte state, named mask and boolean update, L2
    ///   exhaustive transitions catch setting the wrong bit and clearing
    ///   unrelated state; unnamed masks are outside the precondition.
    /// - witness: `mold::tests::facet_flag_updates_preserve_other_answers`
    #[spec(requires: matches!(bit.0, 1 | 2 | 4 | 8), captures: before = self.0, ensures: |()| self.0 & !bit.0 == before & !bit.0 && (self.0 & bit.0 != 0) == value.0)]
    fn set(
        &mut self,
        bit: FacetBit,
        value: FacetFlag,
    )
    {
        if value.0 {
            self.0 |= bit.0;
        }
        else {
            self.0 &= !bit.0;
        }
    }

    /// Whether the subtree can be tile-empty.
    ///
    /// # Specification
    /// trivial.
    const fn nullable(self) -> FacetFlag
    {
        self.get(Self::NULLABLE)
    }

    /// Whether the subtree can complete with no hole required.
    ///
    /// # Specification
    /// trivial.
    const fn form_nullable(self) -> FacetFlag
    {
        self.get(Self::FORM_NULLABLE)
    }

    /// Whether a required hole can stand at the first edge.
    ///
    /// # Specification
    /// trivial.
    const fn required_first(self) -> FacetFlag
    {
        self.get(Self::REQUIRED_FIRST)
    }

    /// Whether a required hole can stand at the last edge.
    ///
    /// # Specification
    /// trivial.
    const fn required_last(self) -> FacetFlag
    {
        self.get(Self::REQUIRED_LAST)
    }

    /// Sets whether the subtree can be tile-empty.
    ///
    /// # Specification
    /// trivial.
    fn set_nullable(
        &mut self,
        value: FacetFlag,
    )
    {
        self.set(Self::NULLABLE, value);
    }

    /// Sets whether the subtree can complete with no hole required.
    ///
    /// # Specification
    /// trivial.
    fn set_form_nullable(
        &mut self,
        value: FacetFlag,
    )
    {
        self.set(Self::FORM_NULLABLE, value);
    }

    /// Sets whether a required hole can stand at the first edge.
    ///
    /// # Specification
    /// trivial.
    fn set_required_first(
        &mut self,
        value: FacetFlag,
    )
    {
        self.set(Self::REQUIRED_FIRST, value);
    }

    /// Sets whether a required hole can stand at the last edge.
    ///
    /// # Specification
    /// trivial.
    fn set_required_last(
        &mut self,
        value: FacetFlag,
    )
    {
        self.set(Self::REQUIRED_LAST, value);
    }
}

/// A subtree's tile-adjacency summary, built bottom-up.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct TileFacet
{
    /// Emptiness and required-hole edges.
    flags: FacetFlags,
    /// The tiles that can come first.
    first: BTreeSet<TileKey>,
    /// The tiles that can come last, holes skipped.
    last: BTreeSet<TileKey>,
    /// The tiles at which the subtree can complete with no hole required.
    ///
    /// Not derivable from `last`: an alternation can reach one tile through a
    /// complete path and a required-tail path.
    complete_last: BTreeSet<TileKey>,
    /// The consecutive tile pairs inside the subtree.
    adjacent: BTreeSet<(TileKey, TileKey)>,
}

impl TileFacet
{
    /// The identity of sequencing: tile-empty and complete.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the documented nullability and required-hole answers, with no
    ///   tile sets or adjacencies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For finite tile and required-hole facets, L3 left/right
    ///   sequencing identity observations catch an empty form that drops tiles
    ///   or requires an operand; arbitrary composite facets are not exhausted.
    /// - witness: `mold::tests::facet_composition_distinguishes_required_tails_and_empty_forms`
    #[spec(ensures: |ret| (ret.flags.0 == FacetFlags::NULLABLE.0 | FacetFlags::FORM_NULLABLE.0) && ret.first.is_empty() && ret.last.is_empty() && ret.complete_last.is_empty() && ret.adjacent.is_empty())]
    fn empty() -> Self
    {
        Self::with_flags([
            FacetFlag(true),
            FacetFlag(true),
            FacetFlag(false),
            FacetFlag(false),
        ])
    }

    /// A required hole: tile-empty but not complete.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the documented nullability and required-hole answers, with no
    ///   tile sets or adjacencies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For prefix and infix forms, L3 completion-set observations
    ///   distinguish a required hole from an empty form, catching erased
    ///   operands; arbitrary form languages are outside the witness.
    /// - witness: `mold::tests::facet_composition_distinguishes_required_tails_and_empty_forms`
    #[spec(ensures: |ret| (ret.flags.0 == FacetFlags::NULLABLE.0 | FacetFlags::REQUIRED_FIRST.0 | FacetFlags::REQUIRED_LAST.0) && ret.first.is_empty() && ret.last.is_empty() && ret.complete_last.is_empty() && ret.adjacent.is_empty())]
    fn required_hole() -> Self
    {
        Self::with_flags([
            FacetFlag(true),
            FacetFlag(false),
            FacetFlag(true),
            FacetFlag(true),
        ])
    }

    /// The identity of alternation: matches nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the documented nullability and required-hole answers, with no
    ///   tile sets or adjacencies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For finite tile facets, L3 alternation identity
    ///   observations catch a void branch that spuriously permits emptiness or
    ///   introduces an operand; arbitrary composite facets are not exhausted.
    /// - witness: `mold::tests::facet_composition_distinguishes_required_tails_and_empty_forms`
    #[spec(ensures: |ret| (ret.flags.0 == 0) && ret.first.is_empty() && ret.last.is_empty() && ret.complete_last.is_empty() && ret.adjacent.is_empty())]
    fn void() -> Self
    {
        Self::with_flags([FacetFlag(false); 4])
    }

    /// A tile-free facet with the given answers, in field order.
    ///
    /// # Specification
    /// trivial.
    fn with_flags(flags: [FacetFlag; 4]) -> Self
    {
        Self {
            flags: FacetFlags::from_parts(flags),
            ..Self::default()
        }
    }

    /// One tile occurrence.
    ///
    /// # Specification
    /// trivial.
    fn leaf(key: TileKey) -> Self
    {
        let set = BTreeSet::from([key]);
        Self {
            flags: FacetFlags::default(),
            first: set.clone(),
            last: set.clone(),
            complete_last: set,
            adjacent: BTreeSet::new(),
        }
    }
}

/// The face of `left` followed by `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the standard FIRST/LAST/nullable composition of a concatenation;
///   the empty face is its identity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For optional and mandatory faces and the empty face, L3
///   boundary and identity observations catch reversed FIRST/LAST propagation
///   and incorrect nullability; the predicate covers complete set unions, while
///   arbitrary symbol sets are not exhaustively generated.
/// - witness: `mold::tests::face_composition_and_wrappers_preserve_boundaries`
/// - witness: `mold::tests::context_data_uses_left_last_and_right_first`
#[spec(ensures: |ret| ret.nullable == (left.nullable && right.nullable) && (if left.nullable { ret.first.iter().eq(left.first.union(&right.first)) } else { ret.first == left.first }) && (if right.nullable { ret.last.iter().eq(left.last.union(&right.last)) } else { ret.last == right.last }))]
fn compose_seq(
    left: &FaceCtx,
    right: &FaceCtx,
) -> FaceCtx
{
    let mut first = left.first.clone();
    if left.nullable {
        first.extend(right.first.iter().copied());
    }
    let mut last = right.last.clone();
    if right.nullable {
        last.extend(left.last.iter().copied());
    }
    FaceCtx {
        nullable: left.nullable && right.nullable,
        first,
        last,
    }
}

/// One pending step of [`face_of`] or [`canon`].
#[derive(Clone, Copy)]
enum FoldFrame<'regex>
{
    /// Visit a subtree.
    Enter(RegexView<'regex>),
    /// Fold the last `count` values as a sequence.
    FinishSeq(usize),
    /// Fold the last `count` values as an alternation.
    FinishAlt(usize),
    /// Make the last value optional.
    FinishOptional,
    /// Make the last value a repetition.
    FinishRepeat,
}

/// Pushes the frames that visit `regex`'s children and then fold them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a leaf pushes nothing and returns it as `Some`; a composite
///   pushes its finishing frame then its children, last child first, and
///   returns `None`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For a leaf, empty composites and ordered multi-child
///   sequences, L3 stack observations catch pushing a leaf, omitting the finish
///   frame and reversed evaluation order; arbitrary nesting is witnessed
///   through the iterative consumers, not exhaustively generated.
/// - witness: `mold::tests::expansion_preserves_pending_frames_and_left_to_right_evaluation`
#[spec(captures: start = frames.len(), ensures: |ret| ret.as_ref().map_or_else(|| frames.len() > start && frames.get(start).is_some_and(|frame| !matches!(frame, FoldFrame::Enter(_))) && frames.iter().skip(start.saturating_add(1)).all(|frame| matches!(frame, FoldFrame::Enter(_))), |shape| frames.len() == start && matches!(shape, RegexShape::Empty | RegexShape::Sym(_))))]
fn expand<'regex>(
    regex: RegexView<'regex>,
    frames: &mut Vec<FoldFrame<'regex>>,
) -> Option<RegexShape<'regex>>
{
    let shape = regex.shape();
    let (finish, children) = match shape {
        | RegexShape::Empty | RegexShape::Sym(_) => return Some(shape),
        | RegexShape::Seq(items) => (FoldFrame::FinishSeq(items.len()), items),
        | RegexShape::Alt(items) => (FoldFrame::FinishAlt(items.len()), items),
        | RegexShape::Optional(inner) => (FoldFrame::FinishOptional, vec![inner]),
        | RegexShape::Repeat(inner) => (FoldFrame::FinishRepeat, vec![inner]),
    };
    frames.push(finish);
    frames.extend(children.into_iter().rev().map(FoldFrame::Enter));
    None
}

/// The face of a form: the symbols it can begin and end with, and whether it
/// can be empty.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the standard FIRST/LAST/nullable summary over symbols, holes and
///   tiles alike.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For empty, leaf, nullable-wrapper and asymmetric sequence
///   forms, L3 exact boundary observations catch lost symbols and wrong
///   nullability; the runtime predicate checks root cases and wrappers, while
///   general composite summaries are not exhaustively generated.
/// - witness: `mold::tests::face_composition_and_wrappers_preserve_boundaries`
#[spec(ensures: |ret| match regex.shape() {
    RegexShape::Empty => ret.nullable && ret.first.is_empty() && ret.last.is_empty(),
    RegexShape::Sym(sym) => { let symbol = match sym { Sym::Sort(sort) => StepSym::Sort(sort), Sym::Tile(tile) => StepSym::Tile(tile.label) }; !ret.nullable && ret.first.len() == 1 && ret.last.len() == 1 && ret.first.contains(&symbol) && ret.last.contains(&symbol) },
    RegexShape::Optional(_) | RegexShape::Repeat(_) => ret.nullable,
    RegexShape::Seq(items) if items.is_empty() => ret.nullable && ret.first.is_empty() && ret.last.is_empty(),
    RegexShape::Alt(items) if items.is_empty() => !ret.nullable && ret.first.is_empty() && ret.last.is_empty(),
    _ => true,
})]
fn face_of(regex: RegexView<'_>) -> FaceCtx
{
    let mut frames = vec![FoldFrame::Enter(regex)];
    let mut values = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            | FoldFrame::Enter(current) => match expand(current, &mut frames) {
                | Some(RegexShape::Sym(Sym::Sort(sort))) => {
                    values.push(FaceCtx::leaf(StepSym::Sort(sort)));
                },
                | Some(RegexShape::Sym(Sym::Tile(tile))) => {
                    values.push(FaceCtx::leaf(StepSym::Tile(tile.label)));
                },
                | Some(_) => values.push(FaceCtx::empty()),
                | None => {},
            },
            | FoldFrame::FinishSeq(count) => {
                let split = values.len().saturating_sub(count);
                let children = values.split_off(split);
                let mut acc = FaceCtx::empty();
                for child in children {
                    acc = compose_seq(&acc, &child);
                }
                values.push(acc);
            },
            | FoldFrame::FinishAlt(count) => {
                let split = values.len().saturating_sub(count);
                let children = values.split_off(split);
                let mut acc = FaceCtx::default();
                for current in children {
                    acc.nullable = acc.nullable || current.nullable;
                    acc.first.extend(current.first);
                    acc.last.extend(current.last);
                }
                values.push(acc);
            },
            | FoldFrame::FinishOptional | FoldFrame::FinishRepeat => {
                let mut summary = values.pop().unwrap_or_else(FaceCtx::empty);
                summary.nullable = true;
                values.push(summary);
            },
        }
    }

    values.pop().unwrap_or_else(FaceCtx::empty)
}

/// A mold's precedence bounds: its precedence on a side a hole can face, the
/// root bound on a side none can.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each known context side uses the mold precedence exactly when it
///   faces a sort; an unknown context yields root bounds.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For asymmetric, two-sided and absent contexts, L3 exact bound
///   observations catch direction reversal and fabricated precedence; arbitrary
///   context tables are outside the finite fixtures.
/// - witness: `tests::walk::mold_bounds_follow_context_nullability`
/// - witness: `mold::tests::context_data_uses_left_last_and_right_first`
#[spec(ensures: |ret| {
    let data = usize::try_from(mold.rctx.0).ok().and_then(|index| rctxs.get(index));
    ret.0 == if data.is_some_and(|ctx| ctx.left_faces_sort) { Bound::Value(mold.prec) } else { Bound::Root }
        && ret.1 == if data.is_some_and(|ctx| ctx.right_faces_sort) { Bound::Value(mold.prec) } else { Bound::Root }
})]
fn bounds_for(
    mold: &MoldDef,
    rctxs: &[RCtxData],
) -> (Bound<Prec>, Bound<Prec>)
{
    let index = usize::try_from(u32::from(mold.rctx)).unwrap_or(usize::MAX);
    match rctxs.get(index) {
        | Some(data) => (
            side_bound(SortFacing(data.left_faces_sort), mold.prec),
            side_bound(SortFacing(data.right_faces_sort), mold.prec),
        ),
        | None => (Bound::Root, Bound::Root),
    }
}

/// One side's precedence bound.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the supplied precedence when the side faces a sort, otherwise the
///   root bound; never the bottom bound.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the finite infix and bracket fixtures, L2 endpoint
///   comparisons catch reversed sort-facing decisions and a wrong precedence
///   value. The const predicate observes the bound variant; the fixture
///   observes its concrete group. The whole precedence-index domain is not
///   exhausted.
/// - witness: `tests::walk::mold_bounds_follow_context_nullability`
#[spec(ensures: |ret| match ret { Bound::Value(_) => faces_sort.0, Bound::Root => !faces_sort.0, Bound::Bottom => false })]
const fn side_bound(
    faces_sort: SortFacing,
    prec: Prec,
) -> Bound<Prec>
{
    if faces_sort.0 {
        Bound::Value(prec)
    }
    else {
        Bound::Root
    }
}

/// A form's canonical spelling, alternation branches unordered.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two forms that differ only in the order of alternation branches
///   spell the same; forms that differ otherwise spell differently.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For permuted alternatives, ordered sequences, empty composites
///   and separator-bearing tile labels, L3 relational spelling observations
///   catch erased order, constructor collisions and ambiguous payload framing;
///   arbitrary labels and deep forms are not exhausted.
/// - witness: `mold::tests::canonical_forms_forget_only_alternative_order`
#[spec(ensures: |ret| match regex.shape() {
    RegexShape::Empty => ret == "e",
    RegexShape::Sym(Sym::Sort(_)) => ret.starts_with('s'),
    RegexShape::Sym(Sym::Tile(tile)) => ret.starts_with('t') && ret.ends_with(tile.label),
    RegexShape::Seq(_) => ret.starts_with("Q[") && ret.ends_with(']'),
    RegexShape::Alt(_) => ret.starts_with("A[") && ret.ends_with(']'),
    RegexShape::Optional(_) => ret.starts_with("O[") && ret.ends_with(']'),
    RegexShape::Repeat(_) => ret.starts_with("R[") && ret.ends_with(']'),
})]
fn canon(regex: RegexView<'_>) -> String
{
    let mut frames = vec![FoldFrame::Enter(regex)];
    let mut values: Vec<String> = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            | FoldFrame::Enter(current) => match expand(current, &mut frames) {
                | Some(RegexShape::Sym(Sym::Sort(sort))) => {
                    values.push(format!("s{}", u16::from(sort.grout_sort())));
                },
                | Some(RegexShape::Sym(Sym::Tile(tile))) => {
                    values.push(format!("t{}:{}", tile.label.len(), tile.label));
                },
                | Some(_) => values.push(String::from("e")),
                | None => {},
            },
            | FoldFrame::FinishSeq(count) => {
                let split = values.len().saturating_sub(count);
                let parts = values.split_off(split);
                values.push(format!("Q[{}]", parts.join(",")));
            },
            | FoldFrame::FinishAlt(count) => {
                let split = values.len().saturating_sub(count);
                let mut parts = values.split_off(split);
                parts.sort();
                values.push(format!("A[{}]", parts.join(",")));
            },
            | FoldFrame::FinishOptional => {
                let inner = values.pop().unwrap_or_default();
                values.push(format!("O[{inner}]"));
            },
            | FoldFrame::FinishRepeat => {
                let inner = values.pop().unwrap_or_default();
                values.push(format!("R[{inner}]"));
            },
        }
    }

    values.pop().unwrap_or_default()
}

/// The facet of `left` followed by `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every last tile of `left` is adjacent to every first tile of
///   `right`; FIRST, LAST and the flags compose as a concatenation, and an
///   infix operator between a required head and a required tail still completes
///   its form.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For empty identities, prefix and infix required holes, and
///   adjacent tile pairs, L3 exact completion and edge observations catch lost
///   seams, wrong nullability and premature prefix completion; arbitrary facets
///   are not exhaustively generated, while the predicate checks full set
///   relations.
/// - witness: `mold::tests::facet_composition_distinguishes_required_tails_and_empty_forms`
/// - witness: `tests::surface::prefix_formers_keep_required_type_tails_unclosed`
/// - witness: `tests::surface::infix_type_operator_keeps_clean_completion`
#[spec(ensures: |ret| ret.flags.nullable().0 == (left.flags.nullable().0 && right.flags.nullable().0)
    && ret.flags.form_nullable().0 == (left.flags.form_nullable().0 && right.flags.form_nullable().0)
    && ret.flags.required_first().0 == (left.flags.required_first().0 || (left.flags.nullable().0 && right.flags.required_first().0))
    && ret.flags.required_last().0 == (right.flags.required_last().0 || (right.flags.nullable().0 && left.flags.required_last().0))
    && (if left.flags.nullable().0 { ret.first.iter().eq(left.first.union(&right.first)) } else { ret.first == left.first })
    && (if right.flags.nullable().0 { ret.last.iter().eq(left.last.union(&right.last)) } else { ret.last == right.last })
    && (if right.flags.form_nullable().0 || (right.flags.required_last().0 && left.flags.required_first().0) { ret.complete_last.iter().eq(left.complete_last.union(&right.complete_last)) } else { ret.complete_last == right.complete_last })
    && left.adjacent.is_subset(&ret.adjacent) && right.adjacent.is_subset(&ret.adjacent)
    && left.last.iter().all(|&tail| right.first.iter().all(|&head| ret.adjacent.contains(&(tail, head))))
    && ret.adjacent.iter().all(|pair| left.adjacent.contains(pair) || right.adjacent.contains(pair) || (left.last.contains(&pair.0) && right.first.contains(&pair.1))))]
fn seq_facet(
    left: &TileFacet,
    right: &TileFacet,
) -> TileFacet
{
    let mut adjacent = left.adjacent.clone();
    adjacent.extend(right.adjacent.iter().copied());
    for tail in &left.last {
        for head in &right.first {
            adjacent.insert((*tail, *head));
        }
    }
    let mut first = left.first.clone();
    if left.flags.nullable().0 {
        first.extend(right.first.iter().copied());
    }
    let mut last = right.last.clone();
    if right.flags.nullable().0 {
        last.extend(left.last.iter().copied());
    }
    // An infix form has required holes either side of its operator, so the
    // operator completes the form once the tail is filled; a prefix former
    // such as `+U` has no required head and stays required-tail only.
    let mut complete_last = right.complete_last.clone();
    if right.flags.form_nullable().0
        || (right.flags.required_last().0 && left.flags.required_first().0)
    {
        complete_last.extend(left.complete_last.iter().copied());
    }
    TileFacet {
        flags: FacetFlags::from_parts([
            FacetFlag(left.flags.nullable().0 && right.flags.nullable().0),
            FacetFlag(left.flags.form_nullable().0 && right.flags.form_nullable().0),
            FacetFlag(
                left.flags.required_first().0
                    || (left.flags.nullable().0 && right.flags.required_first().0),
            ),
            FacetFlag(
                right.flags.required_last().0
                    || (right.flags.nullable().0 && left.flags.required_last().0),
            ),
        ]),
        first,
        last,
        complete_last,
        adjacent,
    }
}

/// The facet of `left` or `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every set is the union and every flag the disjunction.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For a void branch and alternatives sharing a tile through
///   complete and required-tail paths, L3 exact set and flag observations catch
///   dropping one branch or deriving completion from LAST alone; arbitrary
///   facet pairs are outside the finite witness.
/// - witness: `mold::tests::facet_composition_distinguishes_required_tails_and_empty_forms`
#[spec(ensures: |ret| ret.flags.0 == (left.flags.0 | right.flags.0) && ret.first.iter().eq(left.first.union(&right.first)) && ret.last.iter().eq(left.last.union(&right.last)) && ret.complete_last.iter().eq(left.complete_last.union(&right.complete_last)) && ret.adjacent.iter().eq(left.adjacent.union(&right.adjacent)))]
fn alt_facet(
    left: &TileFacet,
    right: &TileFacet,
) -> TileFacet
{
    let mut first = left.first.clone();
    first.extend(right.first.iter().copied());
    let mut last = left.last.clone();
    last.extend(right.last.iter().copied());
    let mut complete_last = left.complete_last.clone();
    complete_last.extend(right.complete_last.iter().copied());
    let mut adjacent = left.adjacent.clone();
    adjacent.extend(right.adjacent.iter().copied());
    TileFacet {
        flags: FacetFlags(left.flags.0 | right.flags.0),
        first,
        last,
        complete_last,
        adjacent,
    }
}

/// The facet of zero or more `inner`: empty and complete, with the seam
/// from each last tile back to each first tile.
///
/// # Specification
/// - requires: nothing.
/// - ensures: preserves tile boundaries and complete endings, permits emptiness
///   without required holes, and adds exactly the LAST-to-FIRST repetition
///   seams to existing adjacency.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For a two-tile body and nullable occurrence sequences, L3
///   exact cycle-edge and completion observations catch missing backedges or
///   retained mandatory tails; arbitrary facets are not exhausted.
/// - witness: `mold::tests::facet_composition_distinguishes_required_tails_and_empty_forms`
/// - witness: `mold::tests::occurrence_order_and_nullable_seams_are_exact`
#[spec(ensures: |ret| ret.first == inner.first && ret.last == inner.last && ret.complete_last == inner.complete_last && ret.flags.nullable().0 && ret.flags.form_nullable().0 && !ret.flags.required_first().0 && !ret.flags.required_last().0 && inner.adjacent.is_subset(&ret.adjacent) && inner.last.iter().all(|&tail| inner.first.iter().all(|&head| ret.adjacent.contains(&(tail, head)))) && ret.adjacent.iter().all(|pair| inner.adjacent.contains(pair) || (inner.last.contains(&pair.0) && inner.first.contains(&pair.1))))]
fn repeat_facet(inner: &TileFacet) -> TileFacet
{
    let mut facet = inner.clone();
    facet.flags.set_nullable(FacetFlag(true));
    facet.flags.set_form_nullable(FacetFlag(true));
    facet.flags.set_required_first(FacetFlag(false));
    facet.flags.set_required_last(FacetFlag(false));
    for tail in &inner.last {
        for head in &inner.first {
            facet.adjacent.insert((*tail, *head));
        }
    }
    facet
}

/// Folds the precedence DAG's fingerprint with the mold and context tables.
///
/// # Specification
/// - requires: nothing.
/// - ensures: FNV-1a over `M`, the DAG fingerprint, the mold count, each mold
///   (label, a zero byte, context, precedence, sort), the context count, and
///   each context (both sort-facing bytes, then both step lists); every word
///   little-endian and every count a 64-bit word.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For empty tables and a table with asymmetric sort/tile steps,
///   L3 literal byte-stream observations and the built-in compatibility pin
///   catch missing frame bytes, wrong word order and omitted state; hash
///   collisions and arbitrary table sizes are not excluded.
/// - witness: `mold::tests::fingerprint_framing_matches_literal_bytes`
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
#[spec(ensures: |ret| {
    let mut expected = Fnv64::new();
    expected.write_bytes(&[FRAME_MOLD][..]);
    expected.write_bytes(&u64::from(dag_fingerprint).to_le_bytes()[..]);
    expected.write_bytes(&u64::try_from(molds.len()).unwrap_or(u64::MAX).to_le_bytes()[..]);
    for mold in molds {
        expected.write_bytes(mold.label.as_bytes());
        expected.write_byte(0_u8);
        expected.write_bytes(&mold.rctx.0.to_le_bytes()[..]);
        expected.write_bytes(&u16::from(mold.prec.index()).to_le_bytes()[..]);
        expected.write_bytes(&u16::from(mold.sort.grout_sort()).to_le_bytes()[..]);
    }
    expected.write_bytes(&u64::try_from(rctxs.len()).unwrap_or(u64::MAX).to_le_bytes()[..]);
    for context in rctxs {
        expected.write_byte(u8::from(context.left_faces_sort));
        expected.write_byte(u8::from(context.right_faces_sort));
        fold_steps(&mut expected, &context.left_steps);
        fold_steps(&mut expected, &context.right_steps);
    }
    u64::from(ret) == u64::from(expected.finish())
})]
fn fold_fingerprint(
    dag_fingerprint: GrammarFingerprint,
    molds: &[MoldDef],
    rctxs: &[RCtxData],
) -> GrammarFingerprint
{
    let mut hasher = Fnv64::new();
    hasher.write_byte(FRAME_MOLD);
    hasher.write_u64(u64::from(dag_fingerprint));
    hasher.write_u64(u64::try_from(molds.len()).unwrap_or(u64::MAX));
    for mold in molds {
        hasher.write_bytes(mold.label.as_bytes());
        hasher.write_byte(0_u8);
        hasher.write_u32(u32::from(mold.rctx));
        hasher.write_u16(u16::from(mold.prec.index()));
        hasher.write_u16(u16::from(mold.sort.grout_sort()));
    }
    hasher.write_u64(u64::try_from(rctxs.len()).unwrap_or(u64::MAX));
    for data in rctxs {
        hasher.write_byte(u8::from(data.left_faces_sort));
        hasher.write_byte(u8::from(data.right_faces_sort));
        fold_steps(&mut hasher, &data.left_steps);
        fold_steps(&mut hasher, &data.right_steps);
    }
    GrammarFingerprint::from(u64::from(hasher.finish()))
}

/// Folds one step list: its length, then each step as `S` and the sort, or
/// `T`, the label and a zero byte.
///
/// # Specification
/// - requires: nothing.
/// - ensures: extends the existing accumulator with the 64-bit little-endian
///   count, then tagged sort words or zero-terminated tile labels, in order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For empty and mixed step lists after a nonempty hash prefix,
///   L3 literal byte observations catch resetting the accumulator, reversing
///   steps or losing a tag/terminator; arbitrary labels and hash collisions are
///   outside the finite witness.
/// - witness: `mold::tests::step_framing_preserves_the_existing_hash_prefix`
#[spec(captures: before = *hasher, ensures: |()| {
    let mut expected = before;
    expected.write_bytes(&u64::try_from(steps.len()).unwrap_or(u64::MAX).to_le_bytes()[..]);
    for step in steps {
        match step.crossed {
            StepSym::Sort(sort) => { expected.write_byte(b'S'); expected.write_bytes(&u16::from(sort.grout_sort()).to_le_bytes()[..]); },
            StepSym::Tile(label) => { expected.write_byte(b'T'); expected.write_bytes(label.as_bytes()); expected.write_byte(0_u8); },
        }
    }
    hasher.finish() == expected.finish()
})]
fn fold_steps(
    hasher: &mut Fnv64,
    steps: &[RCtxStep],
)
{
    hasher.write_u64(u64::try_from(steps.len()).unwrap_or(u64::MAX));
    for step in steps {
        match step.crossed {
            | StepSym::Sort(sort) => {
                hasher.write_byte(b'S');
                hasher.write_u16(u16::from(sort.grout_sort()));
            },
            | StepSym::Tile(label) => {
                hasher.write_byte(b'T');
                hasher.write_bytes(label.as_bytes());
                hasher.write_byte(0_u8);
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use gandr_theory_graphs::EdgeSource as _;
    use gandr_theory_graphs::Fnv64;
    use gandr_theory_graphs::NodeId;
    use gandr_theory_graphs::Prec;
    use gandr_theory_graphs::PrecIndex;

    use super::ContextInterner;
    use super::EndingVerdict;
    use super::FaceCtx;
    use super::FacetFlag;
    use super::FacetFlags;
    use super::FoldFrame;
    use super::MoldDef;
    use super::RCtxData;
    use super::RCtxId;
    use super::RCtxStep;
    use super::StepSym;
    use super::TileFacet;
    use super::TileGraph;
    use super::TileKey;
    use super::alt_facet;
    use super::bounds_for;
    use super::canon;
    use super::collect_occurrences;
    use super::compose_seq;
    use super::context_data;
    use super::expand;
    use super::face_of;
    use super::fold_fingerprint;
    use super::fold_steps;
    use super::repeat_facet;
    use super::resolve_adjacencies;
    use super::resolve_keys;
    use super::seq_facet;
    use super::tile_index;
    use crate::model::Regex;
    use crate::model::RegexShape;
    use crate::model::Rule;
    use crate::model::RuleName;
    use crate::model::Sort;
    use crate::model::Sym;
    use crate::model::Tile;
    use crate::model::TileLabel;

    #[test]
    fn context_interning_keeps_first_data_and_dense_ids()
    {
        let first = context_data(
            &FaceCtx::leaf(StepSym::Tile("left")),
            &FaceCtx::leaf(StepSym::Sort(Sort::Type)),
        );
        let replacement = context_data(&FaceCtx::empty(), &FaceCtx::empty());
        let mut interner = ContextInterner::new();
        let a = interner.intern("a".into(), first.clone());
        let b = interner.intern("b".into(), replacement.clone());
        assert_eq!(RCtxId(0), a);
        assert_eq!(RCtxId(1), b);
        assert_eq!(a, interner.intern("a".into(), replacement.clone()));
        assert_eq!(vec![first, replacement], interner.finish());
    }

    #[test]
    fn ending_verdict_fold_has_identity_absorption_and_agreement()
    {
        let verdicts = [
            EndingVerdict::Empty,
            EndingVerdict::Agree(ClosingClass::Paren),
            EndingVerdict::Agree(ClosingClass::Bracket),
            EndingVerdict::Agree(ClosingClass::Brace),
            EndingVerdict::Divergent,
        ];
        for left in verdicts {
            assert!(left.merge_successor(EndingVerdict::Empty) == left);
            assert!(EndingVerdict::Empty.merge_successor(left) == left);
            assert!(left.merge_successor(EndingVerdict::Divergent) == EndingVerdict::Divergent);
            for right in verdicts {
                assert!(left.merge_successor(right) == right.merge_successor(left));
                for third in verdicts {
                    assert!(
                        left.merge_successor(right).merge_successor(third)
                            == left.merge_successor(right.merge_successor(third))
                    );
                }
            }
        }
        for class in [
            ClosingClass::Paren,
            ClosingClass::Bracket,
            ClosingClass::Brace,
        ] {
            assert!(EndingVerdict::Empty.merge_class(class) == EndingVerdict::Agree(class));
            assert!(EndingVerdict::Agree(class).merge_class(class) == EndingVerdict::Agree(class));
            assert!(EndingVerdict::Divergent.merge_class(class) == EndingVerdict::Divergent);
        }
        assert!(
            EndingVerdict::Agree(ClosingClass::Paren).merge_class(ClosingClass::Brace)
                == EndingVerdict::Divergent
        );
    }

    #[test]
    fn tile_graph_preserves_successor_order_and_refuses_unknown_nodes()
    {
        let graph = TileGraph {
            rows: vec![
                vec![NodeId::from(2), NodeId::from(1), NodeId::from(2)],
                vec![],
                vec![NodeId::from(0)],
            ],
        };
        assert_eq!(3, u32::from(graph.node_count()));
        assert_eq!(
            vec![NodeId::from(2), NodeId::from(1), NodeId::from(2)],
            graph.successors(NodeId::from(0)).collect::<Vec<_>>()
        );
        assert_eq!(None, graph.successors(NodeId::from(1)).next());
        assert_eq!(None, graph.successors(NodeId::from(3)).next());
        assert_eq!(
            vec![NodeId::from(0)],
            graph.successors(NodeId::from(2)).collect::<Vec<_>>()
        );
        let empty = TileGraph { rows: vec![] };
        assert_eq!(0, u32::from(empty.node_count()));
        assert_eq!(None, empty.successors(NodeId::from(0)).next());
    }

    #[test]
    fn occurrence_order_and_nullable_seams_are_exact()
    {
        let rule = Rule::new(
            RuleName("nullable-seams"),
            Sort::Expression,
            Prec::new(PrecIndex::from(0)),
            Regex::seq([
                Regex::tile(TileLabel("z")),
                Regex::optional(Regex::tile(TileLabel("a"))),
                Regex::repeat(Regex::tile(TileLabel("b"))),
            ]),
        );
        let mut interner = ContextInterner::new();
        let mut out = Vec::new();
        let facet = collect_occurrences(&rule, &mut interner, &mut out);
        assert_eq!(
            vec![("z", RCtxId(0)), ("a", RCtxId(1)), ("b", RCtxId(2))],
            out.iter()
                .map(|occurrence| (occurrence.label, occurrence.rctx))
                .collect::<Vec<_>>()
        );
        let z = TileKey::new(TileLabel("z"), RCtxId(0));
        let a = TileKey::new(TileLabel("a"), RCtxId(1));
        let b = TileKey::new(TileLabel("b"), RCtxId(2));
        assert_eq!(BTreeSet::from([z]), facet.first);
        assert_eq!(BTreeSet::from([z, a, b]), facet.last);
        assert_eq!(
            BTreeSet::from([(z, a), (z, b), (a, b), (b, b)]),
            facet.adjacent
        );
        assert_eq!(facet.last, facet.complete_last);
        assert!(!facet.flags.nullable().0);
    }

    #[test]
    fn resolutions_sort_deduplicate_and_skip_missing_keys()
    {
        let a = TileKey::new(TileLabel("a"), RCtxId(0));
        let b = TileKey::new(TileLabel("b"), RCtxId(1));
        let alias = TileKey::new(TileLabel("alias"), RCtxId(2));
        let missing = TileKey::new(TileLabel("missing"), RCtxId(3));
        let high = MoldId::try_from(7_usize).expect("small id");
        let low = MoldId::try_from(2_usize).expect("small id");
        let index = BTreeMap::from([(a, high), (b, low), (alias, high)]);
        assert_eq!(
            vec![low, high],
            resolve_keys(&index, &BTreeSet::from([a, b, alias, missing]))
        );
        assert_eq!(
            vec![(low, high), (high, low)],
            resolve_adjacencies(
                &index,
                &BTreeSet::from([(a, b), (alias, b), (b, a), (a, missing), (missing, b)])
            )
        );
        let prec = Prec::new(PrecIndex::from(0));
        let molds = [
            MoldDef {
                label: "z",
                rctx: RCtxId(4),
                prec,
                sort: Sort::Item,
            },
            MoldDef {
                label: "a",
                rctx: RCtxId(5),
                prec,
                sort: Sort::Type,
            },
        ];
        assert_eq!(
            BTreeMap::from([
                (
                    TileKey::new(TileLabel("z"), RCtxId(4)),
                    MoldId::try_from(0_usize).expect("small id")
                ),
                (
                    TileKey::new(TileLabel("a"), RCtxId(5)),
                    MoldId::try_from(1_usize).expect("small id")
                )
            ]),
            tile_index(&molds)
        );
    }

    #[test]
    fn context_data_uses_left_last_and_right_first()
    {
        let left = FaceCtx {
            nullable: false,
            first: BTreeSet::from([StepSym::Tile("ignored-first")]),
            last: BTreeSet::from([StepSym::Sort(Sort::Type), StepSym::Tile("left")]),
        };
        let right = FaceCtx {
            nullable: false,
            first: BTreeSet::from([StepSym::Tile("right")]),
            last: BTreeSet::from([StepSym::Sort(Sort::Item)]),
        };
        let data = context_data(&left, &right);
        assert!(data.left_faces_sort);
        assert!(!data.right_faces_sort);
        assert_eq!(
            vec![
                RCtxStep {
                    crossed: StepSym::Sort(Sort::Type)
                },
                RCtxStep {
                    crossed: StepSym::Tile("left")
                }
            ],
            data.left_steps
        );
        assert_eq!(
            vec![RCtxStep {
                crossed: StepSym::Tile("right")
            }],
            data.right_steps
        );
        let prec = Prec::new(PrecIndex::from(0));
        let mold = MoldDef {
            label: "x",
            rctx: RCtxId(0),
            prec,
            sort: Sort::Expression,
        };
        assert_eq!(
            (
                gandr_theory_graphs::Bound::Value(prec),
                gandr_theory_graphs::Bound::Root
            ),
            bounds_for(&mold, &[data])
        );
        assert_eq!(
            (
                gandr_theory_graphs::Bound::Root,
                gandr_theory_graphs::Bound::Root
            ),
            bounds_for(&mold, &[])
        );
    }

    #[test]
    fn facet_flag_updates_preserve_other_answers()
    {
        const READ: FacetFlag =
            FacetFlags(FacetFlags::FORM_NULLABLE.0).get(FacetFlags::FORM_NULLABLE);
        let bits = [
            FacetFlags::NULLABLE,
            FacetFlags::FORM_NULLABLE,
            FacetFlags::REQUIRED_FIRST,
            FacetFlags::REQUIRED_LAST,
        ];
        for word in 0_u8 ..= u8::MAX {
            for bit in bits {
                assert_eq!(word & bit.0 != 0, FacetFlags(word).get(bit).0);
                for value in [false, READ.0] {
                    let mut flags = FacetFlags(word);
                    flags.set(bit, FacetFlag(value));
                    assert_eq!(value, flags.get(bit).0);
                    assert_eq!(word & !bit.0, flags.0 & !bit.0);
                }
            }
        }
        for word in 0_u8 .. 16 {
            let mut flags = FacetFlags::from_parts([
                FacetFlag(word & 1 != 0),
                FacetFlag(word & 2 != 0),
                FacetFlag(word & 4 != 0),
                FacetFlag(word & 8 != 0),
            ]);
            flags.set_nullable(FacetFlag(word & 1 == 0));
            assert_eq!(word & 1 == 0, flags.nullable().0);
            assert_eq!(word & 2 != 0, flags.form_nullable().0);
            assert_eq!(word & 4 != 0, flags.required_first().0);
            assert_eq!(word & 8 != 0, flags.required_last().0);
        }
    }

    #[test]
    fn facet_composition_distinguishes_required_tails_and_empty_forms()
    {
        let a = TileKey::new(TileLabel("a"), RCtxId(0));
        let b = TileKey::new(TileLabel("b"), RCtxId(1));
        let first = TileFacet::leaf(a);
        let second = TileFacet::leaf(b);
        let hole = TileFacet::required_hole();
        let prefix = seq_facet(&first, &hole);
        assert_eq!(BTreeSet::from([a]), prefix.last);
        assert!(prefix.complete_last.is_empty());
        assert!(prefix.flags.required_last().0);
        let infix = seq_facet(&seq_facet(&hole, &first), &hole);
        assert_eq!(BTreeSet::from([a]), infix.complete_last);
        for facet in [&first, &prefix, &infix, &hole] {
            assert_eq!(*facet, seq_facet(&TileFacet::empty(), facet));
            assert_eq!(*facet, seq_facet(facet, &TileFacet::empty()));
            assert_eq!(*facet, alt_facet(&TileFacet::void(), facet));
            assert_eq!(*facet, alt_facet(facet, &TileFacet::void()));
        }
        let alternative = alt_facet(&prefix, &first);
        assert_eq!(BTreeSet::from([a]), alternative.complete_last);
        assert!(alternative.flags.required_last().0);
        let repeated = repeat_facet(&seq_facet(&first, &second));
        assert_eq!(BTreeSet::from([a]), repeated.first);
        assert_eq!(BTreeSet::from([b]), repeated.last);
        assert_eq!(BTreeSet::from([(a, b), (b, a)]), repeated.adjacent);
        assert!(repeated.flags.nullable().0 && repeated.flags.form_nullable().0);
        assert!(!repeated.flags.required_first().0 && !repeated.flags.required_last().0);
    }

    #[test]
    fn expansion_preserves_pending_frames_and_left_to_right_evaluation()
    {
        let leaf = Regex::tile(TileLabel("leaf"));
        let mut frames = vec![FoldFrame::FinishAlt(41)];
        assert_eq!(
            Some(RegexShape::Sym(Sym::Tile(Tile::new(TileLabel("leaf"))))),
            expand(leaf.view(), &mut frames)
        );
        assert!(matches!(frames.as_slice(), [FoldFrame::FinishAlt(41)]));
        let sequence = Regex::seq([
            Regex::tile(TileLabel("a")),
            Regex::tile(TileLabel("b")),
            Regex::tile(TileLabel("c")),
        ]);
        assert_eq!(None, expand(sequence.view(), &mut frames));
        for label in ["a", "b", "c"] {
            let Some(FoldFrame::Enter(child)) = frames.pop()
            else {
                panic!("next child")
            };
            assert_eq!(
                RegexShape::Sym(Sym::Tile(Tile::new(TileLabel(label)))),
                child.shape()
            );
        }
        assert!(matches!(frames.pop(), Some(FoldFrame::FinishSeq(3))));
        assert!(matches!(frames.pop(), Some(FoldFrame::FinishAlt(41))));
        let empty = Regex::alt([]);
        assert_eq!(None, expand(empty.view(), &mut frames));
        assert!(matches!(frames.as_slice(), [FoldFrame::FinishAlt(0)]));
    }

    #[test]
    fn face_composition_and_wrappers_preserve_boundaries()
    {
        assert_eq!(FaceCtx::empty(), face_of(Regex::empty().view()));
        assert_eq!(FaceCtx::empty(), face_of(Regex::seq([]).view()));
        assert_eq!(FaceCtx::default(), face_of(Regex::alt([]).view()));
        let sort = Regex::sort(Sort::Item);
        let expected = BTreeSet::from([StepSym::Sort(Sort::Item)]);
        for wrapped in [Regex::optional(sort.clone()), Regex::repeat(sort)] {
            assert_eq!(
                FaceCtx {
                    nullable: true,
                    first: expected.clone(),
                    last: expected.clone()
                },
                face_of(wrapped.view())
            );
        }
        let left = face_of(Regex::optional(Regex::sort(Sort::Item)).view());
        let right = face_of(Regex::tile(TileLabel("}")).view());
        let combined = compose_seq(&left, &right);
        assert_eq!(
            FaceCtx {
                nullable: false,
                first: BTreeSet::from([StepSym::Sort(Sort::Item), StepSym::Tile("}")]),
                last: BTreeSet::from([StepSym::Tile("}")])
            },
            combined
        );
        assert_eq!(left, compose_seq(&FaceCtx::empty(), &left));
        assert_eq!(right, compose_seq(&right, &FaceCtx::empty()));
    }

    #[test]
    fn canonical_forms_forget_only_alternative_order()
    {
        let a = Regex::tile(TileLabel("a,b"));
        let b = Regex::tile(TileLabel("]Q["));
        assert_eq!(
            canon(Regex::alt([a.clone(), b.clone()]).view()),
            canon(Regex::alt([b.clone(), a.clone()]).view())
        );
        assert_ne!(
            canon(Regex::seq([a.clone(), b.clone()]).view()),
            canon(Regex::seq([b, a]).view())
        );
        let forms = [
            Regex::empty(),
            Regex::seq([]),
            Regex::alt([]),
            Regex::optional(Regex::empty()),
            Regex::repeat(Regex::empty()),
            Regex::tile(TileLabel("")),
            Regex::tile(TileLabel("e")),
            Regex::sort(Sort::Item),
        ];
        for (index, left) in forms.iter().enumerate() {
            for right in forms.iter().skip(index.saturating_add(1)) {
                assert_ne!(canon(left.view()), canon(right.view()));
            }
        }
    }

    #[test]
    fn fingerprint_framing_matches_literal_bytes()
    {
        let mold = MoldDef {
            label: "x",
            rctx: RCtxId(0),
            prec: Prec::new(PrecIndex::from(0)),
            sort: Sort::Expression,
        };
        let data = RCtxData {
            left_faces_sort: true,
            right_faces_sort: false,
            left_steps: vec![RCtxStep {
                crossed: StepSym::Sort(Sort::Type),
            }],
            right_steps: vec![RCtxStep {
                crossed: StepSym::Tile(")"),
            }],
        };
        let bytes = [
            b'M', 4, 3, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, b'x', 0, 0, 0, 0, 0, 0, 0, 2, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, b'S', 3, 0, 1, 0, 0, 0, 0, 0, 0,
            0, b'T', b')', 0,
        ];
        let mut expected = Fnv64::new();
        expected.write_bytes(bytes.as_slice());
        assert_eq!(
            u64::from(expected.finish()),
            u64::from(fold_fingerprint(
                GrammarFingerprint::from(0x0102_0304_u64),
                &[mold],
                &[data]
            ))
        );
        let mut empty_expected = Fnv64::new();
        empty_expected.write_bytes(
            [
                b'M', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ]
            .as_slice(),
        );
        assert_eq!(
            u64::from(empty_expected.finish()),
            u64::from(fold_fingerprint(GrammarFingerprint::from(0_u64), &[], &[]))
        );
    }

    #[test]
    fn step_framing_preserves_the_existing_hash_prefix()
    {
        let steps = [
            RCtxStep {
                crossed: StepSym::Sort(Sort::Type),
            },
            RCtxStep {
                crossed: StepSym::Tile(")"),
            },
        ];
        let mut actual = Fnv64::new();
        actual.write_bytes(b"prefix".as_slice());
        let mut expected = actual;
        expected.write_bytes([2, 0, 0, 0, 0, 0, 0, 0, b'S', 3, 0, b'T', b')', 0].as_slice());
        fold_steps(&mut actual, &steps);
        assert_eq!(expected.finish(), actual.finish());
        let mut empty_expected = actual;
        empty_expected.write_bytes([0_u8; 8].as_slice());
        fold_steps(&mut actual, &[]);
        assert_eq!(empty_expected.finish(), actual.finish());
    }
}
