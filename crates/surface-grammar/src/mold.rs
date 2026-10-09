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
    /// Whether each mold has a same-form predecessor, by id.
    has_pred: Vec<bool>,
    /// Whether each mold has a same-form successor, by id.
    has_succ: Vec<bool>,
    /// The molds that can open a form, ascending.
    form_first: Vec<MoldId>,
    /// The molds that can end a form, ascending.
    form_last: Vec<MoldId>,
    /// The form-last molds whose remainder needs no hole, ascending.
    complete_last: Vec<MoldId>,
    /// The form-last molds whose remainder needs a hole, ascending.
    required_tail: Vec<MoldId>,
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
        for &mold in &form_first {
            if let Ok(raw) = usize::try_from(u32::from(mold))
                && let Some(slot) = is_first.get_mut(raw)
            {
                *slot = true;
            }
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
            has_pred,
            has_succ,
            form_first,
            form_last,
            complete_last,
            required_tail,
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

    /// Whether `mold` has a same-form predecessor; false past the table.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn is_form_first(
        &self,
        mold: MoldId,
    ) -> MoldIsFormFirst
    {
        MoldIsFormFirst::from(self.form_first.binary_search(&mold).is_ok())
    }

    /// Whether `mold` can complete its form with no hole still required.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn is_form_last(
        &self,
        mold: MoldId,
    ) -> MoldIsFormLast
    {
        MoldIsFormLast::from(self.complete_last.binary_search(&mold).is_ok())
    }

    /// Whether `mold` can end its form only once a trailing hole is filled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn has_required_tail(
        &self,
        mold: MoldId,
    ) -> MoldHasRequiredTail
    {
        MoldHasRequiredTail::from(self.required_tail.binary_search(&mold).is_ok())
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
    #[inline]
    fn node_count(&self) -> NodeCount
    {
        NodeCount::from(u32::try_from(self.rows.len()).unwrap_or(u32::MAX))
    }

    /// The node's row; none past the graph.
    ///
    /// # Specification
    /// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
