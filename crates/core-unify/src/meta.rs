//! The metacontext: which value holes stand for contextual metavariables, the
//! context each one sees, what the solver has bound it to, and the one store
//! of equations waiting on them.
//!
//! A metavariable is an existing [`Value::Hole`] a [`Metas`] declares, with
//! the number of intuitionistic binders its context holds. A hole the
//! metacontext does not declare stays the gradual hole the checker reads.
//! A solution is written in the metavariable's own context; an occurrence
//! under further binders stands for the solution weakened past them. An
//! equation the solver cannot answer most generally waits in the store with
//! the unsolved metavariables that block it, and leaves it when one is bound.
//!
//! [`Value::Hole`]: gandr_core_term::Value::Hole

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use quenchant_shape::shape::Maybe;

use crate::solve::Equation;
use crate::solve::Postponed;

/// A metavariable's place in its metacontext, in declaration order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MetaId(usize);

impl From<MetaId> for usize
{
    /// The declaration position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: MetaId) -> Self
    {
        id.0
    }
}

quenchant_shape::reason_enum! {
    /// Why a metacontext answers nothing for a hole or a metavariable.
    pub mod meta_lookup {
        /// The reason the lookup finds nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The hole is not declared a metavariable: it is gradual.
            Undeclared,
            /// The identifier is at or past the metacontext's count.
            OutOfRange,
            /// The metavariable is declared and not yet solved.
            Unsolved,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a hole cannot be declared a metavariable.
    pub mod declaration {
        /// The reason the declaration is refused.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The hole is already a metavariable of this metacontext.
            Redeclared,
        }
    }
}

/// One declared metavariable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Entry
{
    /// The hole that stands for it.
    hole: HoleId,
    /// The binders its context holds.
    scope: Binders,
    /// Its solution, in its own context, once the solver binds it.
    solution: Maybe<ValueId, meta_lookup::Absent>,
}

/// One change a trial made to its metacontext, as what puts it back.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Undo
{
    /// `hole` was declared the last metavariable.
    Declared(HoleId),
    /// The metavariable was bound; its solution before.
    Bound(MetaId, Maybe<ValueId, meta_lookup::Absent>),
    /// An equation was put last in the store.
    Postponed,
    /// These equations left the store, each with the place it held.
    Woken(Vec<(usize, Postponed)>),
}

/// The metavariables of one problem, each with its context and its solution,
/// and the equations that wait on them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Metas
{
    /// The declared metavariables, in declaration order.
    entries: Vec<Entry>,
    /// Each declared hole's metavariable.
    by_hole: BTreeMap<HoleId, MetaId>,
    /// The equations that wait, in the order they were postponed.
    postponed: Vec<Postponed>,
    /// While a [`Metas::trial`] runs, every change made since it began, in
    /// order; none outside one.
    journal: Option<Vec<Undo>>,
}

impl Metas
{
    /// An empty metacontext.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Declare `hole` a metavariable whose context holds `scope` binders.
    ///
    /// # Specification
    /// - ensures: a fresh identifier one past the last, the hole unsolved;
    ///   [`declaration::Absent::Redeclared`] for a hole already declared, which
    ///   keeps its first context.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hole declared twice keeps its first metavariable,
    ///   and a hole never declared reads as undeclared.
    /// - witness: `tests::solve::a_hole_is_declared_once`
    #[inline]
    #[spec(captures: before = self.entries.len(),
        ensures: |output| match output {
            Maybe::Present(id) => usize::from(id) == before && self.entries.len() == before.saturating_add(1),
            Maybe::Absent(declaration::Absent::Redeclared) => self.entries.len() == before,
        })]
    pub fn declare(
        &mut self,
        hole: HoleId,
        scope: Binders,
    ) -> Maybe<MetaId, declaration::Absent>
    {
        if self.by_hole.contains_key(&hole) {
            return Maybe::Absent(declaration::Absent::Redeclared);
        }
        let id = MetaId(self.entries.len());
        self.entries.push(Entry {
            hole,
            scope,
            solution: Maybe::Absent(meta_lookup::Absent::Unsolved),
        });
        let _fresh = self.by_hole.insert(hole, id);
        if let Some(ref mut journal) = self.journal {
            journal.push(Undo::Declared(hole));
        }
        Maybe::Present(id)
    }

    /// The metavariable `hole` stands for.
    ///
    /// # Specification
    /// - ensures: the identifier declared for `hole`, or
    ///   [`meta_lookup::Absent::Undeclared`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::declare`].
    /// - witness: `tests::solve::a_hole_is_declared_once`
    #[inline]
    #[spec(ensures: |output| self.by_hole.get(&hole).map_or_else(|| output == Maybe::Absent(meta_lookup::Absent::Undeclared), |&id| output == Maybe::Present(id)))]
    pub fn meta(
        &self,
        hole: HoleId,
    ) -> Maybe<MetaId, meta_lookup::Absent>
    {
        self.by_hole
            .get(&hole)
            .map_or(Maybe::Absent(meta_lookup::Absent::Undeclared), |&id| {
                Maybe::Present(id)
            })
    }

    /// The binders `meta`'s context holds.
    ///
    /// # Specification
    /// - ensures: the scope it was declared with, or
    ///   [`meta_lookup::Absent::OutOfRange`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a metavariable declared under one binder solved by a
    ///   term posed under two reads its solution lowered by one.
    /// - witness: `tests::solve::a_solution_is_read_in_its_own_context`
    #[inline]
    #[spec(ensures: |output| self.entries.get(usize::from(meta)).map_or_else(|| output == Maybe::Absent(meta_lookup::Absent::OutOfRange), |entry| output == Maybe::Present(entry.scope)))]
    pub fn scope(
        &self,
        meta: MetaId,
    ) -> Maybe<Binders, meta_lookup::Absent>
    {
        self.entries
            .get(meta.0)
            .map_or(Maybe::Absent(meta_lookup::Absent::OutOfRange), |entry| {
                Maybe::Present(entry.scope)
            })
    }

    /// The hole that stands for `meta`.
    ///
    /// # Specification
    /// - ensures: the declared hole, or [`meta_lookup::Absent::OutOfRange`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::declare`].
    /// - witness: `tests::solve::a_hole_is_declared_once`
    #[inline]
    #[spec(ensures: |output| self.entries.get(usize::from(meta)).map_or_else(|| output == Maybe::Absent(meta_lookup::Absent::OutOfRange), |entry| output == Maybe::Present(entry.hole)))]
    pub fn hole(
        &self,
        meta: MetaId,
    ) -> Maybe<HoleId, meta_lookup::Absent>
    {
        self.entries
            .get(meta.0)
            .map_or(Maybe::Absent(meta_lookup::Absent::OutOfRange), |entry| {
                Maybe::Present(entry.hole)
            })
    }

    /// The solution `meta` is bound to, in its own context.
    ///
    /// # Specification
    /// - ensures: the bound value; [`meta_lookup::Absent::Unsolved`] before the
    ///   solver binds it; [`meta_lookup::Absent::OutOfRange`] past the count. A
    ///   solution may mention metavariables the solver solved later: reading
    ///   through them is the reader's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decode of a metavariable against a base type
    ///   binds it to the quote, and one the problem never constrains stays
    ///   unsolved.
    /// - witness: `tests::solve::a_decoded_metavariable_takes_the_quote`
    /// - witness: `tests::solve::an_unconstrained_metavariable_stays_unsolved`
    #[inline]
    #[spec(ensures: |output| self.entries.get(usize::from(meta)).map_or_else(|| output == Maybe::Absent(meta_lookup::Absent::OutOfRange), |entry| output == entry.solution))]
    pub fn solution(
        &self,
        meta: MetaId,
    ) -> Maybe<ValueId, meta_lookup::Absent>
    {
        self.entries
            .get(meta.0)
            .map_or(Maybe::Absent(meta_lookup::Absent::OutOfRange), |entry| {
                entry.solution
            })
    }

    /// The number of declared metavariables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(&self) -> MetaCount
    {
        MetaCount(self.entries.len())
    }

    /// Bind `meta` to `solution`, written in its own context.
    ///
    /// # Specification
    /// - requires: `meta` is unsolved, and `solution` is written in its context
    ///   and mentions it nowhere: the solver's checks before it binds.
    /// - ensures: `meta` reads as solved by `solution`; an identifier past the
    ///   count binds nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::solution`].
    /// - witness: `tests::solve::a_decoded_metavariable_takes_the_quote`
    #[inline]
    #[spec(ensures: |()| self.entries.get(usize::from(meta)).is_none_or(|entry| entry.solution == Maybe::Present(solution)))]
    pub(crate) fn bind(
        &mut self,
        meta: MetaId,
        solution: ValueId,
    )
    {
        if let Some(entry) = self.entries.get_mut(meta.0) {
            let previous = core::mem::replace(&mut entry.solution, Maybe::Present(solution));
            if let Some(ref mut journal) = self.journal {
                journal.push(Undo::Bound(meta, previous));
            }
        }
    }

    /// Every declared metavariable, in declaration order.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn ids(&self) -> impl Iterator<Item = MetaId> + use<>
    {
        (0 .. self.entries.len()).map(MetaId)
    }

    /// The equations that wait, in the order they were postponed: what a
    /// caller refuses by name when its declaration ends.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn postponed(&self) -> &[Postponed]
    {
        &self.postponed
    }

    /// Put `waiting` in the store.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn postpone(
        &mut self,
        waiting: Postponed,
    )
    {
        self.postponed.push(waiting);
        if let Some(ref mut journal) = self.journal {
            journal.push(Undo::Postponed);
        }
    }

    /// Take out of the store every equation `meta` blocks, in the order they
    /// were postponed.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn wake(
        &mut self,
        meta: MetaId,
    ) -> Vec<Equation>
    {
        let mut woken = Vec::new();
        let mut left = Vec::new();
        for (place, postponed) in core::mem::take(&mut self.postponed).into_iter().enumerate() {
            if postponed.blockers().contains(&meta) {
                woken.push(postponed.equation());
                if self.journal.is_some() {
                    left.push((place, postponed));
                }
            }
            else {
                self.postponed.push(postponed);
            }
        }
        if let Some(ref mut journal) = self.journal
            && !left.is_empty()
        {
            journal.push(Undo::Woken(left));
        }
        woken
    }

    /// Run `trial` against this metacontext, then put back every change it
    /// made: a solver run on a candidate's equations, judged by its verdict
    /// alone, at the cost of what the run touched rather than of a copy of the
    /// whole metacontext.
    ///
    /// # Specification
    /// - ensures: `trial`'s answer, the metacontext equal to what it was before
    ///   — its metavariables, their solutions and the store, in order — however
    ///   `trial` declared, bound, postponed or woke; a trial run inside another
    ///   puts back its own changes before the outer one resumes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a trial that binds a metavariable, postpones an
    ///   equation and wakes one leaves the metacontext as it found it, and a
    ///   run outside one keeps what it does.
    /// - witness: `tests::solve::a_trial_leaves_the_metacontext_as_it_found_it`
    #[spec(captures: [entries = self.entries.len(), waiting = self.postponed.len()],
        ensures: |_| self.entries.len() == entries && self.postponed.len() == waiting)]
    #[inline]
    pub fn trial<Answer, Run>(
        &mut self,
        trial: Run,
    ) -> Answer
    where
        Run: FnOnce(&mut Self) -> Answer,
    {
        let outer = self.journal.replace(Vec::new());
        let answer = trial(self);
        let journal = core::mem::replace(&mut self.journal, outer).unwrap_or_default();
        for undo in journal.into_iter().rev() {
            match undo {
                Undo::Declared(hole) => {
                    let _declared = self.entries.pop();
                    let _mapped = self.by_hole.remove(&hole);
                },
                Undo::Bound(meta, previous) => {
                    if let Some(entry) = self.entries.get_mut(meta.0) {
                        entry.solution = previous;
                    }
                },
                Undo::Postponed => {
                    let _postponed = self.postponed.pop();
                },
                Undo::Woken(left) => {
                    for (place, postponed) in left {
                        self.postponed.insert(place, postponed);
                    }
                },
            }
        }
        answer
    }
}

/// A count of metavariables.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MetaCount(usize);

impl From<MetaCount> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: MetaCount) -> Self
    {
        count.0
    }
}
