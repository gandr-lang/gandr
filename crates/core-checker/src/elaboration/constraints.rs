//! Residual conversion equations, restricted to bare owed code constants, and
//! the collector a value declaration's judgement leaves them in, beside the
//! metavariables it solves for the implicits its calls omit.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::hole::HoleId;
use gandr_core_term::model::CandidatePlace;
use gandr_core_term::model::ModelSlot;
use gandr_core_term::model::Survivors;
use gandr_core_unify::MetaId;
use gandr_core_unify::Metas;
use gandr_core_unify::Reason;
use gandr_core_unify::Side;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::TypeNode;
use crate::Unsolved;

quenchant_shape::reason_enum! {
    /// Why an equation cannot enter the residual fragment.
    mod candidate {
        /// The equation has no bare owed flex head opposite a rigid head.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// Ordinary conversion must decide this equation.
            Rigid,
        }
    }
}

/// One conversion obligation on a bare module hole.
///
/// # Specification
/// - requires: constructed only by the elaboration conversion boundary.
/// - ensures: `hole` was owed when the equation was recorded; `flex` is its
///   decode with no application spine, and `rigid` has a constructor head.
/// - provides: a residual equation, not a unifier or a certificate of
///   emptiness.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact equations and blockers separate bare flex–rigid
///   suspension from rigid disagreement and flex–flex comparison.
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Equation
{
    /// The module hole whose filling may settle the comparison.
    hole: ConstantIndex,
    /// The stuck decode.
    flex: TypeNode,
    /// The type opposite the decode.
    rigid: TypeNode,
}

impl Equation
{
    /// The owed constant at the flex head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hole(&self) -> ConstantIndex
    {
        self.hole
    }

    /// The flex side, a decode of the bare hole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flex(&self) -> TypeNode
    {
        self.flex
    }

    /// The constructor-headed side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rigid(&self) -> TypeNode
    {
        self.rigid
    }
}

/// Whether a comparison was recorded instead of decided.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Deferred
{
    /// Continue the surrounding conjunction, retaining the equation.
    Yes,
    /// Run ordinary conversion.
    No,
}

/// What the solver made of a comparison whose side is the decode of a
/// metavariable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unified
{
    /// The solver bound the metavariables so the pair holds, or put the pair
    /// in its store: the surrounding conjunction goes on.
    Agreed,
    /// No binding of the metavariables makes the pair hold.
    Refuted,
    /// No side is the decode of a metavariable: ordinary conversion decides.
    Rigid,
}

/// Whether the running judgement may leave residuals.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Collecting
{
    /// A nominal declaration's formation, or no judgement: every comparison
    /// is decided rigidly.
    #[default]
    Off,
    /// A value declaration's judgement: a bare owed flex–rigid equation is
    /// recorded, and a read of a waiting declaration is a dependency.
    On,
}

/// What one value declaration's judgement left undecided: the equations it
/// recorded and the waiting declarations it read.
///
/// # Specification
/// - requires: taken from the collector once the verdict's run ends.
/// - ensures: the equations in the order the judgement recorded them; the
///   dependencies are the waiting declarations whose types it read.
/// - provides: the input a [`super::Suspension`] is built from.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a residual alone, a waiting read alone and neither
///   separate the three answers of [`Residue::pending`].
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Residue
{
    /// The equations recorded.
    pub equations: Vec<Equation>,
    /// The waiting declarations read.
    pub dependencies: BTreeSet<ConstantIndex>,
}

impl Residue
{
    /// Whether the judgement waits: it recorded an equation or read a waiting
    /// declaration.
    ///
    /// # Specification
    /// trivial.
    pub fn pending(&self) -> Deferred
    {
        if self.equations.is_empty() && self.dependencies.is_empty() {
            Deferred::No
        }
        else {
            Deferred::Yes
        }
    }
}

/// The residual collector: the holes a comparison may wait on, the
/// declarations that wait, and what the running judgement left.
///
/// An empty owed set disables suspension, so a context that never judged an
/// owed hole decides every comparison as ordinary checking does.
#[derive(Default)]
pub struct Deferrals
{
    /// The only constants eligible as flex heads: the holes judged owed.
    pub owed: BTreeSet<ConstantIndex>,
    /// The declarations judged suspended; a judgement reading one waits too.
    pub suspended: BTreeSet<ConstantIndex>,
    /// Whether the running judgement collects.
    pub collecting: Collecting,
    /// What the running judgement left.
    pub residue: Residue,
    /// Per-occurrence transport, enabled only for a term-producing run.
    pub emission: super::output::Emission,
    /// The metavariables of the running judgement: each hole a call
    /// nominated for an implicit it omits, declared where the judgement met
    /// it.
    pub metas: Metas,
    /// The nodes of the nominated holes the running judgement met, in the
    /// order it met them.
    pub nominated: Vec<ValueId>,
}

impl Deferrals
{
    /// Start one declaration's judgement: `collecting` says whether it may
    /// leave residuals; nothing an earlier judgement left is kept.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the residue is empty, the collector is in `collecting`, and a
    ///   recording emission holds no transport; the owed and suspended sets are
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two suspended declarations judged in turn keep their
    ///   own blockers, and a nominal declaration after an owed hole forms
    ///   rigidly.
    /// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
    /// - witness: `elaboration::tests::resumptions_commute`
    #[spec(
        captures: [owed = self.owed.len(), suspended = self.suspended.len()],
        ensures: self.collecting == collecting && self.residue.equations.is_empty()
            && self.residue.dependencies.is_empty()
            && self.nominated.is_empty() && usize::from(self.metas.count()) == 0
            && self.owed.len() == owed && self.suspended.len() == suspended,
    )]
    pub fn open(
        &mut self,
        collecting: Collecting,
    )
    {
        self.collecting = collecting;
        self.residue = Residue::default();
        self.emission.restart();
        self.metas = Metas::new();
        self.nominated.clear();
    }

    /// Take what the running judgement left, leaving the residue empty.
    ///
    /// # Specification
    /// trivial.
    pub fn take(&mut self) -> Residue
    {
        core::mem::take(&mut self.residue)
    }

    /// Note that the running judgement read `constant`'s type: a dependency
    /// when `constant` waits and the judgement collects.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` is a dependency exactly when the collector is on
    ///   and `constant` is suspended; nothing else changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reference to a waiting declaration and one to a
    ///   checked declaration separate a dependency from a plain read.
    /// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    #[spec(
        captures: count = self.residue.dependencies.len(),
        ensures: if self.collecting == Collecting::On && self.suspended.contains(&constant) {
            self.residue.dependencies.contains(&constant)
        } else {
            self.residue.dependencies.len() == count
        },
    )]
    pub fn read(
        &mut self,
        constant: ConstantIndex,
    )
    {
        if self.collecting == Collecting::On && self.suspended.contains(&constant) {
            self.residue.dependencies.insert(constant);
        }
    }

    /// Recognize either orientation of a bare flex–rigid equation.
    ///
    /// # Specification
    /// - requires: the arguments are weak-head types of the same family.
    /// - ensures: returns the first orientation with a bare owed code constant
    ///   and a constructor-headed opposite side; otherwise
    ///   `candidate::Absent::Rigid`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reversed orientation, rigid and flex–flex controls in
    ///   both the value and the computation family distinguish the eligibility
    ///   boundary without claiming unification.
    /// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
    /// - witness: `elaboration::tests::computation_code_decodes_suspend_as_value_ones_do`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(equation) => self.owed.contains(&equation.hole),
        Maybe::Absent(_) => true,
    })]
    fn candidate(
        &self,
        arena: &CoreArena,
        left: TypeNode,
        right: TypeNode,
    ) -> Maybe<Equation, candidate::Absent>
    {
        for (flex, rigid) in [(left, right), (right, left)] {
            let code = match (flex, rigid) {
                (TypeNode::Value(flex), TypeNode::Value(rigid)) => {
                    match (arena.value_type(flex), arena.value_type(rigid)) {
                        (Some(&ValueType::Element { code, .. }), Some(other))
                            if !matches!(*other, ValueType::Element { .. }) =>
                        {
                            code
                        },
                        _ => continue,
                    }
                },
                (TypeNode::Computation(flex), TypeNode::Computation(rigid)) => {
                    match (arena.comp_type(flex), arena.comp_type(rigid)) {
                        (Some(&CompType::Element { code, .. }), Some(other))
                            if !matches!(*other, CompType::Element { .. }) =>
                        {
                            code
                        },
                        _ => continue,
                    }
                },
                _ => continue,
            };
            if let Some(&Value::Constant(hole)) = arena.value(code)
                && self.owed.contains(&hole)
            {
                return Maybe::Present(Equation { hole, flex, rigid });
            }
        }
        Maybe::Absent(candidate::Absent::Rigid)
    }

    /// Accumulate a residual without changing ordinary checking contexts.
    ///
    /// # Specification
    /// - requires: both nodes are weak-head types of the same family.
    /// - ensures: `Yes` records one eligible equation; `No` changes nothing. A
    ///   collector that is off, or has no owed flex head, always answers `No`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an owed decode suspends a value declaration; a rigid
    ///   decode keeps the rigid mismatch, and a collector that is off defers
    ///   nothing while holes are owed.
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    /// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
    /// - witness: `elaboration::tests::an_off_collector_never_defers`
    #[spec(
        captures: before = self.residue.equations.len(),
        ensures: |ret| match ret {
            Deferred::Yes => self.residue.equations.len() == before.saturating_add(1),
            Deferred::No => self.residue.equations.len() == before,
        },
    )]
    pub fn defer(
        &mut self,
        arena: &CoreArena,
        left: TypeNode,
        right: TypeNode,
    ) -> Deferred
    {
        if self.collecting == Collecting::Off || self.owed.is_empty() {
            return Deferred::No;
        }
        match self.candidate(arena, left, right) {
            Maybe::Present(equation) => {
                self.residue.equations.push(equation);
                Deferred::Yes
            },
            Maybe::Absent(_) => Deferred::No,
        }
    }

    /// Declare the nominated hole `hole`, met at `at` under `scope`
    /// intuitionistic binders, a metavariable of the running judgement.
    ///
    /// # Specification
    /// - requires: `at` is the node of `hole`, which a call nominated.
    /// - ensures: `hole` is a metavariable whose context holds `scope` binders,
    ///   and `at` is met; a hole met before keeps its first context, and is not
    ///   met twice.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call omitting an implicit declares its hole once,
    ///   at the call's binders, and the solution stands in that context.
    /// - witness: `elaboration::tests::an_omitted_implicit_is_solved_from_the_argument_1216`
    #[spec(
        captures: before = self.nominated.len(),
        ensures: matches!(self.metas.meta(hole), Maybe::Present(_))
            && self.nominated.len() <= before.saturating_add(1),
    )]
    pub fn nominate(
        &mut self,
        at: ValueId,
        hole: HoleId,
        scope: Binders,
    )
    {
        if let Maybe::Present(_) = self.metas.declare(hole, scope) {
            self.nominated.push(at);
        }
    }

    /// The metavariable `side` is, or is the decode of, when the running
    /// judgement declared one.
    ///
    /// # Specification
    /// trivial.
    fn decoded(
        &self,
        arena: &CoreArena,
        side: Side,
    ) -> Option<MetaId>
    {
        let hole = match side {
            Side::Value(at) => at,
            Side::ValueType(at) => match arena.value_type(at) {
                Some(&ValueType::Element { code, .. } | &ValueType::RowTail(code)) => code,
                _ => return None,
            },
            Side::CompType(at) => match arena.comp_type(at) {
                Some(&CompType::Element { code, .. }) => code,
                _ => return None,
            },
        };
        match arena.value(hole) {
            Some(&Value::Hole(hole)) => match self.metas.meta(hole) {
                Maybe::Present(meta) => Some(meta),
                Maybe::Absent(_) => None,
            },
            _ => None,
        }
    }

    /// Why the solver left `meta` unbound: the reason of the first equation
    /// in its store that waits on `meta`, names it, or has its decode at a
    /// head; unforced when none does.
    ///
    /// # Specification
    /// trivial.
    fn unsolved(
        &self,
        arena: &CoreArena,
        meta: MetaId,
    ) -> Unsolved
    {
        let named = |reason| match reason {
            Reason::Pruning { meta: named, .. }
            | Reason::Escape { meta: named }
            | Reason::Occurs { meta: named }
            | Reason::Scope { meta: named } => Some(named),
            Reason::Unfolding
            | Reason::Gradual
            | Reason::Spine
            | Reason::Outside
            | Reason::Families
            | Reason::Neutral
            | Reason::Levels
            | Reason::Linear
            | Reason::Dangling
            | Reason::Budget
            | Reason::Rows => None,
        };
        self.metas
            .postponed()
            .iter()
            .find(|waiting| {
                let equation = waiting.equation();
                waiting.blockers().contains(&meta)
                    || named(waiting.reason()) == Some(meta)
                    || [equation.left(), equation.right()]
                        .into_iter()
                        .any(|side| self.decoded(arena, side) == Some(meta))
            })
            .map_or(Unsolved::Unforced, |waiting| {
                Unsolved::from(waiting.reason())
            })
    }

    /// Pose `left` against `right`, under `scope` intuitionistic binders, to
    /// the solver when a side is the decode of a metavariable.
    ///
    /// # Specification
    /// - requires: both nodes are weak-head types of the same family, read in
    ///   the context of `scope` binders.
    /// - ensures: [`Unified::Rigid`], with nothing changed, unless a side is
    ///   the decode of a metavariable; otherwise the solver's run over the one
    ///   equation: [`Unified::Refuted`] when it refutes it, and
    ///   [`Unified::Agreed`] when it solves it or puts it in the store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decode of an omitted implicit against the type
    ///   its argument synthesises binds it, the same decode against a second,
    ///   different type is refuted, and a pair with no decode of a metavariable
    ///   is left to conversion.
    /// - witness: `elaboration::tests::an_omitted_implicit_is_solved_from_the_argument_1216`
    /// - witness: `elaboration::tests::two_arguments_disagreeing_on_an_implicit_are_apart_1216`
    #[spec(
        captures: before = usize::from(self.metas.count()),
        ensures: |ret| usize::from(self.metas.count()) == before
            && (ret == Unified::Rigid || before > 0),
    )]
    pub fn unify(
        &mut self,
        arena: &mut CoreArena,
        scope: Binders,
        left: TypeNode,
        right: TypeNode,
    ) -> Unified
    {
        let (left, right) = match (left, right) {
            (TypeNode::Value(left), TypeNode::Value(right)) => {
                (Side::ValueType(left), Side::ValueType(right))
            },
            (TypeNode::Computation(left), TypeNode::Computation(right)) => {
                (Side::CompType(left), Side::CompType(right))
            },
            (TypeNode::Value(_), TypeNode::Computation(_))
            | (TypeNode::Computation(_), TypeNode::Value(_)) => return Unified::Rigid,
        };
        if self.nominated.is_empty()
            || (self.decoded(arena, left).is_none() && self.decoded(arena, right).is_none())
        {
            return Unified::Rigid;
        }
        self.pose(arena, scope, left, right)
    }

    /// Pose the value `left` against `right`, under `scope` intuitionistic
    /// binders, to the solver when a side is a metavariable: a wildcard a
    /// type holds against the term a judgement compares it with.
    ///
    /// # Specification
    /// - requires: both values are read in the context of `scope` binders, at
    ///   one type.
    /// - ensures: [`Unified::Rigid`], with nothing changed, unless a side is a
    ///   metavariable; otherwise the solver's run over the one equation:
    ///   [`Unified::Refuted`] when it refutes it, and [`Unified::Agreed`] when
    ///   it solves it or puts it in the store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path's open end against the point that reaches it
    ///   is bound to the point, a second, different point is refuted, and two
    ///   rigid values are left to conversion.
    /// - witness: `elaboration::tests::an_open_end_is_solved_from_its_point_1979`
    #[spec(
        captures: before = usize::from(self.metas.count()),
        ensures: |ret| usize::from(self.metas.count()) == before
            && (ret == Unified::Rigid || before > 0),
    )]
    pub fn unify_values(
        &mut self,
        arena: &mut CoreArena,
        scope: Binders,
        left: ValueId,
        right: ValueId,
    ) -> Unified
    {
        let (left, right) = (Side::Value(left), Side::Value(right));
        if self.nominated.is_empty()
            || (self.decoded(arena, left).is_none() && self.decoded(arena, right).is_none())
        {
            return Unified::Rigid;
        }
        self.pose(arena, scope, left, right)
    }

    /// Pose the row `left` against `right`, under `scope` intuitionistic
    /// binders, to the solver when a side is open through a metavariable: the
    /// two rows as row values, so the solver decides them by the row equation.
    ///
    /// # Specification
    /// - requires: both rows are read in the context of `scope` binders.
    /// - ensures: [`Unified::Rigid`], with nothing changed, unless a row's tail
    ///   stands over a metavariable; otherwise the solver's run over the one
    ///   equation: [`Unified::Refuted`] when it refutes it, and
    ///   [`Unified::Agreed`] when it solves it or puts it in the store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row open through a metavariable against a closed
    ///   row binds the metavariable to what the closed row writes beyond it,
    ///   one writing an instance the closed row lacks is refuted, and two rows
    ///   over no metavariable are left to conversion.
    /// - witness: `elaboration::tests::a_row_open_through_an_implicit_is_solved_by_the_row_equation_2270`
    #[spec(
        captures: before = usize::from(self.metas.count()),
        ensures: |ret| usize::from(self.metas.count()) == before
            && (ret == Unified::Rigid || before > 0),
    )]
    pub fn unify_rows(
        &mut self,
        arena: &mut CoreArena,
        scope: Binders,
        (left, right): (&EffectRow, &EffectRow),
    ) -> Unified
    {
        let open = |row: &EffectRow| {
            row.tail()
                .is_some_and(|tail| self.decoded(arena, Side::ValueType(tail)).is_some())
        };
        if self.nominated.is_empty() || (!open(left) && !open(right)) {
            return Unified::Rigid;
        }
        let left = arena.value_row(left.clone());
        let right = arena.value_row(right.clone());
        self.pose(arena, scope, Side::Value(left), Side::Value(right))
    }

    /// The solver's run over the one equation `left` against `right`.
    ///
    /// # Specification
    /// trivial.
    fn pose(
        &mut self,
        arena: &mut CoreArena,
        scope: Binders,
        left: Side,
        right: Side,
    ) -> Unified
    {
        let equation = gandr_core_unify::Equation::new(scope, left, right);
        match gandr_core_unify::solve(arena, &mut self.metas, &[equation]) {
            gandr_core_unify::Verdict::Solved | gandr_core_unify::Verdict::Postponed => {
                Unified::Agreed
            },
            gandr_core_unify::Verdict::Refuted(_) => Unified::Refuted,
        }
    }

    /// Each nominated hole the running judgement met, with its solution and
    /// the binders the solution is written under, or the node of the first
    /// one the solver left unbound and why.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per hole met, its solution in its own context and
    ///   that context's binders, when every one is bound; the first unbound
    ///   one's node otherwise, with the reason of the first equation in the
    ///   store that waits on it, names it or has its decode at a head, or
    ///   [`Unsolved::Unforced`] when none does; nothing when the judgement met
    ///   none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call whose argument forces its implicit answers the
    ///   solution; one whose arguments force none answers the hole, unforced;
    ///   one whose only solution names a binder of an argument's own lambda
    ///   answers the hole and its escape.
    /// - witness: `elaboration::tests::an_omitted_implicit_is_solved_from_the_argument_1216`
    /// - witness: `elaboration::tests::an_implicit_no_argument_forces_is_unsolved_1216`
    /// - witness: `elaboration::tests::an_implicit_solved_past_its_scope_escapes_1216`
    #[spec(ensures: |ret| ret.as_ref().map_or(!self.nominated.is_empty(), |solutions| {
        solutions.len() == self.nominated.len()
    }))]
    pub fn solutions(
        &self,
        arena: &CoreArena,
    ) -> Result<BTreeMap<HoleId, (ValueId, Binders)>, (ValueId, Unsolved)>
    {
        let mut solutions = BTreeMap::new();
        for &at in &self.nominated {
            let Some(meta) = self.decoded(arena, Side::Value(at))
            else {
                return Err((at, Unsolved::Dangling));
            };
            match (
                arena.value(at),
                self.metas.solution(meta),
                self.metas.scope(meta),
            ) {
                (Some(&Value::Hole(hole)), Maybe::Present(solution), Maybe::Present(scope)) => {
                    let _first = solutions.insert(hole, (solution, scope));
                },
                (_, Maybe::Present(_) | Maybe::Absent(_), Maybe::Present(_) | Maybe::Absent(_)) => {
                    return Err((at, self.unsolved(arena, meta)));
                },
            }
        }
        Ok(solutions)
    }

    /// Resolve each slot of `models` the running judgement met to the one
    /// candidate the solver's store leaves, binding the slot's holes as that
    /// candidate's components.
    ///
    /// # Specification
    /// - requires: the judgement over the body has run, so every equation its
    ///   arguments force has been posed.
    /// - ensures: for each slot, in order, every hole of which the judgement
    ///   met and some hole of which the solver left unbound: each candidate is
    ///   tried on a copy of the store, its components posed against the holes
    ///   and its code of each sort the slot fixes against the slot's, where the
    ///   slot's code reads no binder of the callee, and one the solver refutes
    ///   is dropped; a single candidate left binds the holes as its trial did.
    ///   A slot whose holes are all bound, one a hole of which the judgement
    ///   did not meet, and a candidate of another arity, or carrying another
    ///   number of fixed sorts, are left out.
    /// - fails: [`CheckRefusal::ModelUnanswered`] at the slot's first hole when
    ///   no candidate is left; [`CheckRefusal::ModelAmbiguous`] there, naming
    ///   every candidate left, when more than one is.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// One trial per candidate of each finite slot, each a run of the solver,
    /// which its step budget bounds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a slot whose sort the argument forces resolves to the
    ///   candidate of that sort, its operation then solved as the candidate's;
    ///   two candidates of the forced sort are ambiguous, naming both; a slot
    ///   no candidate of the forced sort answers is unanswered; a slot whose
    ///   type fixes the sort resolves to the candidate of that sort alone.
    /// - witness: `elaboration::tests::a_model_slot_resolves_to_the_candidate_its_sort_admits_739`
    /// - witness: `elaboration::tests::a_model_slot_two_candidates_answer_is_ambiguous_739`
    /// - witness: `elaboration::tests::a_model_slot_no_candidate_answers_is_refused_739`
    /// - witness: `elaboration::tests::a_manifest_model_slot_resolves_to_the_candidate_of_its_fixed_sort_2317`
    #[spec(ensures: |ret| match ret {
        | Err((at, CheckRefusal::ModelAmbiguous { at: named, survivors })) => at == named && (survivors.places().count() > 1 || u32::from(survivors.beyond()) > 0),
        | Err((at, refusal)) => refusal == CheckRefusal::ModelUnanswered { at },
        | Ok(()) => true,
    })]
    pub fn resolve(
        &mut self,
        arena: &mut CoreArena,
        models: &[ModelSlot],
    ) -> Result<(), (ValueId, CheckRefusal)>
    {
        let met: BTreeMap<HoleId, ValueId> = self
            .nominated
            .iter()
            .filter_map(|&at| match arena.value(at) {
                Some(&Value::Hole(hole)) => Some((hole, at)),
                _ => None,
            })
            .collect();
        let mut holes: Vec<(ValueId, MetaId)> = Vec::new();
        let mut equations: Vec<gandr_core_unify::Equation> = Vec::new();
        let mut closed: Vec<(usize, ValueId)> = Vec::new();
        'slots: for slot in models {
            holes.clear();
            for hole in &slot.holes {
                let (Some(&at), Maybe::Present(meta)) = (met.get(hole), self.metas.meta(*hole))
                else {
                    continue 'slots;
                };
                holes.push((at, meta));
            }
            let Some(&(first, _)) = holes.first()
            else {
                continue;
            };
            if holes
                .iter()
                .all(|&(_, meta)| matches!(self.metas.solution(meta), Maybe::Present(_)))
            {
                continue;
            }
            closed.clear();
            closed.extend(
                slot.fixed
                    .iter()
                    .enumerate()
                    .filter(|&(_, &code)| {
                        crate::code::loose_reach(
                            arena,
                            crate::refusal::CoreNode::Term(crate::refusal::TermNode::Value(code)),
                        )
                        .is_ok_and(|reach| usize::from(reach) == 0)
                    })
                    .map(|(place, &code)| (place, code)),
            );
            let mut survivors = Survivors::default();
            let mut count = 0_usize;
            let mut chosen = None;
            for (place, candidate) in slot.candidates.iter().enumerate() {
                if candidate.components.len() != holes.len()
                    || candidate.fixed.len() != slot.fixed.len()
                {
                    continue;
                }
                let mut trial = self.metas.clone();
                equations.clear();
                equations.extend(holes.iter().zip(&candidate.components).map(
                    |(&(at, meta), &component)| {
                        let scope = match trial.scope(meta) {
                            Maybe::Present(scope) => scope,
                            Maybe::Absent(_) => Binders::NONE,
                        };
                        gandr_core_unify::Equation::new(
                            scope,
                            Side::Value(at),
                            Side::Value(component),
                        )
                    },
                ));
                equations.extend(closed.iter().filter_map(|&(sort, code)| {
                    candidate.fixed.get(sort).map(|&own| {
                        gandr_core_unify::Equation::new(
                            Binders::NONE,
                            Side::Value(code),
                            Side::Value(own),
                        )
                    })
                }));
                if let gandr_core_unify::Verdict::Refuted(_) =
                    gandr_core_unify::solve(arena, &mut trial, &equations)
                {
                    continue;
                }
                survivors = survivors.with(CandidatePlace::from(place));
                count = count.saturating_add(1);
                if chosen.is_none() {
                    chosen = Some(trial);
                }
            }
            match (count, chosen) {
                (1, Some(trial)) => self.metas = trial,
                (0, _) | (_, None) => {
                    return Err((first, CheckRefusal::ModelUnanswered { at: first }));
                },
                _ => {
                    return Err((first, CheckRefusal::ModelAmbiguous {
                        at: first,
                        survivors,
                    }));
                },
            }
        }
        Ok(())
    }
}
