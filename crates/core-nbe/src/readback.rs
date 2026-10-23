//! Readback: a glued domain node back into a core term, as a machine over an
//! explicit task stack.
//!
//! # Readback is where a face is chosen
//!
//! The domain populates two faces and reads neither. This is the consumer that
//! reads them, and the mode it runs in is what the choice is spelled as:
//!
//! - [`ReadbackMode::ZeroUnfold`] prefers the **term face**. A value whose face
//!   is [`TermFace::Source`] hands back the core node it came from, so an
//!   unreduced subterm costs one id and rebuilds nothing, and the sharing the
//!   core arena already carried survives the round trip. It never **spends** or
//!   forces a neutral's unfolding face — the face is read, because the mode's
//!   own arm is what declines to act on it — so an [`Unfolding::Unforced`] body
//!   is still unforced when the readback returns, which is the property a
//!   conversion stands on when it compares neutral forms before it falls back
//!   to unfolding.
//! - [`ReadbackMode::Unfolding`] ignores the term face and rebuilds from the
//!   domain node, so the result is in canonical binder form and two results are
//!   comparable by structure alone. It spends a neutral's unfolding face,
//!   forcing an unforced body first: the body's lowering is read from the run's
//!   [`LoweredChain`](crate::LoweredChain), evaluated in the empty environment
//!   from the readback's own budget, and recorded on the neutral, so a neutral
//!   met twice evaluates its body once. Every body the chain holds is lowered,
//!   so the only body it can refuse is one no entry of the chain names — a
//!   neutral minted by hand or by another run's definitions — rather than
//!   answering the neutral form under a mode that promised to unfold it.
//!
//! The two modes are one nominal input rather than a flag, because a caller
//! that passed the wrong boolean would get a *different term*, not a slower
//! one.
//!
//! # The source-face short circuit is sound exactly where the input is scoped
//!
//! Evaluation marks a node [`TermFace::Source`] only when nothing under it
//! reduced: every child came back denoting the corresponding source child, and
//! a closure captured the **empty** environment. Over a well-scoped input those
//! two conditions make the source node **closed** — a bound occurrence resolves
//! out of the environment and costs its parent the face, and a closure that
//! kept the face captured nothing — so splicing the source id under any number
//! of open binders denotes what it always denoted.
//!
//! **That is a precondition, not a theorem about arbitrary arena content.** A
//! core term with a loose de Bruijn index inside an unevaluated thunk body is
//! never rejected, because the body is never evaluated: `thunk (λ. return x₁)`
//! read in the empty environment keeps its face, and splicing it under one open
//! binder would capture the loose index. The mitigation is the same run
//! discipline the domain arena already states for the core ids it holds — this
//! readback is run over content evaluated from well-scoped terms — rather than
//! a check, because checking closedness is the whole traversal the short
//! circuit exists to avoid.
//!
//! # Levels go back to indices
//!
//! Going under a binder mints a fresh [`NeutralHead::Variable`] at a de Bruijn
//! **level**, so alpha-equivalence is identity in the domain and a binder never
//! depends on an allocation order. The core syntax counts **indices**, so every
//! variable head is converted back on the way out: at `depth` open binders in
//! its zone, a level `l` is the index `depth - l - 1`. Both subtractions are
//! checked, and a level that counts outside the binders this readback opened is
//! refused by name rather than wrapped into a different variable.
//!
//! # One arena is read, one is written, and the faults say which
//!
//! Readback resolves domain ids constantly and reads **no** core node but a
//! mark's body: it mints into the core arena and splices ids the domain
//! already holds. So a domain-arena miss arrives as [`ReadbackFault::Domain`]
//! carrying the domain's own refusal, and the only way a core-arena miss can
//! arise is inside an evaluation the readback drives — opening a closure or
//! forcing a lowered body — where it arrives as [`ReadbackFault::Eval`]
//! carrying [`EvalFault::DanglingTerm`]. Neither is translated into the
//! other's vocabulary.
//!
//! # A hole reads back as itself, a mark through its environment
//!
//! A hole-headed neutral reads back as the hole it stands on, with its spine
//! folded over it as any neutral's is. A hole names no variable, so the term is
//! well scoped wherever it is spliced; the environment the hole was met in
//! stays with the domain node, which is where a fill reads it. A mark's body
//! was never evaluated, so it is read back by substitution rather than by
//! evaluation: each environment entry is read back at the binders open where
//! the mark stands, and the mark's body takes them all at once.
//!
//! # Fuel, because readback drives evaluation
//!
//! Going under a binder evaluates the closure's body to weak head, and forcing
//! a body evaluates its lowering, so readback is a normalizer and inherits
//! every way normalization fails to stop. The machine carries a [`Fuel`]
//! budget, spends one unit per task it pops, and hands the remainder to each
//! evaluation it drives so the two share one budget rather than each holding
//! its own.
//!
//! # Readback modes
//!
//! `ReadbackMode::ZeroUnfold` prefers the term face: a node whose face is
//! `TermFace::Source` hands back that core id and mints nothing, and no
//! unfolding is forced, so an `Unfolding::Unforced` body is still unforced when
//! readback returns. `ReadbackMode::Unfolding` ignores the term face, rebuilds
//! every node in canonical binder form so two results compare by structure, and
//! spends every unfolding, forcing an unforced one from the run's
//! `LoweredChain` first. The mode is a nominal input rather than a flag,
//! because the wrong mode yields a different term. At `depth` open binders in
//! its zone a level `l` is the index `depth - l - 1`; both subtractions are
//! checked, and a level outside the opened binders is refused by name. A
//! missing domain reference surfaces as `ReadbackFault::Domain`. Reading quoted
//! formers also consults core nodes: a missing quoted type or quote body is
//! `ReadbackFault::MachineInvariant`, while a failure from a driven evaluation
//! remains `ReadbackFault::Eval`.
//!
//! One budget covers the readback tasks and every evaluation they drive. A
//! force completed before a later refusal remains cached in the domain;
//! truncating the core arena does not undo it. Budget witnesses therefore start
//! each attempt from the same domain state, so a failed attempt cannot
//! subsidize its successor. The measured minimum succeeds independently and one
//! less refuses. Witness:
//! `readback::tests::budget_search_does_not_reuse_forcing_from_failed_attempts`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::substitute_environment;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::Summand;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::arena::ValueClosureId;
use crate::closure::Environment;
use crate::closure::EnvironmentDepth;
use crate::domain::BinderLevel;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::LiftTarget;
use crate::domain::NeutralHead;
use crate::domain::Reading;
use crate::domain::Suspended;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::apply_static_within;
use crate::eval::eval_closed_value;
use crate::eval::eval_value_within;

/// Which of the domain's two faces a readback spends.
///
/// The mode is an input rather than a flag because the two answers are
/// different terms: one retains the source ids the evaluation preserved, the
/// other rebuilds every node and spends what has been unfolded.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReadbackMode
{
    /// Prefer the term face and **force nothing**: a node whose face is
    /// [`TermFace::Source`] hands back that core node, and a neutral is always
    /// read through its neutral form, whatever its unfolding face holds.
    ZeroUnfold,
    /// Ignore the term face and rebuild, spending a neutral's unfolding face:
    /// a forced one is spent as it stands, and an unforced one is forced from
    /// the lowering the run's [`LoweredChain`](crate::LoweredChain) holds. A
    /// body no entry of the chain names is refused with
    /// [`ReadbackFault::UnloweredBody`].
    Unfolding,
}

/// Why a readback was refused.
///
/// Every variant is a fail-closed answer rather than a panic, and each names
/// the arena or the machine the condition belongs to rather than collapsing
/// them into one "something dangled".
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ReadbackFault
{
    /// The budget ran out on the readback's own task stack. The value may or
    /// may not have a normal form; the machine declines rather than continuing.
    OutOfFuel,
    /// The **domain** arena refused, in its own vocabulary. Carried rather than
    /// translated, so a refusal never arrives under a name that describes a
    /// different condition.
    Domain(DomainFault),
    /// The evaluation an opened closure drove refused, in **its** own
    /// vocabulary. This is the only path by which a core-arena miss or an
    /// ill-shaped elimination reaches a readback, and it arrives under
    /// evaluation's name — including [`EvalFault::OutOfFuel`], which says the
    /// shared budget ran out inside a closure rather than on this machine's own
    /// stack.
    Eval(EvalFault),
    /// A variable head named a de Bruijn level that counts outside the binders
    /// this readback has opened in that zone. Converting it would produce a
    /// different variable rather than the one the head named.
    LevelOutOfScope
    {
        /// The zone the level counts in.
        zone: Zone,
        /// The level that resolved to no open binder.
        level: BinderLevel,
    },
    /// One more binder would count past the level ceiling of its zone. The
    /// readback declines rather than reusing the ceiling level for two binders,
    /// which would make two distinct variables convert to one index.
    BinderCeiling
    {
        /// The zone whose binders reached the ceiling.
        zone: Zone,
    },
    /// A mode that spends unfoldings met a body named by a canonical
    /// subterm-table entry index, never forced, that no entry of the run's
    /// [`LoweredChain`](crate::LoweredChain) names. Every body the chain holds
    /// is lowered by construction, so this is a neutral minted by hand or by
    /// another run's definitions; the readback declines rather than silently
    /// answering the neutral form.
    UnloweredBody
    {
        /// The body's canonical subterm-table entry index.
        body: GlobalIndex,
    },
    /// A neutral's head and spine do not compose to the polarity the neutral
    /// stands in: a computation-position neutral whose spine never leaves value
    /// polarity, an application stacked where no computation has been reached,
    /// a `force` stacked on a computation, or a value-position neutral carrying
    /// a spine at all.
    NeutralPolarity
    {
        /// The neutral whose composition did not land.
        neutral: NeutralId,
    },
    /// An internal invariant broke: a frame found no operand where one of its
    /// own tasks should have left one. Unreachable while the machine's own
    /// pushes are the only source of tasks; reported rather than asserted, so a
    /// future frame that miscounts surfaces as a refusal instead of a wrong
    /// term.
    MachineInvariant,
}

/// The number of binders a readback has opened in one zone, which is also the
/// level the next binder of that zone takes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ZoneDepth(u32);

/// The binders a readback has opened, counted per zone.
///
/// It mirrors [the environment]'s two zones for the same forced reason: a
/// variable head names a zone as well as a level, and one counter could not
/// answer a level in the zone it was not counting.
///
/// [the environment]: crate::closure::Environment
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct OpenBinders
{
    /// The intuitionistic zone's open binders.
    intuitionistic: ZoneDepth,
    /// The linear zone's open binders.
    linear: ZoneDepth,
}

impl OpenBinders
{
    /// No binder open in either zone, which is where a whole-term readback
    /// starts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn none() -> Self
    {
        Self::default()
    }

    /// How many binders are open in `zone`.
    ///
    /// # Specification
    /// - requires: nothing; either zone may be at any depth.
    /// - ensures: `self.intuitionistic` for [`Zone::Intuitionistic`] and
    ///   `self.linear` for [`Zone::Linear`], so the two zones' counters are
    ///   never read for each other.
    /// - provides: the per-zone depth a fresh level and an index conversion are
    ///   both computed against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal zone depths are observed before and after
    ///   opening either zone. Reading the peer counter changes a fresh level or
    ///   converted index.
    /// - witness: `readback::tests::opening_a_binder_counts_one_zone_and_leaves_the_other`
    /// - witness: `readback::tests::a_level_becomes_the_index_counting_the_other_way`
    #[spec(
        ensures: |ret| ret.0 == match zone { Zone::Intuitionistic => self.intuitionistic.0, Zone::Linear => self.linear.0 },
    )]
    #[inline]
    fn depth(
        self,
        zone: Zone,
    ) -> ZoneDepth
    {
        match zone {
            Zone::Intuitionistic => self.intuitionistic,
            Zone::Linear => self.linear,
        }
    }

    /// The level the next binder opened in `zone` takes.
    ///
    /// Levels count inward from the empty context, so the next one is exactly
    /// the number already open — which is what makes a binder's identity
    /// independent of how deep the reader has gone.
    ///
    /// # Specification
    /// - requires: nothing; either zone may already be at its ceiling.
    /// - ensures: the level equal to the number of binders already open in
    ///   `zone`, so the level a binder takes is fixed by the zone's depth where
    ///   it is opened and by nothing else.
    /// - provides: the identity a variable head carries, which is why a closure
    ///   can be entered under a fresh binder without shifting the environment.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested binders retain distinct levels while their
    ///   indices change under another binder. Reusing level zero or counting
    ///   from the innermost end captures the wrong variable.
    /// - witness: `readback::tests::nested_binders_read_back_as_the_indices_that_name_them`
    /// - witness: `readback::tests::a_quoted_dependent_arrow_reads_its_binder_as_an_index`
    #[spec(
        ensures: |ret| u32::from(ret) == self.depth(zone).0,
    )]
    #[inline]
    fn fresh(
        self,
        zone: Zone,
    ) -> BinderLevel
    {
        BinderLevel::from(self.depth(zone).0)
    }

    /// One more binder open in `zone`.
    ///
    /// # Specification
    /// - requires: nothing — a zone already at the ceiling is admissible input.
    /// - ensures: a copy whose `zone` counts one deeper and whose other zone is
    ///   untouched.
    /// - provides: the binder-entering step of every rule that goes under one.
    /// - fails: returns `None` at the level ceiling of the zone, which the
    ///   caller reports as [`ReadbackFault::BinderCeiling`] rather than reusing
    ///   the ceiling level for a second binder.
    /// - panics: none — the increment is checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the zone selection and the
    ///   checked increment, separated by opening each zone with the other
    ///   asserted unmoved, and by a zone held at the ceiling.
    /// - witness: `readback::tests::opening_a_binder_counts_one_zone_and_leaves_the_other`
    /// - witness: `readback::tests::the_binder_ceiling_is_refused_rather_than_reused`
    #[inline]
    #[spec(ensures: |ret| match (zone, ret) {
        | (Zone::Intuitionistic, Some(deeper)) => {
            Some(deeper.intuitionistic.0) == self.intuitionistic.0.checked_add(1_u32)
                && deeper.linear.0 == self.linear.0
        },
        | (Zone::Linear, Some(deeper)) => {
            Some(deeper.linear.0) == self.linear.0.checked_add(1_u32)
                && deeper.intuitionistic.0 == self.intuitionistic.0
        },
        | (Zone::Intuitionistic | Zone::Linear, None) => self.depth(zone).0 == u32::MAX,
    })]
    fn opened(
        self,
        zone: Zone,
    ) -> Option<Self>
    {
        let deeper = self.depth(zone).0.checked_add(1_u32)?;
        let deeper = ZoneDepth(deeper);
        Some(match zone {
            Zone::Intuitionistic => Self {
                intuitionistic: deeper,
                linear: self.linear,
            },
            Zone::Linear => Self {
                intuitionistic: self.intuitionistic,
                linear: deeper,
            },
        })
    }

    /// The de Bruijn index a `level` of `zone` counts at here.
    ///
    /// # Specification
    /// - requires: nothing — a level at or past the open binders is admissible
    ///   input.
    /// - ensures: `depth - level - 1`, the index counting binders outward from
    ///   this point, exactly when the level names one of the binders open in
    ///   `zone`.
    /// - provides: the one conversion from the domain's levels to the syntax's
    ///   indices, which is the whole reason a variable head carries a level.
    /// - fails: returns `None` when the level is at or past the zone's open
    ///   binders — including every level read against a zone with none open —
    ///   which the caller reports as [`ReadbackFault::LevelOutOfScope`].
    /// - panics: none — both subtractions are checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two decision surfaces are the two checked
    ///   subtractions, separated by the innermost and the outermost binder of a
    ///   two-deep zone, the first level at the depth, a level past it, and a
    ///   level read against a zone with nothing open.
    /// - witness: `readback::tests::a_level_becomes_the_index_counting_the_other_way`
    /// - witness: `readback::tests::a_level_outside_the_open_binders_is_refused`
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Some(index) => {
            u32::from(index)
                .checked_add(u32::from(level))
                .and_then(|counted| counted.checked_add(1_u32))
                == Some(self.depth(zone).0)
        },
        | None => u32::from(level) >= self.depth(zone).0,
    })]
    fn index(
        self,
        zone: Zone,
        level: BinderLevel,
    ) -> Option<DeBruijnIndex>
    {
        let remaining = self.depth(zone).0.checked_sub(u32::from(level))?;
        let index = remaining.checked_sub(1_u32)?;
        Some(DeBruijnIndex::from(index))
    }
}

/// Which polarity a partially folded neutral stands at.
///
/// A neutral's head is always a **value** — a variable, a declaration, a module
/// form — and its spine walks it into computation polarity and keeps it there.
/// The fold tracks that rather than inferring it from a stack's contents,
/// because inferring it is how an ill-shaped spine reads an unrelated operand
/// instead of being refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Polarity
{
    /// The fold holds a value term.
    Value,
    /// The fold holds a computation term.
    Computation,
}

/// A position within a neutral's spine, counting innermost first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SpineOffset(usize);

impl SpineOffset
{
    /// The innermost elimination's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn innermost() -> Self
    {
        Self(0_usize)
    }

    /// The next position outward.
    ///
    /// Saturating rather than checked: the offset only advances while the spine
    /// holds an entry at it, so the ceiling would need a spine of
    /// `usize::MAX` eliminations, which no arena can hold. At the ceiling the
    /// lookup finds nothing and the fold ends, which is a refusal or a result
    /// rather than a wrong term.
    ///
    /// # Specification
    /// - requires: nothing; the ceiling is admissible input.
    /// - ensures: the position one further out, and the ceiling again once
    ///   reached.
    /// - provides: the fold's advance. The paragraph above states why the
    ///   saturation is unreachable and why reaching it ends the fold rather
    ///   than misreading a spine.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered force and application frames distinguish
    ///   advancing once from repeating or skipping a frame. The ceiling cannot
    ///   index a realizable elimination vector; saturation is nevertheless
    ///   stated exactly.
    /// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
    /// - witness: `readback::tests::an_unfolded_operator_reads_back_reduced`
    #[spec(
        ensures: |ret| ret.0 == self.0.saturating_add(1_usize),
    )]
    #[inline]
    fn next(self) -> Self
    {
        Self(self.0.saturating_add(1_usize))
    }
}

/// One position of a neutral's spine fold.
///
/// The five parts travel together because every one of them is needed to fold
/// the next elimination, and splitting them across parameters is how a fold
/// ends up reading one neutral's spine against another's polarity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SpineStep
{
    /// The neutral whose spine is being folded.
    neutral: NeutralId,
    /// The position to fold next.
    at: SpineOffset,
    /// The polarity the fold currently stands at.
    polarity: Polarity,
    /// The polarity the finished fold must stand at, which is the polarity of
    /// the position the neutral itself stands in.
    wanted: Polarity,
    /// The binders open where the neutral stands.
    binders: OpenBinders,
}

impl SpineStep
{
    /// The step after this one.
    ///
    /// A computation eliminator leaves the fold at computation polarity
    /// whatever it stood at before; the static application, the one value
    /// eliminator, leaves it at value polarity.
    ///
    /// # Specification
    /// - requires: nothing; a position past the spine's end is admissible and
    ///   ends the fold at the lookup.
    /// - ensures: the same neutral, wanted polarity, and open binders, the
    ///   position advanced by one, and `polarity` — for the reason the
    ///   paragraph above states.
    /// - provides: the one step the spine fold advances by, so no rule
    ///   recomputes the polarity an elimination leaves behind.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a spine folding a static application then a
    ///   computation application, read back at each polarity.
    /// - witness: `readback::tests::an_unfolded_operator_reads_back_reduced`
    #[inline]
    #[spec(ensures: |ret| ret.polarity == polarity
        && ret.neutral == self.neutral
        && ret.wanted == self.wanted
        && ret.binders == self.binders
        && ret.at.0 == self.at.0.saturating_add(1_usize))]
    fn onward(
        self,
        polarity: Polarity,
    ) -> Self
    {
        Self {
            neutral: self.neutral,
            at: self.at.next(),
            polarity,
            wanted: self.wanted,
            binders: self.binders,
        }
    }
}

/// Whether entering a closure opens a binder over it.
///
/// A lambda, a bind continuation and a case branch each stand under one binder;
/// a thunk stands under none, because the core thunk former binds nothing and
/// suspends its body as it stands.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Entry
{
    /// Evaluate the body in exactly the environment the closure captured.
    Bare,
    /// Evaluate the body in the captured environment extended by one binding.
    Under
    {
        /// The zone the binder was opened in.
        zone: Zone,
        /// What the binder stands for: a fresh variable neutral.
        bound: DomainValueId,
    },
}

/// One unit of work on the machine's task stack.
///
/// Every variant either reads one domain node or assembles a core node from
/// operands its own earlier tasks left on the result stacks, so the stack is
/// the defunctionalized continuation of the recursive presentation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Task
{
    /// Read back a domain value.
    Value
    {
        /// The domain node.
        value: DomainValueId,
        /// The binders open where it stands.
        binders: OpenBinders,
    },
    /// Read back a domain computation at weak head.
    Comp
    {
        /// The domain node.
        comp: DomainCompId,
        /// The binders open where it stands.
        binders: OpenBinders,
    },
    /// Assemble a native product path.
    PathProduct,
    /// Assemble transport beneath a neutral path.
    Transport,
    /// Assemble product transport beneath a neutral pair.
    ProductTransport,
    /// Assemble element-path transport beneath a neutral path, from its
    /// motive and operand.
    PathTransport,
    /// Assemble element-path transport beneath a neutral operand, from its
    /// motive and path.
    OperandTransport,
    /// Assemble a ride beneath a neutral flow, from its motive and operand.
    Ride,
    /// Assemble a ride beneath a neutral operand, from its motive and flow.
    OperandRide,
    /// Assemble a telescope transport beneath a neutral path, from its motive,
    /// start, identity over the path and operand.
    TelescopeTransport,
    /// Assemble reflexivity over the value term on the stack.
    Here,
    /// Assemble univalence over the record and forward map on the stack.
    Univalence,
    /// Assemble a flow introduction of this former over the value terms on
    /// the stack, as many as it holds.
    Flow(crate::domain::FlowFormer),
    /// Assemble a compound endpoint over the computation term on the stack.
    Returned,
    /// Assemble an element identity from its carrier and two endpoints.
    PathType,
    /// Assemble a directed identity from its carrier and two endpoints.
    FlowType,
    /// Assemble a run type over the session code on the stack.
    RunType,
    /// Assemble a prefix type over the session code on the stack.
    PrefixType,
    /// Assemble a dialogue type over the session code on the stack.
    DialogueType,
    /// Assemble a tuple from its components, this many on the stack.
    Tuple(usize),
    /// Assemble a native list cell.
    ListCons,
    /// Assemble a native fold from its annotations, list and branches.
    ListFold,
    /// Assemble a native list case from its annotation, list and branches.
    ListCase,
    /// Assemble a sum injection.
    Inject
    {
        /// The summand injected into.
        summand: Summand,
    },
    /// Assemble a universe lift over the level the domain holds.
    Lift
    {
        /// The held level.
        target: LiftTarget,
    },
    /// Assemble a thunk from the computation term on the stack.
    Thunk,
    /// Assemble a lambda from the computation term on the stack.
    Lambda,
    /// Assemble a fixpoint, with its source's claim, from the computation
    /// term on the stack.
    Fixpoint(gandr_kernel_term::FixpointEvidence),
    /// Assemble a static lambda from the value term on the stack.
    StaticLambda,
    /// Assemble a returner from the value term on the stack.
    Return,
    /// Fold one more of a neutral's eliminations onto the term beneath it.
    Spine(SpineStep),
    /// Assemble a `force` over the value term on the stack.
    Force,
    /// Assemble an application over the computation and value terms.
    Apply,
    /// Assemble a static application over the two value terms.
    StaticApply,
    /// Assemble a bind over the two computation terms.
    Bind,
    /// Assemble a sum elimination over the value term and the two branches.
    Case(usize),
    /// Assemble a split over the value term and the body binding this many
    /// components.
    Split(gandr_core_term::ComponentCount),
    /// Assemble a dependent split over the value term, the motive and the body
    /// binding this many components.
    DependentSplit(gandr_core_term::ComponentCount),
    /// Assemble a constructor, including its normalized nominal classifier.
    Constructor
    {
        /// Constructor position in the declaration.
        tag: gandr_core_term::ConstructorTag,
        /// The field span supplies the operand count.
        fields: crate::FieldSpan,
    },
    /// Assemble a record with the source's exact labels.
    Record(ValueId),
    /// Assemble a recorded run with the source's exact moves and labels.
    Recorded(ValueId),
    /// Assemble a nominal type with the source's declaration identity.
    DataType(ValueTypeId),
    /// Assemble a codata type with the source's declaration identity.
    CodataType(CompTypeId),
    /// Assemble a record type with the source's exact labels.
    RecordType(ValueTypeId),
    /// Assemble a session type with the source's protocol and state over as
    /// many types on the stack as the source has payloads.
    SessionType(ValueTypeId),
    /// Assemble a case with a normalized motive and ambient branch functions.
    DataCase(ComputationId),
    /// Assemble a projection with the projector's exact label or component.
    Projection(crate::domain::Projector),
    /// Read back a value type a quote carries, in a frame.
    QuotedValueType
    {
        /// The core value type.
        quoted: ValueTypeId,
        /// The environment its codes read.
        frame: Frame,
        /// The binders open where it stands.
        binders: OpenBinders,
    },
    /// Read back a computation type a quote carries, in a frame.
    QuotedCompType
    {
        /// The core computation type.
        quoted: CompTypeId,
        /// The environment its codes read.
        frame: Frame,
        /// The binders open where it stands.
        binders: OpenBinders,
    },
    /// Evaluate a decode's code in a frame, then read the value back.
    QuotedCode
    {
        /// The core code.
        code: ValueId,
        /// The environment it reads.
        frame: Frame,
        /// The binders open where it stands.
        binders: OpenBinders,
    },
    /// Assemble a value-type quote from the type on the stack.
    Quote,
    /// Assemble a computation-type quote from the type on the stack.
    QuoteComputation,
    /// Assemble a product type from as many types on the stack as the source
    /// has components.
    ProductType(ValueTypeId),
    /// Assemble a sum type from as many types on the stack as the source has
    /// summands.
    SumType(ValueTypeId),
    /// Assemble a native List type from its element type.
    ListType,
    /// Assemble the type on the stack refined at the held stage.
    StagedType(gandr_kernel_term::Stage),
    /// Assemble the type on the stack kept in the held region.
    KeptType(gandr_core_term::effect::capability::Region),
    /// Assemble a handle type at the held world from the type on the stack.
    LocatedType(gandr_core_term::world::World),
    /// Assemble a thunk type from the computation type on the stack.
    ThunkType,
    /// Assemble a stack type from its input and output computation types.
    StackType,
    /// Assemble a lazy product from as many computation types on the stack as
    /// the source has components.
    WithType(CompTypeId),
    /// Assemble a type lift over the level the domain holds.
    LiftType
    {
        /// The held level.
        target: LiftTarget,
    },
    /// Assemble a value decode over the code on the value stack.
    Element
    {
        /// The held level.
        target: LiftTarget,
    },
    /// Assemble a computation decode over the code on the value stack.
    CompElement
    {
        /// The held level.
        target: LiftTarget,
    },
    /// Assemble the result and operation types of the source returner's row.
    Returner
    {
        /// The source classifier whose inline effect row is being rebuilt.
        source: CompTypeId,
    },
    /// Assemble the operation types of the source capability's authority.
    CapabilityType
    {
        /// The source classifier whose authority is being rebuilt.
        source: ValueTypeId,
    },
    /// Assemble an arrow from the two types on the stacks.
    Arrow,
    /// Assemble a dependent arrow from the two types on the stacks.
    Pi,
    /// Assemble a static Pi from the two value types on the stack.
    StaticPi,
    /// Assemble a dependent pair from the two value types on the stack.
    SigmaType,
    /// Read back the hole or the mark a neutral stands on.
    Suspended
    {
        /// The hole or the mark, closed over its environment.
        closure: Suspended,
        /// Which of the two it is.
        kind: SuspendedKind,
        /// The binders open where it stands.
        binders: OpenBinders,
    },
    /// Substitute the read-back environment entries on the value stack into a
    /// mark's body or a hole's filling.
    Substitute
    {
        /// The mark's body or the filling.
        body: TermId,
        /// How many entries the stack holds for it, innermost index first
        /// from the bottom.
        count: EnvironmentDepth,
    },
}

/// Which suspended head a [`Task::Suspended`] reads.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum SuspendedKind
{
    /// A hole: read back as itself, or as its filling when the run writes it.
    Hole(HoleId),
    /// A mark: read back through its environment.
    Mark,
}

/// The hole a readback writes as it reads, if any.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Writing
{
    /// Every hole reads back as itself.
    Nothing,
    /// Every hole of the name, in the filling's family, reads back as the
    /// filling read through the hole's environment.
    Fill
    {
        /// The hole written.
        hole: HoleId,
        /// What it is written with, in the context the hole stands in.
        filling: TermId,
    },
}

/// An environment a quoted type is read in, by its position in the machine's
/// frame table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Frame(usize);

/// The running machine: the task stack, the result stacks, the frames quoted
/// types are read in, and the run's parameters.
struct Machine<'run>
{
    /// Work still to do, most recent last.
    tasks: Vec<Task>,
    /// Core value results, most recent last.
    values: Vec<ValueId>,
    /// Core computation results, most recent last.
    comps: Vec<ComputationId>,
    /// Core value-type results of a quoted type, most recent last.
    value_types: Vec<ValueTypeId>,
    /// Core computation-type results of a quoted type, most recent last.
    comp_types: Vec<CompTypeId>,
    /// The environments quoted types are read in: a quote's own, and one more
    /// per dependent arrow its type opens.
    frames: Vec<Environment>,
    /// What may be unfolded, and where from, for the evaluations this readback
    /// drives.
    definitions: Definitions<'run>,
    /// Which faces this run spends.
    mode: ReadbackMode,
    /// Steps left, shared with every evaluation this run drives.
    fuel: Fuel,
    /// The hole this run writes as it reads, if any.
    writing: Writing,
}

impl<'run> Machine<'run>
{
    /// Start a machine holding no work.
    ///
    /// # Specification
    /// - requires: nothing; `fuel` may be zero, which refuses at the first
    ///   step, and `mode` selects which faces the run may spend.
    /// - ensures: a machine holding no task, no result and no frame, carrying
    ///   exactly the definitions, mode, and budget offered.
    /// - provides: the entry state every readback run starts from, with the
    ///   budget shared with the evaluations the run drives rather than refilled
    ///   per evaluation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and sufficient budgets separate fuel
    ///   preservation; retained and rebuilt faces separate modes; unfolding a
    ///   lowered body requires the offered definitions. A nonempty initial
    ///   stack changes the assembled term.
    /// - witness: `readback::tests::a_readback_declines_on_fuel_rather_than_running_on`
    /// - witness: `readback::tests::the_unfolding_mode_rebuilds_a_kept_face`
    /// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
    #[spec(
        ensures: |ret| ret.tasks.is_empty() && ret.values.is_empty() && ret.comps.is_empty()
            && ret.value_types.is_empty() && ret.comp_types.is_empty() && ret.frames.is_empty()
            && ret.mode == mode && ret.fuel == fuel && ret.writing == Writing::Nothing
            && core::ptr::eq(core::ptr::from_ref(ret.definitions.bodies()), core::ptr::from_ref(definitions.bodies())),
    )]
    fn new(
        definitions: Definitions<'run>,
        mode: ReadbackMode,
        fuel: Fuel,
    ) -> Self
    {
        Self {
            tasks: Vec::new(),
            values: Vec::new(),
            comps: Vec::new(),
            value_types: Vec::new(),
            comp_types: Vec::new(),
            frames: Vec::new(),
            definitions,
            mode,
            fuel,
            writing: Writing::Nothing,
        }
    }

    /// Hold an environment a quoted type is read in, and name it.
    ///
    /// # Specification
    /// - requires: the environment belongs to this readback's domain.
    /// - ensures: a fresh frame names the offered environment; older slots stay
    ///   valid.
    /// - provides: ownership of the capture while its quoted type is traversed.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ambient lambda capture and an additional
    ///   dependent-arrow binder are read at different indices. Reusing the
    ///   ambient frame or losing its outer binding changes the reconstructed
    ///   codomain.
    /// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
    /// - witness: `readback::tests::a_quoted_dependent_arrow_reads_its_binder_as_an_index`
    #[spec(
        captures: [entry_len = self.frames.len(),
            intuitionistic = environment.depth(Zone::Intuitionistic), linear = environment.depth(Zone::Linear),
            intuitionistic_top = environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            linear_top = environment.lookup(Zone::Linear, DeBruijnIndex::from(0_u32))],
        ensures: |ret| ret.0 == entry_len && self.frames.len() == entry_len.saturating_add(1_usize)
            && self.frames.get(ret.0).is_some_and(|held| held.depth(Zone::Intuitionistic) == intuitionistic
                && held.depth(Zone::Linear) == linear
                && held.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == intuitionistic_top
                && held.lookup(Zone::Linear, DeBruijnIndex::from(0_u32)) == linear_top),
    )]
    fn hold_frame(
        &mut self,
        environment: Environment,
    ) -> Frame
    {
        self.frames.push(environment);
        Frame(self.frames.len().saturating_sub(1_usize))
    }

    /// The environment a frame names, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the environment `frame` names.
    /// - provides: the checked read of the frame table.
    /// - fails: [`ReadbackFault::MachineInvariant`] when `frame` names no
    ///   frame, which only a task this machine did not push could hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the frame does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quote reads its captured lambda variable, and a
    ///   dependent codomain additionally reads its newly opened binder.
    ///   Selecting another held frame changes an index. A nonexistent slot is
    ///   excluded by the append-only frame producer; its checked refusal
    ///   remains explicit.
    /// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
    /// - witness: `readback::tests::a_quoted_dependent_arrow_reads_its_binder_as_an_index`
    #[spec(
        ensures: |ret| self.frames.get(frame.0).map_or_else(
            || ret == Err(ReadbackFault::MachineInvariant),
            |held| ret.as_ref().is_ok_and(|returned| core::ptr::eq(core::ptr::from_ref(*returned), core::ptr::from_ref(held)))),
    )]
    fn frame(
        &self,
        frame: Frame,
    ) -> Result<&Environment, ReadbackFault>
    {
        self.frames
            .get(frame.0)
            .ok_or(ReadbackFault::MachineInvariant)
    }

    /// Pop one value-type result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent value type, removed from the stack.
    /// - provides: the one read of the value-type result stack.
    /// - fails: [`ReadbackFault::MachineInvariant`] when the stack is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the stack was empty.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — differently shaped operands appear in their declared
    ///   domain and codomain positions. Popping an older result or failing to
    ///   remove the newest one changes the reconstructed type. Empty stacks are
    ///   excluded by the frame producer, not assumed infallible.
    /// - witness: `readback::tests::a_quoted_static_pi_reads_back_former_by_former`
    #[spec(
        captures: [entry_len = self.value_types.len(), entry_last = self.value_types.last().copied()],
        ensures: |ret| ret == entry_last.ok_or(ReadbackFault::MachineInvariant)
            && self.value_types.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_value_type(&mut self) -> Result<ValueTypeId, ReadbackFault>
    {
        self.value_types
            .pop()
            .ok_or(ReadbackFault::MachineInvariant)
    }

    /// Pop one computation-type result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent computation type, removed from the stack.
    /// - provides: the one read of the computation-type result stack.
    /// - fails: [`ReadbackFault::MachineInvariant`] when the stack is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the stack was empty.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — differently shaped operands appear in their declared
    ///   domain and codomain positions. Popping an older result or failing to
    ///   remove the newest one changes the reconstructed type. Empty stacks are
    ///   excluded by the frame producer, not assumed infallible.
    /// - witness: `readback::tests::a_quoted_dependent_arrow_reads_its_binder_as_an_index`
    #[spec(
        captures: [entry_len = self.comp_types.len(), entry_last = self.comp_types.last().copied()],
        ensures: |ret| ret == entry_last.ok_or(ReadbackFault::MachineInvariant)
            && self.comp_types.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_comp_type(&mut self) -> Result<CompTypeId, ReadbackFault>
    {
        self.comp_types.pop().ok_or(ReadbackFault::MachineInvariant)
    }

    /// Pop one value result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent value term, removed from the stack.
    /// - provides: the one read of the value result stack.
    /// - fails: [`ReadbackFault::MachineInvariant`] when the stack is empty,
    ///   which a frame reaches only by claiming an operand its own tasks never
    ///   pushed.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the value result stack was
    ///   empty.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on the reachable arm, an exact exclusion on the other.
    ///   The decision surface is the two-state stack. The non-empty state is
    ///   separated pointwise by every value-assembling frame in the suite, each
    ///   asserting the exact node the popped operand went into and in which
    ///   position, so a pop that answered the wrong entry is a wrong term
    ///   rather than a missing assertion. The empty state is **excluded rather
    ///   than witnessed**: a frame reaches it only by claiming an operand its
    ///   own tasks never pushed, and every frame here is pushed by the same arm
    ///   that pushed those tasks, so no input to the public entries reaches it.
    ///   The exclusion is the reason the arm is a returned refusal rather than
    ///   a debug assertion — a future frame that miscounts surfaces as a
    ///   refusal instead of a wrong term.
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    /// - witness: `readback::tests::a_stuck_bind_and_case_read_back_their_branches`
    #[spec(
        captures: [entry_len = self.values.len(), entry_last = self.values.last().copied()],
        ensures: |ret| ret == entry_last.ok_or(ReadbackFault::MachineInvariant)
            && self.values.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_value(&mut self) -> Result<ValueId, ReadbackFault>
    {
        self.values.pop().ok_or(ReadbackFault::MachineInvariant)
    }

    /// Pop one computation result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent computation term, removed from the stack.
    /// - provides: the one read of the computation result stack.
    /// - fails: [`ReadbackFault::MachineInvariant`] when the stack is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the computation result stack was
    ///   empty.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on the reachable arm, an exact exclusion on the other,
    ///   for the reason its positive-side sibling records. The non-empty state
    ///   is separated pointwise by the bind and case frames, whose two popped
    ///   operands are asserted to land in the positions that distinguish them —
    ///   the bound computation against the continuation, the left branch
    ///   against the right — so a pop taking the wrong entry is a wrong term.
    ///   The empty state is excluded: no input to the public entries reaches it
    ///   while the machine's own pushes are the only source of frames.
    /// - witness: `readback::tests::a_stuck_bind_and_case_read_back_their_branches`
    /// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
    #[spec(
        captures: [entry_len = self.comps.len(), entry_last = self.comps.last().copied()],
        ensures: |ret| ret == entry_last.ok_or(ReadbackFault::MachineInvariant)
            && self.comps.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_comp(&mut self) -> Result<ComputationId, ReadbackFault>
    {
        self.comps.pop().ok_or(ReadbackFault::MachineInvariant)
    }
}

/// The source value a readback may answer with instead of rebuilding.
///
/// # Specification
/// - requires: nothing — every mode and every face is admissible input.
/// - ensures: the cached core value exactly when the mode prefers the term face
///   **and** the face names one; nothing under the rebuilding mode, and nothing
///   for a node something reduced inside.
/// - provides: the whole content of "readback chooses a face" on the positive
///   side, in one table rather than at each arm.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the mode-by-face table, separated
///   by all four of its entries: the retaining mode on a kept face and on a
///   lost one, and the rebuilding mode on each of the same two.
/// - witness: `readback::tests::an_unreduced_value_reads_back_as_its_own_source`
/// - witness: `readback::tests::a_reduced_value_is_rebuilt_from_the_domain`
/// - witness: `readback::tests::the_unfolding_mode_rebuilds_a_kept_face`
/// - witness: `readback::tests::the_unfolding_mode_spends_a_body_already_forced`
#[inline]
#[spec(ensures: |ret| match (mode, node.face()) {
    | (ReadbackMode::ZeroUnfold, TermFace::Source(source)) => ret == Some(source),
    | (ReadbackMode::ZeroUnfold, TermFace::Reduced)
    | (ReadbackMode::Unfolding, TermFace::Source(_) | TermFace::Reduced) => ret.is_none(),
})]
fn retained_value(
    mode: ReadbackMode,
    node: DomainValue,
) -> Option<ValueId>
{
    match (mode, node.face()) {
        (ReadbackMode::ZeroUnfold, TermFace::Source(source)) => Some(source),
        (ReadbackMode::ZeroUnfold, TermFace::Reduced) | (ReadbackMode::Unfolding, _) => None,
    }
}

/// The negative side's counterpart of [`retained_value`].
///
/// # Specification
/// - requires: nothing — every mode and every face is admissible input.
/// - ensures: the cached core computation exactly when the mode prefers the
///   term face and the face names one.
/// - provides: the face choice on the negative side.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the mode-by-face table, separated
///   by all four of its entries, observed through the weak head each mode reads
///   back.
/// - witness: `readback::tests::an_unreduced_weak_head_reads_back_as_its_own_source`
/// - witness: `readback::tests::the_unfolding_mode_rebuilds_a_kept_face`
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
#[inline]
#[spec(ensures: |ret| match (mode, node.face()) {
    | (ReadbackMode::ZeroUnfold, CompTermFace::Source(source)) => ret == Some(source),
    | (ReadbackMode::ZeroUnfold, CompTermFace::Reduced)
    | (ReadbackMode::Unfolding, CompTermFace::Source(_) | CompTermFace::Reduced) => ret.is_none(),
})]
fn retained_comp(
    mode: ReadbackMode,
    node: DomainComp,
) -> Option<ComputationId>
{
    match (mode, node.face()) {
        (ReadbackMode::ZeroUnfold, CompTermFace::Source(source)) => Some(source),
        (ReadbackMode::ZeroUnfold, CompTermFace::Reduced) | (ReadbackMode::Unfolding, _) => None,
    }
}

/// Refuse unless the fold of `neutral` stands at `expected`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when the two polarities agree.
/// - provides: the one polarity check the spine fold and its end share, written
///   as a total table so a third polarity added later has to answer here.
/// - fails: [`ReadbackFault::NeutralPolarity`] naming `neutral` when they
///   disagree.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::NeutralPolarity`] — the fold does not stand where the
///   elimination, or the neutral's own position, requires.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the two-by-two table, separated
///   by an agreeing fold, an application stacked at value polarity, and a
///   computation-position neutral whose spine leaves it at value polarity.
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
/// - witness: `readback::tests::a_spine_that_misses_its_polarity_is_refused`
#[inline]
#[spec(ensures: |ret| (ret.is_ok() == (polarity == expected))
    && (ret.is_ok()
        || matches!(ret, Err(ReadbackFault::NeutralPolarity { neutral: at }) if at == neutral)))]
fn expect_polarity(
    polarity: Polarity,
    expected: Polarity,
    neutral: NeutralId,
) -> Result<(), ReadbackFault>
{
    match (polarity, expected) {
        (Polarity::Value, Polarity::Value) | (Polarity::Computation, Polarity::Computation) => {
            Ok(())
        },
        (Polarity::Value, Polarity::Computation) | (Polarity::Computation, Polarity::Value) => {
            Err(ReadbackFault::NeutralPolarity { neutral })
        },
    }
}

/// Evaluate a closure's body in the environment it captured, extended as
/// `entry` says.
///
/// # Specification
/// - requires: nothing — a dangling closure id is admissible input.
/// - ensures: on success the weak head of the closure's body, with the fuel the
///   evaluation spent taken off the machine's own budget, so the two are one
///   budget rather than two.
/// - provides: the one place a readback drives an evaluation, which is what
///   makes it a normalizer rather than a printer. The clause states that a
///   successful weak head resolves in `domain` and that the machine's budget
///   never grows; which weak head the body has is the evaluation's own
///   postcondition, and the witnesses below carry it.
/// - fails: [`ReadbackFault::Domain`] carrying [`DomainFault::Dangling`] when
///   the closure id names no node, and [`ReadbackFault::Eval`] carrying the
///   evaluation's own refusal otherwise — including the core-arena miss, which
///   reaches a readback by no other path.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::Domain`] — the closure id names no node.
/// - [`ReadbackFault::Eval`] — the evaluation refused.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the closure lookup, the
///   extension arm and the fuel handover, separated by entering a thunk's bare
///   closure, opening a lambda's closure under a binder the body reads, and a
///   closure over a body that resolves in no core arena.
/// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
/// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
/// - witness: `readback::tests::an_opened_closure_reports_the_evaluations_own_fault`
#[spec(
    captures: entry_fuel = u32::from(machine.fuel),
    ensures: |ret| ret.is_err()
        || (ret.as_ref().is_ok_and(|whnf| domain.computation(*whnf).is_some())
            && u32::from(machine.fuel) <= entry_fuel),
)]
fn enter(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    closure: CompClosureId,
    entry: Entry,
) -> Result<DomainCompId, ReadbackFault>
{
    let (body, mut environment) = {
        let Some(held) = domain.comp_closure(closure)
        else {
            return Err(ReadbackFault::Domain(DomainFault::Dangling));
        };
        (held.body(), held.environment().clone())
    };
    match entry {
        Entry::Bare => {},
        Entry::Under { zone, bound } => environment.extend(zone, bound),
    }
    let evaluated = crate::eval::eval_body_within(
        core,
        domain,
        machine.definitions,
        machine.fuel,
        body,
        environment,
    );
    let (whnf, remaining) = evaluated.map_err(ReadbackFault::Eval)?;
    machine.fuel = remaining;
    Ok(whnf)
}

/// Open a closure under one fresh binder of `zone`.
///
/// # Specification
/// - requires: nothing — a dangling closure id and a zone at the ceiling are
///   both admissible input.
/// - ensures: on success the weak head of the body read with a fresh variable
///   neutral bound in `zone`, paired with the binders that variable is in scope
///   under. The fresh variable takes the level `binders` has open in `zone`, so
///   its identity depends on the number of binders alone.
/// - provides: the binder-entering step every rule that goes under one shares,
///   which is the step that mints the levels the index conversion inverts. The
///   clause states the reported binders against [`OpenBinders::opened`], the
///   ceiling refusal, and that the produced head resolves in `domain`; that the
///   fresh variable is bound in `zone` at the level `binders` has open there is
///   a judgement over the produced graph, and the witnesses below carry it.
/// - fails: [`ReadbackFault::BinderCeiling`] at the zone's level ceiling,
///   [`ReadbackFault::Domain`] when the closure or the fresh neutral does not
///   resolve, and [`ReadbackFault::Eval`] when the body's evaluation refuses.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::BinderCeiling`] — one more binder would pass the level
///   ceiling.
/// - [`ReadbackFault::Domain`] — the closure id names no node.
/// - [`ReadbackFault::Eval`] — evaluating the body refused.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the ceiling guard, the fresh
///   level, and the extension, separated by opening a binder whose body reads
///   it, opening a second binder so the two levels differ, and a zone held at
///   the ceiling.
/// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
/// - witness: `readback::tests::nested_binders_read_back_as_the_indices_that_name_them`
/// - witness: `readback::tests::the_binder_ceiling_is_refused_rather_than_reused`
// economy: each opened binder clones the environment the closure captured, so
// a body of n nested binders costs O(n^2) copying and retains it for the run.
// It is the same shape and the same ceiling the beta rule records in `eval.rs`,
// reached here once per binder a readback goes under. Upgrade path: the same
// one — hold the environment as a persistent chain of frames, each naming its
// parent, its zone and its binding, so an extension is one push and only a
// closure capture materializes a flat environment. That trades O(1) lookup for
// a walk, so it is worth taking when a measurement says which dominates.
#[spec(ensures: |ret| [
    ret.is_err() || ret.as_ref().is_ok_and(|pair| Some(pair.1) == binders.opened(zone)),
    binders.opened(zone).is_some()
        || matches!(ret, Err(ReadbackFault::BinderCeiling { zone: at }) if at == zone),
    ret.is_err() || ret.as_ref().is_ok_and(|pair| domain.computation(pair.0).is_some()),
])]
fn open(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    closure: CompClosureId,
    binders: OpenBinders,
    zone: Zone,
) -> Result<(DomainCompId, OpenBinders), ReadbackFault>
{
    let Some(deeper) = binders.opened(zone)
    else {
        return Err(ReadbackFault::BinderCeiling { zone });
    };
    let level = binders.fresh(zone);
    let minted = domain.neutral_node(
        NeutralHead::Variable { zone, level },
        Vec::new(),
        Unfolding::Rigid,
    );
    let neutral = minted.map_err(ReadbackFault::Domain)?;
    let stood = domain.value_neutral(neutral, TermFace::Reduced);
    let bound = stood.map_err(ReadbackFault::Domain)?;
    let whnf = enter(core, domain, machine, closure, Entry::Under { zone, bound })?;
    Ok((whnf, deeper))
}

/// Open a closure under `count` fresh intuitionistic binders, outermost first:
/// a List cell branch under head then folded-result binders, or a split body
/// under one binder per component.
///
/// # Specification
/// - requires: the closure and its captured environment resolve.
/// - ensures: the body is evaluated with `count` distinct fresh variables and
///   returned at the binder depth extended `count` times.
/// - fails: existing domain, binder-ceiling and evaluation faults.
/// - panics: none.
///
/// # Errors
/// Returns domain, binder-ceiling or evaluation faults unchanged.
///
/// # Adequacy
/// - hypothesis: L3 — a neutral fold retaining both binders and an outer
///   capture distinguishes the opening order and the ambient depth.
/// - witness: `readback::tests::native_lists_and_folds_read_back_without_sum_encoding`
/// - witness: `readback::tests::a_stuck_split_reads_back_with_its_components_bound`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|pair|
    (0_usize .. usize::from(count)).try_fold(binders, |at, _| at.opened(Zone::Intuitionistic)) == Some(pair.1)
        && domain.computation(pair.0).is_some()) || ret.is_err())]
fn open_many(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    closure: CompClosureId,
    binders: OpenBinders,
    count: gandr_core_term::ComponentCount,
) -> Result<(DomainCompId, OpenBinders), ReadbackFault>
{
    let held = domain
        .comp_closure(closure)
        .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
    let body = held.body();
    let mut environment = held.environment().clone();
    let mut deeper = binders;
    let zone = Zone::Intuitionistic;
    for _ in 0_usize .. usize::from(count) {
        let level = deeper.fresh(zone);
        deeper = deeper
            .opened(zone)
            .ok_or(ReadbackFault::BinderCeiling { zone })?;
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable { zone, level },
                Vec::new(),
                Unfolding::Rigid,
            )
            .map_err(ReadbackFault::Domain)?;
        let bound = domain
            .value_neutral(neutral, TermFace::Reduced)
            .map_err(ReadbackFault::Domain)?;
        environment.extend(zone, bound);
    }
    let (whnf, remaining) = crate::eval::eval_body_within(
        core,
        domain,
        machine.definitions,
        machine.fuel,
        body,
        environment,
    )
    .map_err(ReadbackFault::Eval)?;
    machine.fuel = remaining;
    Ok((whnf, deeper))
}

/// Open a static lambda under one fresh intuitionistic binder.
///
/// # Specification
/// - requires: nothing — a dangling closure id, a closure over anything but a
///   static lambda, and the intuitionistic zone at its ceiling are all
///   admissible input.
/// - ensures: on success the domain value of the lambda's body read with a
///   fresh variable neutral bound in the intuitionistic zone, paired with the
///   binders that variable is in scope under.
/// - provides: the binder-entering step of a static lambda's readback, the
///   value twin of [`open`]: the lambda's closure holds the lambda itself, so
///   the body evaluated is the lambda's own body.
/// - fails: [`ReadbackFault::BinderCeiling`] at the zone's level ceiling,
///   [`ReadbackFault::Domain`] when the closure or the fresh neutral does not
///   resolve, [`ReadbackFault::MachineInvariant`] when the closure holds no
///   static lambda, and [`ReadbackFault::Eval`] when the body's evaluation
///   refuses.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the ceiling guard and the
///   extension, separated by a static lambda whose body reads its binder.
/// - witness: `readback::tests::a_static_lambda_reads_back_with_its_binder_as_an_index`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        Some(pair.1) == binders.opened(Zone::Intuitionistic) && domain.value(pair.0).is_some()
    }))]
fn open_static(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    lambda: ValueClosureId,
    binders: OpenBinders,
) -> Result<(DomainValueId, OpenBinders), ReadbackFault>
{
    let zone = Zone::Intuitionistic;
    let Some(deeper) = binders.opened(zone)
    else {
        return Err(ReadbackFault::BinderCeiling { zone });
    };
    let (term, mut environment) = {
        let Some(held) = domain.value_closure(lambda)
        else {
            return Err(ReadbackFault::Domain(DomainFault::Dangling));
        };
        let crate::ValueBody::Source(body) = held.body()
        else {
            return Err(ReadbackFault::MachineInvariant);
        };
        let Some(&Value::StaticLambda(term)) = core.value(body)
        else {
            return Err(ReadbackFault::MachineInvariant);
        };
        (term, held.environment().clone())
    };
    let level = binders.fresh(zone);
    let minted = domain.neutral_node(
        NeutralHead::Variable { zone, level },
        Vec::new(),
        Unfolding::Rigid,
    );
    let neutral = minted.map_err(ReadbackFault::Domain)?;
    let stood = domain.value_neutral(neutral, TermFace::Reduced);
    let bound = stood.map_err(ReadbackFault::Domain)?;
    environment.extend(zone, bound);
    let evaluated = eval_value_within(
        core,
        domain,
        machine.definitions,
        machine.fuel,
        term,
        environment,
    );
    let (body, remaining) = evaluated.map_err(ReadbackFault::Eval)?;
    machine.fuel = remaining;
    Ok((body, deeper))
}

/// The core value a neutral head reads back as.
///
/// # Specification
/// - requires: nothing — a level outside the open binders is admissible input.
/// - ensures: a variable head becomes the index its level counts at here; a
///   declaration head and a module head both become a reference to the
///   admission position they name, because the core value vocabulary has one
///   reference former. That collapse loses nothing: one admission position
///   admits one declaration, so a module form and a declaration reference at
///   the same position are not both well formed.
/// - provides: the head half of reading a neutral back, and the only site the
///   level-to-index conversion is reached from.
/// - fails: [`ReadbackFault::LevelOutOfScope`] naming the zone and the level
///   when the level counts at or past the binders open in its zone, and
///   [`ReadbackFault::MachineInvariant`] for a hole or a mark head, which is
///   read through its closure by [`step_suspended`] and never reaches here.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::LevelOutOfScope`] — the level names no open binder.
/// - [`ReadbackFault::MachineInvariant`] — the head is a hole or a mark.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-arm head match plus the
///   conversion guard, separated by a variable at the innermost and at the
///   outermost of two open binders, a variable with nothing open, a declaration
///   head, and a module head.
/// - witness: `readback::tests::nested_binders_read_back_as_the_indices_that_name_them`
/// - witness: `readback::tests::a_level_outside_the_open_binders_is_refused`
/// - witness: `readback::tests::a_module_head_and_a_declaration_head_read_back_alike`
#[spec(ensures: |ret| match head {
    | NeutralHead::Variable { zone, level } => match binders.index(zone, level) {
        | Some(index) => {
            ret.as_ref().is_ok_and(|term| {
                core.value(*term).is_some_and(|node| {
                    matches!(*node, gandr_core_term::Value::Variable { zone: at, index: counted }
                        if at == zone && counted == index)
                })
            })
        },
        | None => {
            matches!(ret, Err(ReadbackFault::LevelOutOfScope { zone: at, level: named })
                if at == zone && named == level)
        },
    },
    | NeutralHead::Constant(constant) | NeutralHead::Module(constant) => {
        ret.as_ref().is_ok_and(|term| {
            core.value(*term).is_some_and(|node| {
                matches!(*node, gandr_core_term::Value::Constant(at) if at == constant)
            })
        })
    },
    | NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_) => ret == Err(ReadbackFault::MachineInvariant),
})]
fn head_term(
    core: &mut CoreArena,
    head: NeutralHead,
    binders: OpenBinders,
) -> Result<ValueId, ReadbackFault>
{
    match head {
        NeutralHead::Variable { zone, level } => {
            let Some(index) = binders.index(zone, level)
            else {
                return Err(ReadbackFault::LevelOutOfScope { zone, level });
            };
            Ok(core.value_variable(zone, index))
        },
        NeutralHead::Constant(constant) | NeutralHead::Module(constant) => {
            Ok(core.value_constant(constant))
        },
        NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_) => {
            Err(ReadbackFault::MachineInvariant)
        },
    }
}

/// Read a domain value back into the core arena, under no open binder.
///
/// # Specification
/// - requires: `value` resolves in `domain`; every [`TermFace::Source`] the
///   readback reaches names a **closed** core value, which is what evaluating
///   well-scoped terms produces and what makes splicing a source id under an
///   open binder denote what it always denoted.
/// - ensures: on success a core value the domain node denotes. Under
///   [`ReadbackMode::ZeroUnfold`] an unreduced node is answered by the very id
///   it was evaluated from, no core node is minted for it, and no unfolding
///   face is forced; under [`ReadbackMode::Unfolding`] every node is rebuilt,
///   every unforced body the run holds a lowering for is forced and spent, and
///   every binder comes out as an index counted from a level, so two results
///   are comparable by structure alone.
/// - provides: the value half of readback, which is the consumer the domain's
///   two faces were populated for. The clause states that a successful result
///   resolves in `core`; which core value it is, and the per-mode reading
///   above, are judgements over the whole produced term rather than over one
///   call's exit state, and the witnesses below carry them.
/// - fails: every variant of [`ReadbackFault`]; a refusal leaves whatever it
///   minted in the core arena, which a caller discards by truncating to a
///   watermark taken before the call.
/// - panics: none — every stack read is checked and every arithmetic step is
///   checked or saturating.
/// - intension: the machine performs one task per step and spends one unit of
///   fuel per step, and hands the remainder to each evaluation it drives, so
///   the budget bounds the readback and the evaluations under it together
///   rather than each separately.
///
/// # Errors
/// Every variant of [`ReadbackFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L2 against pinned terms for the walk as a whole — a value
///   evaluated and read back is compared structurally against an expected term
///   written out by hand, so the oracle is external to this machine rather than
///   another run of it — over an L3 residue: the face choice, the seven value
///   arms, the neutral's unfolding table and the refusals, separated by an
///   unreduced value answered by its own id with the core arena asserted
///   unchanged, a reduced value rebuilt and asserted by shape, each leaf and
///   composite arm, a thunk whose body is entered, a neutral at each of the
///   three unfolding states under both modes, and one triggering input per
///   failure mode with the exact variant and its payload asserted — the
///   [`ReadbackFault::MachineInvariant`] arm excepted, which no input reaches
///   while the machine's own pushes are the only source of tasks. The declared
///   `- intension:` projection is the budget, separated by two readbacks over
///   the same suspended body differing only in how many evaluations they drive:
///   the gap between their least sufficient budgets is a whole evaluation under
///   one shared budget and a handful of tasks under a budget handed fresh to
///   each. The heap-resident depth is separated by a chain no host stack of the
///   size the witness runs in could hold.
/// - witness: `readback::tests::an_unreduced_value_reads_back_as_its_own_source`
/// - witness: `readback::tests::a_reduced_value_is_rebuilt_from_the_domain`
/// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
/// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
/// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
/// - witness: `readback::tests::the_zero_unfold_mode_leaves_an_unforced_body_unforced`
/// - witness: `readback::tests::the_unfolding_mode_spends_a_body_already_forced`
/// - witness: `readback::tests::the_unfolding_mode_refuses_a_body_no_chain_entry_names`
/// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
/// - witness: `readback::tests::a_level_outside_the_open_binders_is_refused`
/// - witness: `readback::tests::a_value_from_another_domain_arena_is_refused`
/// - witness: `readback::tests::an_opened_closure_reports_the_evaluations_own_fault`
/// - witness: `readback::tests::a_readback_declines_on_fuel_rather_than_running_on`
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
/// - witness: `tests::readback_terms::an_unreduced_term_reads_back_as_the_id_it_was_evaluated_from`
/// - witness: `tests::deep_readback::a_deep_value_reads_back_inside_a_small_stack`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all, fields(fuel = u32::from(fuel), unfolding = matches!(mode, ReadbackMode::Unfolding))))]
#[inline]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|term| core.value(*term).is_some()))]
pub fn readback_value(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    mode: ReadbackMode,
    fuel: Fuel,
    value: DomainValueId,
) -> Result<ValueId, ReadbackFault>
{
    read_value_under(
        core,
        domain,
        definitions,
        mode,
        fuel,
        value,
        OpenBinders::none(),
    )
}

/// Read a domain computation back into the core arena, under no open binder.
///
/// # Specification
/// - requires: `comp` resolves in `domain`; the source-face precondition of
///   [`readback_value`].
/// - ensures: on success a core computation the weak head denotes, with the
///   same per-mode reading [`readback_value`] states.
/// - provides: the computation half of readback, which is where the binders a
///   lambda and a stuck bind or case stand under are opened. The clause states
///   that a successful result resolves in `core`; which core computation it is
///   is a judgement over the whole produced term, and the witnesses below carry
///   it.
/// - fails: every variant of [`ReadbackFault`].
/// - panics: none.
/// - intension: one task per step, one unit of fuel per step, shared with the
///   evaluations the readback drives.
///
/// # Errors
/// Every variant of [`ReadbackFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L2 against pinned terms for the walk as a whole — a
///   computation evaluated and read back is compared structurally against an
///   expected term written out by hand, in the two directions that matter: a
///   redex contracted under a binder, and a stuck elimination whose branches
///   normalize under their own binders — over an L3 residue: the three
///   computation arms, the spine fold and its refusals, separated by an
///   unreduced weak head answered by its own id, a lambda opened under a binder
///   its body reads, two nested binders so the levels do not collapse, a stuck
///   spine carrying one of each elimination, a spine that never reaches
///   computation polarity, and a binder opened at the level ceiling — the last
///   two by exact variant. The declared `- intension:` projection is the
///   budget, separated as [`readback_value`] states; the heap-resident depth is
///   separated by a chain of suspensions no host stack of the size the witness
///   runs in could hold.
/// - witness: `readback::tests::an_unreduced_weak_head_reads_back_as_its_own_source`
/// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
/// - witness: `readback::tests::nested_binders_read_back_as_the_indices_that_name_them`
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
/// - witness: `readback::tests::a_stuck_bind_and_case_read_back_their_branches`
/// - witness: `readback::tests::a_spine_that_misses_its_polarity_is_refused`
/// - witness: `readback::tests::the_binder_ceiling_is_refused_rather_than_reused`
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
/// - witness: `tests::readback_terms::a_redex_normalizes_to_the_term_written_out_by_hand`
/// - witness: `tests::readback_terms::a_redex_under_a_binder_normalizes_to_the_term_written_out_by_hand`
/// - witness: `tests::readback_terms::a_case_that_fires_normalizes_to_the_branch_it_took`
/// - witness: `tests::readback_terms::a_stuck_elimination_normalizes_to_the_spine_written_out_by_hand`
/// - witness: `tests::deep_readback::a_deep_computation_reads_back_inside_a_small_stack`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all, fields(fuel = u32::from(fuel), unfolding = matches!(mode, ReadbackMode::Unfolding))))]
#[inline]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|term| core.computation(*term).is_some()))]
pub fn readback_computation(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    mode: ReadbackMode,
    fuel: Fuel,
    comp: DomainCompId,
) -> Result<ComputationId, ReadbackFault>
{
    read_comp_under(
        core,
        domain,
        definitions,
        mode,
        fuel,
        comp,
        OpenBinders::none(),
    )
}

/// Read a domain value back with `binders` already open over it.
///
/// # Specification
/// - requires: `binders` counts the binders the value actually stands under, so
///   a variable head's level resolves against the scope it was minted in.
/// - ensures: on success the core value the node denotes in that scope.
/// - provides: the seeded entry the whole-term readback is the empty case of,
///   and the one an out-of-scope level or a zone at the ceiling is reached
///   through. The clause states that a successful result resolves in `core`;
///   which core value it denotes is a judgement over the whole produced term,
///   and the witnesses below carry it.
/// - fails: every variant of [`ReadbackFault`].
/// - panics: none.
///
/// # Errors
/// Every variant of [`ReadbackFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the seeded depth, separated by a
///   variable level resolving under two open binders and the same level read
///   with none open.
/// - witness: `readback::tests::a_level_becomes_the_index_counting_the_other_way`
/// - witness: `readback::tests::a_level_outside_the_open_binders_is_refused`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|term| core.value(*term).is_some()))]
fn read_value_under(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    mode: ReadbackMode,
    fuel: Fuel,
    value: DomainValueId,
    binders: OpenBinders,
) -> Result<ValueId, ReadbackFault>
{
    let mut machine = Machine::new(definitions, mode, fuel);
    machine.tasks.push(Task::Value { value, binders });
    run(core, domain, &mut machine)?;
    machine.pop_value()
}

/// Read a domain computation back with `binders` already open over it.
///
/// # Specification
/// - requires: `binders` counts the binders the weak head actually stands
///   under.
/// - ensures: on success the core computation the weak head denotes in that
///   scope.
/// - provides: the seeded entry the whole-term computation readback is the
///   empty case of. The clause states that a successful result resolves in
///   `core`; which core computation it denotes is a judgement over the whole
///   produced term, and the witnesses below carry it.
/// - fails: every variant of [`ReadbackFault`].
/// - panics: none.
///
/// # Errors
/// Every variant of [`ReadbackFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the seeded depth, separated by a
///   lambda opened at the ceiling and one opened with room left.
/// - witness: `readback::tests::the_binder_ceiling_is_refused_rather_than_reused`
/// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|term| core.computation(*term).is_some()))]
fn read_comp_under(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    mode: ReadbackMode,
    fuel: Fuel,
    comp: DomainCompId,
    binders: OpenBinders,
) -> Result<ComputationId, ReadbackFault>
{
    let mut machine = Machine::new(definitions, mode, fuel);
    machine.tasks.push(Task::Comp { comp, binders });
    run(core, domain, &mut machine)?;
    machine.pop_comp()
}

/// Read a closed result back with every hole of one name written, reporting
/// the budget the run did not spend.
///
/// # Specification
/// - requires: `result` resolves in `domain` and stands under no binder;
///   `filling` is live in `core` and written in the context the holes of the
///   name stand in; the source-face precondition of [`readback_value`].
/// - ensures: on success the term [`ReadbackMode::ZeroUnfold`] reads `result`
///   back as, except that every hole-headed neutral of the name whose family is
///   the filling's reads back as the filling, its free indices replaced by the
///   read-back entries of the hole's environment; paired with the fuel left
///   over. A hole kept inside a retained source face stands: that face was
///   evaluated in no environment, so the caller fills it syntactically.
/// - provides: the substitution half of filling a result: the hole closures
///   written, everything else read back as it stands.
/// - fails: every variant of [`ReadbackFault`].
/// - panics: none.
///
/// # Errors
/// Every variant of [`ReadbackFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — a hole whose environment binds the variable its filling
///   reads, a hole of another name, and a hole in a computation position
///   separate the substituted filling, the name check and the family.
/// - witness: `live::tests::filling_resumes_where_the_hole_stood`
/// - witness: `live::tests::a_fill_leaves_other_holes_standing`
/// - witness: `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(term, remaining)| u32::from(remaining) <= u32::from(fuel) && match (term, result) {
    (TermId::Value(id), Glued::Value(_)) => core.value(id).is_some(),
    (TermId::Computation(id), Glued::Computation(_)) => core.computation(id).is_some(),
    (TermId::Value(_), Glued::Computation(_)) | (TermId::Computation(_), Glued::Value(_)) => false,
}))]
pub fn read_written(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    result: Glued,
    hole: HoleId,
    filling: TermId,
) -> Result<(TermId, Fuel), ReadbackFault>
{
    let mut machine = Machine::new(definitions, ReadbackMode::ZeroUnfold, fuel);
    machine.writing = Writing::Fill { hole, filling };
    let binders = OpenBinders::none();
    machine.tasks.push(match result {
        Glued::Value(value) => Task::Value { value, binders },
        Glued::Computation(comp) => Task::Comp { comp, binders },
    });
    run(core, domain, &mut machine)?;
    let read = match result {
        Glued::Value(_) => TermId::Value(machine.pop_value()?),
        Glued::Computation(_) => TermId::Computation(machine.pop_comp()?),
    };
    Ok((read, machine.fuel))
}

/// Drive the machine until its task stack empties or its fuel runs out.
///
/// # Specification
/// - requires: the machine's task stack holds the run's initial task.
/// - ensures: on success the task stack is empty and the result stacks hold
///   exactly what the run produced.
/// - provides: the one loop; every rule is an arm of it, so there is no call
///   cycle for the recursion gate to find and no host frame per term node. The
///   clauses state a non-empty task stack at entry and an empty one on success;
///   that the stack held exactly the run's initial task, and that the result
///   stacks hold exactly what the run produced, are statements about the run's
///   history rather than about either state the attribute observes.
/// - fails: every variant of [`ReadbackFault`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the fuel guard against the
///   task-stack guard, separated by a run that completes with fuel to spare, a
///   run that exhausts it on this stack, and a run that exhausts it inside an
///   evaluation this loop drove, the last two asserted by variant. That the
///   loop is a loop rather than a call cycle is separated by chains of both
///   polarities read back inside a host stack far too small to hold a frame per
///   node.
/// - witness: `readback::tests::a_readback_declines_on_fuel_rather_than_running_on`
/// - witness: `readback::tests::a_reduced_value_is_rebuilt_from_the_domain`
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
/// - witness: `tests::deep_readback::a_deep_value_reads_back_inside_a_small_stack`
/// - witness: `tests::deep_readback::a_deep_computation_reads_back_inside_a_small_stack`
#[spec(
    requires: !machine.tasks.is_empty(),
    ensures: |ret| ret.is_err() || machine.tasks.is_empty(),
)]
fn run(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<(), ReadbackFault>
{
    while let Some(task) = machine.tasks.pop() {
        let Some(remaining) = u32::from(machine.fuel).checked_sub(1_u32)
        else {
            #[cfg(feature = "tracing")]
            tracing::warn!("readback fuel exhausted");
            return Err(ReadbackFault::OutOfFuel);
        };
        machine.fuel = Fuel::from(remaining);
        step(core, domain, machine, task)?;
    }
    Ok(())
}

/// Perform one task.
///
/// # Specification
/// - requires: `task` was popped from `machine`'s own stack, so its operands
///   are on the result stacks.
/// - ensures: the task's result is pushed on the stack of its own polarity, or
///   further tasks are pushed that will produce it.
/// - provides: the machine's whole transition relation, one arm per domain
///   former plus one per assembly frame. Copy-sized entry counts express each
///   frame's typed operand consumption and result production; the resulting id
///   must resolve in its core family. Structural witnesses separate former
///   choice and operand order. Nested evaluation shares the remaining fuel.
/// - fails: every variant of [`ReadbackFault`] except
///   [`ReadbackFault::OutOfFuel`], which belongs to the driver rather than to a
///   step.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the node arms and the frame
///   arms, separated by one case per arm across the suite, with each assembly
///   frame's operand order separated by a case whose two operands differ.
/// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
/// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
/// - witness: `readback::tests::a_stuck_bind_and_case_read_back_their_branches`
/// - witness: `readback::tests::quoted_formers_preserve_distinct_children_and_targets`
#[spec(
    captures: [entry_fuel = u32::from(machine.fuel), entry_tasks = machine.tasks.len(),
        entry_values = machine.values.len(), entry_comps = machine.comps.len(), entry_value_types = machine.value_types.len(), entry_comp_types = machine.comp_types.len()],
    ensures: |ret| u32::from(machine.fuel) <= entry_fuel && ret != Err(ReadbackFault::OutOfFuel) && (ret.is_err() || match task {
        | Task::Tuple(count) => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(count).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|id| core.value(*id).and_then(Value::components).is_some_and(|held| held.len() == count))
            && entry_comps == machine.comps.len()
            && entry_value_types == machine.value_types.len()
            && entry_comp_types == machine.comp_types.len(),
        | Task::ListCons | Task::PathProduct | Task::StaticApply | Task::Univalence => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(2_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|id| core.value(*id).is_some())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Flow(_) => machine.tasks.len() == entry_tasks
            && machine.values.len() < entry_values.saturating_add(1_usize)
            && machine.values.last().is_some_and(|id| core.value(*id).is_some())
            && entry_comps == machine.comps.len()
            && entry_value_types == machine.value_types.len()
            && entry_comp_types == machine.comp_types.len(),
        | Task::Inject { .. } | Task::Lift { .. } | Task::StaticLambda | Task::Here => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|id| core.value(*id).is_some())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Thunk => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|id| core.value(*id).is_some())
            && entry_comps.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Lambda | Task::Fixpoint(_) => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(1_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comps.len())
            && machine.comps.last().is_some_and(|id| core.computation(*id).is_some())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Transport | Task::ProductTransport => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(2) == Some(machine.values.len())
            && machine.comps.len() == entry_comps.saturating_add(1)
            && machine.comps.last().is_some_and(|&id| core.computation(id).is_some())
            && machine.value_types.len() == entry_value_types && machine.comp_types.len() == entry_comp_types,
        | Task::PathTransport | Task::OperandTransport | Task::Ride | Task::OperandRide => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(2) == Some(machine.values.len())
            && entry_value_types.checked_sub(1) == Some(machine.value_types.len())
            && machine.comps.len() == entry_comps.saturating_add(1)
            && machine.comps.last().is_some_and(|&id| core.computation(id).is_some())
            && machine.comp_types.len() == entry_comp_types,
        | Task::TelescopeTransport => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(4) == Some(machine.values.len())
            && entry_comp_types.checked_sub(1) == Some(machine.comp_types.len())
            && machine.comps.len() == entry_comps.saturating_add(1)
            && machine.comps.last().is_some_and(|&id| core.computation(id).is_some())
            && machine.value_types.len() == entry_value_types,
        | Task::Returned => machine.tasks.len() == entry_tasks
            && machine.values.len() == entry_values.saturating_add(1)
            && entry_comps.checked_sub(1) == Some(machine.comps.len())
            && machine.values.last().is_some_and(|&id| core.value(id).is_some())
            && machine.value_types.len() == entry_value_types && machine.comp_types.len() == entry_comp_types,
        | Task::PathType | Task::FlowType => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(2) == Some(machine.values.len())
            && machine.value_types.len() == entry_value_types
            && machine.value_types.last().is_some_and(|&id| core.value_type(id).is_some())
            && machine.comps.len() == entry_comps && machine.comp_types.len() == entry_comp_types,
        | Task::RunType | Task::PrefixType | Task::DialogueType => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1) == Some(machine.values.len())
            && machine.value_types.len() == entry_value_types.saturating_add(1)
            && machine.value_types.last().is_some_and(|&id| core.value_type(id).is_some())
            && machine.comps.len() == entry_comps && machine.comp_types.len() == entry_comp_types,
        | Task::Return | Task::Force => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comps.len())
            && machine.comps.last().is_some_and(|id| core.computation(*id).is_some())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Apply => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(1_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comps.len())
            && machine.comps.last().is_some_and(|id| core.computation(*id).is_some())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Bind => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(2_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comps.len())
            && machine.comps.last().is_some_and(|id| core.computation(*id).is_some())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Case(count) => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(count).and_then(|left| left.checked_add(1_usize)) == Some(machine.comps.len())
            && machine.comps.last().is_some_and(|id| core.computation(*id).is_some())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Split(arity) => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1) == Some(machine.values.len())
            && machine.comps.len() == entry_comps
            && machine.comps.last().is_some_and(|&id| matches!(core.computation(id), Some(&Computation::Split { arity: actual, .. }) if actual == arity))
            && machine.value_types.len() == entry_value_types && machine.comp_types.len() == entry_comp_types,
        | Task::DependentSplit(arity) => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1) == Some(machine.values.len())
            && machine.comps.len() == entry_comps
            && machine.comps.last().is_some_and(|&id| matches!(core.computation(id), Some(&Computation::Split { arity: actual, motive: SplitMotive::Scrutinee(_), .. }) if actual == arity))
            && machine.value_types.len() == entry_value_types && entry_comp_types.checked_sub(1) == Some(machine.comp_types.len()),
        | Task::ListFold => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1) == Some(machine.values.len())
            && entry_comps.checked_sub(1) == Some(machine.comps.len())
            && entry_value_types.checked_sub(2) == Some(machine.value_types.len())
            && entry_comp_types == machine.comp_types.len()
            && machine.comps.last().is_some_and(|&id| matches!(core.computation(id), Some(gandr_core_term::Computation::ListFold { .. }))),
        | Task::ListCase => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1) == Some(machine.values.len())
            && entry_comps.checked_sub(1) == Some(machine.comps.len())
            && entry_value_types == machine.value_types.len()
            && entry_comp_types == machine.comp_types.len()
            && machine.comps.last().is_some_and(|&id| matches!(core.computation(id), Some(gandr_core_term::Computation::ListCase { .. }))),
        | Task::Quote => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|id| core.value(*id).is_some())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::QuoteComputation => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|id| core.value(*id).is_some())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::ProductType(source) | Task::SumType(source) => core.value_type(source).is_some_and(|held| matches!(*held, ValueType::Product(ref parts) | ValueType::Sum(ref parts)
            if machine.tasks.len() == entry_tasks
            && machine.values.len() == entry_values && machine.comps.len() == entry_comps
            && entry_value_types.checked_sub(parts.len()).and_then(|left| left.checked_add(1)) == Some(machine.value_types.len())
            && machine.comp_types.len() == entry_comp_types
            && machine.value_types.last().is_some_and(|&id| core.value_type(id).is_some_and(|held| matches!(*held, ValueType::Product(ref result) | ValueType::Sum(ref result) if result.len() == parts.len()))))),
        | Task::StaticPi | Task::SigmaType => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(2_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.value_types.len())
            && machine.value_types.last().is_some_and(|id| core.value_type(*id).is_some())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::StackType => machine.tasks.len() == entry_tasks
            && machine.values.len() == entry_values && machine.comps.len() == entry_comps
            && machine.value_types.len() == entry_value_types.saturating_add(1)
            && entry_comp_types.checked_sub(2) == Some(machine.comp_types.len())
            && machine.value_types.last().is_some_and(|&id| matches!(core.value_type(id), Some(ValueType::Stack { .. }))),
        | Task::WithType(source) => core.comp_type(source).is_some_and(|held| matches!(*held, CompType::With(ref parts)
            if machine.tasks.len() == entry_tasks
            && machine.values.len() == entry_values && machine.comps.len() == entry_comps
            && machine.value_types.len() == entry_value_types
            && entry_comp_types.checked_sub(parts.len()).and_then(|left| left.checked_add(1)) == Some(machine.comp_types.len())
            && machine.comp_types.last().is_some_and(|&id| matches!(core.comp_type(id), Some(&CompType::With(..)))))),
        | Task::ThunkType => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.value_types.len())
            && machine.value_types.last().is_some_and(|id| core.value_type(*id).is_some())
            && entry_comp_types.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::ListType | Task::StagedType(_) | Task::KeptType(_) | Task::LocatedType(_) | Task::LiftType { .. } => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(1_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.value_types.len())
            && machine.value_types.last().is_some_and(|id| core.value_type(*id).is_some())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::Element { .. } => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.value_types.len())
            && machine.value_types.last().is_some_and(|id| core.value_type(*id).is_some())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comp_types.len()),
        | Task::CompElement { .. } => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comp_types.len())
            && machine.comp_types.last().is_some_and(|id| core.comp_type(*id).is_some()),
        | Task::Returner { source } => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && core.comp_type(source).is_some_and(|node| match *node { CompType::Returner { ref effects, .. } => entry_value_types.checked_sub(1_usize.saturating_add(effects.types().count())) == Some(machine.value_types.len()), CompType::Arrow { .. } | CompType::Pi { .. } | CompType::Element { .. } | CompType::Unknown | CompType::With(..) | CompType::Codata { .. } => false })
            && entry_comp_types.checked_sub(0_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comp_types.len())
            && machine.comp_types.last().is_some_and(|id| core.comp_type(*id).is_some()),
        | Task::CapabilityType { source } => machine.tasks.len() == entry_tasks
            && machine.values.len() == entry_values && machine.comps.len() == entry_comps
            && core.value_type(source).is_some_and(|node| match *node { ValueType::Capability { ref authority, .. } => entry_value_types.checked_sub(authority.types().count()).and_then(|left| left.checked_add(1_usize)) == Some(machine.value_types.len()), ValueType::Data { .. } | ValueType::Record(_) | ValueType::PathUniverse(..) | ValueType::Path { .. } | ValueType::Flow { .. } | ValueType::Run(_) | ValueType::Prefix(_) | ValueType::Dialogue(_) | ValueType::Web | ValueType::Base(_) | ValueType::Product(_) | ValueType::Sigma { .. } | ValueType::Sum(_) | ValueType::List(_) | ValueType::Thunk(_) | ValueType::Universe { .. } | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Abstract(_) | ValueType::StaticPi { .. } | ValueType::Unknown | ValueType::Buffer | ValueType::Stack { .. } | ValueType::Session(_) | ValueType::Staged { .. } | ValueType::Kept { .. } | ValueType::World(_) => false })
            && machine.comp_types.len() == entry_comp_types
            && machine.value_types.last().is_some_and(|id| core.value_type(*id).is_some()),
        | Task::Arrow | Task::Pi => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.values.len())
            && entry_comps.checked_sub(0_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.comps.len())
            && entry_value_types.checked_sub(1_usize).and_then(|left| left.checked_add(0_usize)) == Some(machine.value_types.len())
            && entry_comp_types.checked_sub(1_usize).and_then(|left| left.checked_add(1_usize)) == Some(machine.comp_types.len())
            && machine.comp_types.last().is_some_and(|id| core.comp_type(*id).is_some()),
        | Task::Constructor { tag, fields } => domain.fields(fields).is_ok_and(|fields|
            entry_values.checked_sub(fields.len()).and_then(|n| n.checked_add(1)) == Some(machine.values.len()))
            && entry_value_types.checked_sub(1) == Some(machine.value_types.len())
            && machine.values.last().is_some_and(|&id| matches!(core.value(id), Some(Value::Constructor { tag: actual, .. }) if *actual == tag)),
        | Task::Record(source) => matches!(core.value(source), Some(Value::Record(fields))
            if entry_values.checked_sub(fields.len()).and_then(|n| n.checked_add(1)) == Some(machine.values.len())
            && machine.values.last().is_some_and(|&id| matches!(core.value(id), Some(Value::Record(result)) if fields.keys().eq(result.keys())))),
        | Task::Recorded(source) => match (core.value(source), machine.values.last().and_then(|&id| core.value(id))) {
            | (Some(&Value::Recorded(ref moves)), Some(&Value::Recorded(ref result))) =>
                result.len() == moves.len() && result.iter().zip(moves.iter()).all(|(read, written)| read.kind() == written.kind()),
            | (Some(&Value::Dialogue(ref moves)), Some(&Value::Dialogue(ref result))) =>
                result.len() == moves.len() && result.iter().zip(moves.iter()).all(|(read, written)| read.endpoint == written.endpoint && read.movement.kind() == written.movement.kind()),
            | (Some(&Value::Web(ref pieces)), Some(&Value::Web(ref result))) => pieces == result,
            | _ => false,
        },
        | Task::DataType(source) => matches!(core.value_type(source), Some(ValueType::Data { declaration, arguments })
            if entry_values.checked_sub(arguments.len()) == Some(machine.values.len())
            && machine.value_types.len() == entry_value_types.saturating_add(1)
            && machine.value_types.last().is_some_and(|&id| matches!(core.value_type(id), Some(ValueType::Data { declaration: actual, arguments: args }) if actual == declaration && args.len() == arguments.len()))),
        | Task::CodataType(source) => matches!(core.comp_type(source), Some(CompType::Codata { declaration, arguments })
            if entry_values.checked_sub(arguments.len()) == Some(machine.values.len())
            && machine.comp_types.len() == entry_comp_types.saturating_add(1)
            && machine.comp_types.last().is_some_and(|&id| matches!(core.comp_type(id), Some(CompType::Codata { declaration: actual, arguments: args }) if actual == declaration && args.len() == arguments.len()))),
        | Task::RecordType(source) => matches!(core.value_type(source), Some(ValueType::Record(fields))
            if entry_value_types.checked_sub(fields.len()).and_then(|n| n.checked_add(1)) == Some(machine.value_types.len())
            && machine.value_types.last().is_some_and(|&id| matches!(core.value_type(id), Some(ValueType::Record(result)) if fields.keys().eq(result.keys())))),
        | Task::SessionType(source) => matches!(core.value_type(source), Some(ValueType::Session(session))
            if entry_value_types.checked_sub(session.payloads().len()).and_then(|n| n.checked_add(1)) == Some(machine.value_types.len())
            && machine.value_types.last().is_some_and(|&id| matches!(core.value_type(id), Some(ValueType::Session(result))
                if result.protocol() == session.protocol() && result.state() == session.state()))),
        | Task::DataCase(source) => matches!(core.computation(source), Some(Computation::DataCase { branches, .. })
            if entry_values.checked_sub(1) == Some(machine.values.len())
            && entry_comp_types.checked_sub(1) == Some(machine.comp_types.len())
            && entry_comps.checked_sub(branches.len()).and_then(|n| n.checked_add(1)) == Some(machine.comps.len())
            && machine.comps.last().is_some_and(|&id| matches!(core.computation(id), Some(Computation::DataCase { branches: actual, .. }) if actual.len() == branches.len()))),
        | Task::Projection(_) => entry_values.checked_sub(1) == Some(machine.values.len())
            && machine.comps.len() == entry_comps.saturating_add(1)
            && machine.comps.last().is_some_and(|&id| matches!(core.computation(id), Some(Computation::RecordProjection(..) | Computation::TupleProjection(..)))),
        | Task::Value { .. } | Task::Comp { .. } | Task::Spine(_) | Task::QuotedValueType { .. }
        | Task::QuotedCompType { .. } | Task::QuotedCode { .. } | Task::Suspended { .. } => true,
        | Task::Substitute { body, count } => machine.tasks.len() == entry_tasks
            && entry_values.checked_sub(usize::from(count)).is_some_and(|left| match body {
                | TermId::Value(_) => machine.values.len() == left.saturating_add(1_usize)
                    && machine.values.last().is_some_and(|&id| core.value(id).is_some()),
                | TermId::Computation(_) => machine.values.len() == left
                    && machine.comps.len() == entry_comps.saturating_add(1_usize)
                    && machine.comps.last().is_some_and(|&id| core.computation(id).is_some()),
            }),
    }),
)]
fn step(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    task: Task,
) -> Result<(), ReadbackFault>
{
    match task {
        Task::StackType => {
            let output = machine.pop_comp_type()?;
            let input = machine.pop_comp_type()?;
            machine
                .value_types
                .push(core.value_type_stack(input, output));
            Ok(())
        },
        Task::WithType(source) => {
            let Some(&CompType::With(ref parts)) = core.comp_type(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let start = machine
                .comp_types
                .len()
                .checked_sub(parts.len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let read = machine
                .comp_types
                .get(start ..)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let assembled = core.comp_type_with(read);
            machine.comp_types.truncate(start);
            machine.comp_types.push(assembled);
            Ok(())
        },
        Task::ListType => {
            let element = machine.pop_value_type()?;
            machine.value_types.push(core.value_type_list(element));
            Ok(())
        },
        Task::StagedType(stage) => {
            let base = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_staged(base, stage));
            Ok(())
        },
        Task::KeptType(region) => {
            let value = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_kept(value, region));
            Ok(())
        },
        Task::LocatedType(world) => {
            let inner = machine.pop_value_type()?;
            machine.value_types.push(
                core.value_type_world(gandr_core_term::world::WorldType::At { inner, world }),
            );
            Ok(())
        },
        Task::Value { value, binders } => step_value(core, domain, machine, value, binders),
        Task::Comp { comp, binders } => step_comp(core, domain, machine, comp, binders),
        Task::Constructor { tag, fields } => {
            let count = domain.fields(fields).map_err(ReadbackFault::Domain)?.len();
            let start = machine
                .values
                .len()
                .checked_sub(count)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let datatype = machine.pop_value_type()?;
            let fields = machine.values.drain(start ..).collect();
            machine
                .values
                .push(core.value_constructor(datatype, tag, fields));
            Ok(())
        },
        Task::Record(source) => {
            let Some(matched_native_node) = core.value(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let Value::Record(ref fields) = *matched_native_node
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let start = machine
                .values
                .len()
                .checked_sub(fields.len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let fields = fields
                .keys()
                .cloned()
                .zip(machine.values.drain(start ..))
                .collect();
            machine.values.push(core.value_record(fields));
            Ok(())
        },
        Task::Recorded(source) => {
            let Some(written) = core.value(source).cloned()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let carried = crate::eval::recording(&written)
                .ok_or(ReadbackFault::MachineInvariant)?
                .count();
            let start = machine
                .values
                .len()
                .checked_sub(carried)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let mut payloads = machine.values.drain(start ..);
            let mut next = |_written| payloads.next().ok_or(ReadbackFault::MachineInvariant);
            let read = if let Value::Recorded(ref moves) = written {
                let mut read = Vec::with_capacity(moves.len());
                for movement in moves.iter() {
                    read.push(movement.try_map(&mut next)?);
                }
                core.value_recorded(alloc::sync::Arc::from(read))
            }
            else if let Value::Dialogue(ref moves) = written {
                let mut read = Vec::with_capacity(moves.len());
                for turn in moves.iter() {
                    read.push(gandr_core_term::session::DialogueMove {
                        endpoint: turn.endpoint,
                        movement: turn.movement.try_map(&mut next)?,
                    });
                }
                core.value_dialogue(alloc::sync::Arc::from(read))
            }
            else if let Value::Web(ref pieces) = written {
                core.value_web(alloc::sync::Arc::clone(pieces))
            }
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            drop(payloads);
            machine.values.push(read);
            Ok(())
        },
        Task::DataType(source) => {
            let Some(matched_native_node) = core.value_type(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let ValueType::Data {
                ref declaration,
                ref arguments,
            } = *matched_native_node
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let declaration = *declaration;
            let start = machine
                .values
                .len()
                .checked_sub(arguments.len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let arguments = machine.values.drain(start ..).collect();
            machine
                .value_types
                .push(core.value_type_data(declaration, arguments));
            Ok(())
        },
        Task::CodataType(source) => {
            let Some(&CompType::Codata {
                declaration,
                ref arguments,
            }) = core.comp_type(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let start = machine
                .values
                .len()
                .checked_sub(arguments.len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let arguments = machine.values.drain(start ..).collect();
            machine
                .comp_types
                .push(core.comp_type_codata(declaration, arguments));
            Ok(())
        },
        Task::RecordType(source) => {
            let Some(matched_native_node) = core.value_type(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let ValueType::Record(ref fields) = *matched_native_node
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let start = machine
                .value_types
                .len()
                .checked_sub(fields.len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let fields = fields
                .keys()
                .cloned()
                .zip(machine.value_types.drain(start ..))
                .collect();
            machine.value_types.push(core.value_type_record(fields));
            Ok(())
        },
        Task::SessionType(source) => {
            let Some(matched_native_node) = core.value_type(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let ValueType::Session(ref session) = *matched_native_node
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let start = machine
                .value_types
                .len()
                .checked_sub(session.payloads().len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let mut payloads = machine.value_types.drain(start ..);
            let rebuilt = session
                .try_map_payloads(gandr_core_term::session::ChildOrder::Forward, |_| {
                    payloads.next().ok_or(ReadbackFault::MachineInvariant)
                })?;
            drop(payloads);
            machine.value_types.push(core.value_type_session(rebuilt));
            Ok(())
        },
        Task::DataCase(source) => {
            let Some(matched_native_node) = core.computation(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let Computation::DataCase {
                ref branches,
                ref arities,
                equations,
                ..
            } = *matched_native_node
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let arities = arities.clone();
            let start = machine
                .comps
                .len()
                .checked_sub(branches.len())
                .ok_or(ReadbackFault::MachineInvariant)?;
            let motive = machine.pop_comp_type()?;
            let scrutinee = machine.pop_value()?;
            let branches = machine.comps.drain(start ..).collect();
            machine
                .comps
                .push(core.computation_data_case_with_equations(
                    scrutinee,
                    motive,
                    (branches, arities),
                    equations,
                ));
            Ok(())
        },
        Task::Projection(projector) => {
            let projection = match crate::rules::projection_key(core, projector)
                .map_err(|_fault| ReadbackFault::MachineInvariant)?
            {
                crate::rules::ProjectionKey::Label(label) => Ok(label.clone()),
                crate::rules::ProjectionKey::Component(component) => Err(component),
            };
            let projected = machine.pop_value()?;
            let assembled = match projection {
                Ok(label) => core.computation_record_projection(projected, label),
                Err(component) => core.computation_tuple_projection(projected, component),
            };
            machine.comps.push(assembled);
            Ok(())
        },
        Task::PathProduct => {
            let second = machine.pop_value()?;
            let first = machine.pop_value()?;
            machine.values.push(core.value_path_product(first, second));
            Ok(())
        },
        Task::Transport => {
            let value = machine.pop_value()?;
            let path = machine.pop_value()?;
            machine.comps.push(core.computation_transport(path, value));
            Ok(())
        },
        Task::ProductTransport => {
            let path = machine.pop_value()?;
            let value = machine.pop_value()?;
            machine.comps.push(core.computation_transport(path, value));
            Ok(())
        },
        Task::PathTransport => {
            let value = machine.pop_value()?;
            let path = machine.pop_value()?;
            let motive = machine.pop_value_type()?;
            machine
                .comps
                .push(core.computation_path_transport(motive, path, value));
            Ok(())
        },
        Task::OperandTransport => {
            let path = machine.pop_value()?;
            let value = machine.pop_value()?;
            let motive = machine.pop_value_type()?;
            machine
                .comps
                .push(core.computation_path_transport(motive, path, value));
            Ok(())
        },
        Task::Ride => {
            let value = machine.pop_value()?;
            let flow = machine.pop_value()?;
            let motive = machine.pop_value_type()?;
            machine
                .comps
                .push(core.computation_ride(motive, flow, value));
            Ok(())
        },
        Task::OperandRide => {
            let flow = machine.pop_value()?;
            let value = machine.pop_value()?;
            let motive = machine.pop_value_type()?;
            machine
                .comps
                .push(core.computation_ride(motive, flow, value));
            Ok(())
        },
        Task::TelescopeTransport => {
            let value = machine.pop_value()?;
            let over = machine.pop_value()?;
            let start = machine.pop_value()?;
            let path = machine.pop_value()?;
            let motive = machine.pop_comp_type()?;
            machine
                .comps
                .push(core.computation_telescope_transport(motive, path, start, over, value));
            Ok(())
        },
        Task::Here => {
            let point = machine.pop_value()?;
            machine.values.push(core.value_here(point));
            Ok(())
        },
        Task::Flow(former) => {
            let flow = match former {
                crate::domain::FlowFormer::Stay => {
                    let point = machine.pop_value()?;
                    core.value_stay(point)
                },
                crate::domain::FlowFormer::Forward => {
                    let translator = machine.pop_value()?;
                    core.value_forward(translator)
                },
                crate::domain::FlowFormer::Then => {
                    let second = machine.pop_value()?;
                    let first = machine.pop_value()?;
                    core.value_then(first, second)
                },
                crate::domain::FlowFormer::Function => {
                    let codomain = machine.pop_value()?;
                    let domain = machine.pop_value()?;
                    core.value_function_flow(domain, codomain)
                },
                crate::domain::FlowFormer::Product => {
                    let second = machine.pop_value()?;
                    let first = machine.pop_value()?;
                    core.value_flow_product(first, second)
                },
            };
            machine.values.push(flow);
            Ok(())
        },
        Task::Returned => {
            let computation = machine.pop_comp()?;
            machine.values.push(core.value_returned(computation));
            Ok(())
        },
        Task::PathType => {
            let right = machine.pop_value()?;
            let left = machine.pop_value()?;
            let carrier = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_path(carrier, left, right));
            Ok(())
        },
        Task::FlowType => {
            let target = machine.pop_value()?;
            let source = machine.pop_value()?;
            let carrier = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_flow(carrier, source, target));
            Ok(())
        },
        Task::RunType => {
            let session = machine.pop_value()?;
            machine.value_types.push(core.value_type_run(session));
            Ok(())
        },
        Task::DialogueType => {
            let session = machine.pop_value()?;
            machine.value_types.push(core.value_type_dialogue(session));
            Ok(())
        },
        Task::PrefixType => {
            let session = machine.pop_value()?;
            machine.value_types.push(core.value_type_prefix(session));
            Ok(())
        },
        Task::Tuple(count) => {
            let start = machine
                .values
                .len()
                .checked_sub(count)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let tuple = core.value_tuple(machine.values.get(start ..).unwrap_or_default());
            machine.values.truncate(start);
            machine.values.push(tuple);
            Ok(())
        },
        Task::ListCons => {
            let tail = machine.pop_value()?;
            let head = machine.pop_value()?;
            machine.values.push(core.value_list_cons(head, tail));
            Ok(())
        },
        Task::Univalence => {
            let forward = machine.pop_value()?;
            let record = machine.pop_value()?;
            machine.values.push(core.value_univalence(record, forward));
            Ok(())
        },
        Task::ListFold => {
            let on_cons = machine.pop_comp()?;
            let on_nil = machine.pop_comp()?;
            let result = machine.pop_value_type()?;
            let element = machine.pop_value_type()?;
            let list = machine.pop_value()?;
            machine
                .comps
                .push(core.computation_list_fold(element, result, list, on_nil, on_cons));
            Ok(())
        },
        Task::ListCase => {
            let on_cons = machine.pop_comp()?;
            let on_nil = machine.pop_comp()?;
            let list = machine.pop_value()?;
            machine
                .comps
                .push(core.computation_list_case(list, on_nil, on_cons));
            Ok(())
        },
        Task::Inject { summand } => {
            let body = machine.pop_value()?;
            machine.values.push(core.value_injection(summand, body));
            Ok(())
        },
        Task::Lift { target } => {
            let body = machine.pop_value()?;
            let Some(held) = domain.level(target)
            else {
                return Err(ReadbackFault::Domain(DomainFault::Dangling));
            };
            let level = held.level().clone();
            machine.values.push(core.value_lift(level, body));
            Ok(())
        },
        Task::Thunk => {
            let body = machine.pop_comp()?;
            machine.values.push(core.value_thunk(body));
            Ok(())
        },
        Task::Lambda => {
            let body = machine.pop_comp()?;
            machine.comps.push(core.computation_lambda(body));
            Ok(())
        },
        Task::Fixpoint(evidence) => {
            let body = machine.pop_comp()?;
            machine
                .comps
                .push(core.computation_fixpoint(body, evidence));
            Ok(())
        },
        Task::StaticLambda => {
            let body = machine.pop_value()?;
            machine.values.push(core.value_static_lambda(body));
            Ok(())
        },
        Task::Return => {
            let produced = machine.pop_value()?;
            machine.comps.push(core.computation_return(produced));
            Ok(())
        },
        Task::Spine(spine) => step_spine(core, domain, machine, spine),
        Task::Force => {
            let forced = machine.pop_value()?;
            machine.comps.push(core.computation_force(forced));
            Ok(())
        },
        Task::Apply => {
            let argument = machine.pop_value()?;
            let head = machine.pop_comp()?;
            machine
                .comps
                .push(core.computation_application(head, argument));
            Ok(())
        },
        Task::StaticApply => {
            let argument = machine.pop_value()?;
            let head = machine.pop_value()?;
            machine
                .values
                .push(core.value_static_application(head, argument));
            Ok(())
        },
        Task::Bind => {
            let body = machine.pop_comp()?;
            let bound = machine.pop_comp()?;
            machine.comps.push(core.computation_bind(bound, body));
            Ok(())
        },
        Task::Split(arity) => {
            let body = machine.pop_comp()?;
            let scrutinee = machine.pop_value()?;
            machine
                .comps
                .push(core.computation_split(scrutinee, arity, body));
            Ok(())
        },
        Task::DependentSplit(arity) => {
            let body = machine.pop_comp()?;
            let motive = machine.pop_comp_type()?;
            let scrutinee = machine.pop_value()?;
            machine
                .comps
                .push(core.computation_dependent_split(scrutinee, arity, motive, body));
            Ok(())
        },
        Task::Case(count) => {
            let start = machine
                .comps
                .len()
                .checked_sub(count)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let scrutinee = machine.pop_value()?;
            let case =
                core.computation_case(scrutinee, machine.comps.get(start ..).unwrap_or_default());
            machine.comps.truncate(start);
            machine.comps.push(case);
            Ok(())
        },
        Task::QuotedValueType {
            quoted,
            frame,
            binders,
        } => step_quoted_value_type(core, domain, machine, quoted, frame, binders),
        Task::QuotedCompType {
            quoted,
            frame,
            binders,
        } => step_quoted_comp_type(core, domain, machine, quoted, frame, binders),
        Task::QuotedCode {
            code,
            frame,
            binders,
        } => {
            let environment = machine.frame(frame)?.clone();
            let evaluated = eval_value_within(
                core,
                domain,
                machine.definitions,
                machine.fuel,
                code,
                environment,
            );
            let (value, remaining) = evaluated.map_err(ReadbackFault::Eval)?;
            machine.fuel = remaining;
            machine.tasks.push(Task::Value { value, binders });
            Ok(())
        },
        Task::Quote => {
            let quoted = machine.pop_value_type()?;
            machine.values.push(core.value_quote(quoted));
            Ok(())
        },
        Task::QuoteComputation => {
            let quoted = machine.pop_comp_type()?;
            machine.values.push(core.value_quote_computation(quoted));
            Ok(())
        },
        Task::ProductType(source) | Task::SumType(source) => {
            let (product, arity) = match core.value_type(source) {
                Some(&ValueType::Product(ref parts)) => (true, parts.len()),
                Some(&ValueType::Sum(ref parts)) => (false, parts.len()),
                _ => return Err(ReadbackFault::MachineInvariant),
            };
            let start = machine
                .value_types
                .len()
                .checked_sub(arity)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let read = machine
                .value_types
                .get(start ..)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let assembled = if product {
                core.value_type_product(read)
            }
            else {
                core.value_type_sum(read)
            };
            machine.value_types.truncate(start);
            machine.value_types.push(assembled);
            Ok(())
        },
        Task::ThunkType => {
            let body = machine.pop_comp_type()?;
            machine.value_types.push(core.value_type_thunk(body));
            Ok(())
        },
        Task::LiftType { target } => {
            let inner = machine.pop_value_type()?;
            let level = held_level(domain, target)?;
            machine.value_types.push(core.value_type_lift(inner, level));
            Ok(())
        },
        Task::Element { target } => {
            let code = machine.pop_value()?;
            let level = held_level(domain, target)?;
            machine
                .value_types
                .push(core.value_type_element(code, level));
            Ok(())
        },
        Task::CompElement { target } => {
            let code = machine.pop_value()?;
            let level = held_level(domain, target)?;
            machine.comp_types.push(core.comp_type_element(code, level));
            Ok(())
        },
        Task::Returner { source } => {
            let source = core
                .comp_type(source)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let CompType::Returner { ref effects, .. } = *source
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let effects = effects
                .try_map_types(gandr_core_term::effect::TypeOrder::Reverse, |_| {
                    machine.pop_value_type()
                })?;
            let result = machine.pop_value_type()?;
            machine
                .comp_types
                .push(core.comp_type_returner_with_effects(result, effects));
            Ok(())
        },
        Task::CapabilityType { source } => {
            let source = core
                .value_type(source)
                .ok_or(ReadbackFault::MachineInvariant)?;
            let ValueType::Capability {
                ref authority,
                grade,
                region,
            } = *source
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let authority = authority
                .try_map_types(gandr_core_term::effect::TypeOrder::Reverse, |_| {
                    machine.pop_value_type()
                })?;
            machine
                .value_types
                .push(core.value_type_capability(authority, grade, region));
            Ok(())
        },
        Task::Arrow => {
            let codomain = machine.pop_comp_type()?;
            let domain_type = machine.pop_value_type()?;
            machine
                .comp_types
                .push(core.comp_type_arrow(domain_type, codomain));
            Ok(())
        },
        Task::Pi => {
            let codomain = machine.pop_comp_type()?;
            let domain_type = machine.pop_value_type()?;
            machine
                .comp_types
                .push(core.comp_type_pi(domain_type, codomain));
            Ok(())
        },
        Task::StaticPi => {
            let codomain = machine.pop_value_type()?;
            let domain_type = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_static_pi(domain_type, codomain));
            Ok(())
        },
        Task::SigmaType => {
            let second = machine.pop_value_type()?;
            let first = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_sigma(first, second));
            Ok(())
        },
        Task::Suspended {
            closure,
            kind,
            binders,
        } => step_suspended(domain, machine, closure, kind, binders),
        Task::Substitute { body, count } => {
            let mut environment = Vec::with_capacity(usize::from(count));
            for _ in 0_usize .. usize::from(count) {
                environment.push(machine.pop_value()?);
            }
            environment.reverse();
            match substitute_environment(core, body, &environment) {
                TermId::Value(value) => machine.values.push(value),
                TermId::Computation(comp) => machine.comps.push(comp),
            }
            Ok(())
        },
    }
}

/// Read back the hole or the mark a neutral stands on.
///
/// # Specification
/// - requires: `closure` holds the hole or the mark itself as its source body,
///   as evaluation suspends one; a filling the run writes is written in the
///   context the hole stands in.
/// - ensures: a hole the run does not write, and a mark or a written hole
///   closed over an environment with no intuitionistic entry, push their term —
///   the hole, the mark, or the filling — on the stack of their position; a
///   mark or a written hole over a non-empty environment queues one
///   substitution, then one readback per entry, outermost first, so the
///   innermost is read first. A hole is written when the run writes its name
///   and the filling's family is the hole's.
/// - provides: the head half of reading a hole-headed or mark-headed neutral,
///   and the substitution half of filling one.
/// - fails: [`ReadbackFault::Domain`] when the closure does not resolve, and
///   [`ReadbackFault::MachineInvariant`] when its body is not source syntax.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a hole under a binder read as itself, the same hole
///   written with a filling that reads the bound variable, a hole of another
///   name left standing, a mark met in the empty environment and a mark whose
///   body reads a bound variable separate the spliced term, the written one,
///   the name check and the unsubstituted and substituted marks.
/// - witness: `live::tests::a_hole_evaluates_to_a_neutral_carrying_its_environment`
/// - witness: `live::tests::a_mark_reads_back_through_its_environment`
/// - witness: `live::tests::filling_resumes_where_the_hole_stood`
/// - witness: `live::tests::a_fill_leaves_other_holes_standing`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_values = machine.values.len(), entry_comps = machine.comps.len()],
    ensures: |ret| ret.is_err()
        || machine.tasks.len() > entry_tasks
        || machine.values.len().saturating_add(machine.comps.len()) == entry_values.saturating_add(entry_comps).saturating_add(1_usize),
)]
fn step_suspended(
    domain: &DomainArena,
    machine: &mut Machine<'_>,
    closure: Suspended,
    kind: SuspendedKind,
    binders: OpenBinders,
) -> Result<(), ReadbackFault>
{
    let dangling = ReadbackFault::Domain(DomainFault::Dangling);
    let (body, environment) = match closure {
        Suspended::Value(id) => {
            let held = domain.value_closure(id).ok_or(dangling)?;
            let crate::ValueBody::Source(body) = held.body()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            (TermId::Value(body), held.environment())
        },
        Suspended::Computation(id) => {
            let held = domain.comp_closure(id).ok_or(dangling)?;
            let crate::CompBody::Source(body) = held.body()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            (TermId::Computation(body), held.environment())
        },
    };
    let count = environment.depth(Zone::Intuitionistic);
    let body = match (kind, machine.writing, body) {
        (
            SuspendedKind::Hole(named),
            Writing::Fill {
                hole,
                filling: filling @ TermId::Value(_),
            },
            TermId::Value(_),
        )
        | (
            SuspendedKind::Hole(named),
            Writing::Fill {
                hole,
                filling: filling @ TermId::Computation(_),
            },
            TermId::Computation(_),
        ) if named == hole => filling,
        (SuspendedKind::Hole(_), Writing::Nothing | Writing::Fill { .. }, own) => {
            match own {
                TermId::Value(value) => machine.values.push(value),
                TermId::Computation(comp) => machine.comps.push(comp),
            }
            return Ok(());
        },
        (SuspendedKind::Mark, Writing::Nothing | Writing::Fill { .. }, own) => own,
    };
    if usize::from(count) == 0_usize {
        match body {
            TermId::Value(value) => machine.values.push(value),
            TermId::Computation(comp) => machine.comps.push(comp),
        }
        return Ok(());
    }
    machine.tasks.push(Task::Substitute { body, count });
    for &value in environment.bindings(Zone::Intuitionistic) {
        machine.tasks.push(Task::Value { value, binders });
    }
    Ok(())
}

/// The level a held lift target names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a copy of the level `target` names.
/// - provides: the one read of the level table the type frames share.
/// - fails: [`ReadbackFault::Domain`] when `target` names no level.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::Domain`] — the target dangles.
///
/// # Adequacy
/// - hypothesis: L3 — decoded types retain their target level while the code
///   beneath them changes through a captured environment. Replacing the held
///   level with another target changes the type. A missing target is a checked
///   dangling refusal, excluded by the type task producer.
/// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
/// - witness: `readback::tests::a_quoted_decode_unfolds_to_the_quoted_type`
/// - witness: `readback::tests::quoted_formers_preserve_distinct_children_and_targets`
#[spec(
    ensures: |ret| domain.level(target).map_or_else(
        || ret == Err(ReadbackFault::Domain(DomainFault::Dangling)),
        |held| ret.as_ref().is_ok_and(|level| level == held.level())),
)]
fn held_level(
    domain: &DomainArena,
    target: LiftTarget,
) -> Result<Level, ReadbackFault>
{
    domain
        .level(target)
        .map(|held| held.level().clone())
        .ok_or(ReadbackFault::Domain(DomainFault::Dangling))
}

/// Read one value type a quote carries.
///
/// A type has no weak head and no face: it is rebuilt former by former, a
/// closed leaf or native path classifier is spliced as it stands, and a
/// decode's code is evaluated in the frame and read back, so a code that
/// unfolds comes back as its unfolding and a quote decodes to its type.
///
/// # Specification
/// - requires: `frame` binds every variable `quoted` reads past its own
///   dependent arrows and dependent pairs, and `binders` counts the binders
///   open where it stands.
/// - ensures: a leaf pushes itself; a composite pushes its children's tasks and
///   its own assembly frame, a dependent pair's second factor in a frame
///   extended by a fresh variable at the level `binders` has open; a decode
///   pushes its code's evaluation.
/// - provides: the value-type half of reading a quote back.
/// - fails: [`ReadbackFault::MachineInvariant`] when `quoted` does not resolve,
///   [`ReadbackFault::BinderCeiling`] at the level ceiling, and
///   [`ReadbackFault::Domain`] when the fresh variable cannot be minted.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — one case per former, separated by a quote of a leaf, a
///   quote whose decode unfolds, a quote over a dependent arrow, a quoted
///   static Pi and a quoted dependent pair whose second factor reads its
///   binder.
/// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
/// - witness: `readback::tests::a_quoted_decode_unfolds_to_the_quoted_type`
/// - witness: `readback::tests::a_quoted_dependent_pair_reads_its_binder_as_an_index`
/// - witness: `readback::tests::a_quoted_static_pi_reads_back_former_by_former`
/// - witness: `readback::tests::quoted_formers_preserve_distinct_children_and_targets`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_results = machine.value_types.len(), entry_fuel = machine.fuel],
    ensures: |ret| machine.fuel == entry_fuel && if core.value_type(quoted).is_none() {
        ret == Err(ReadbackFault::MachineInvariant) && machine.tasks.len() == entry_tasks && machine.value_types.len() == entry_results
    } else { (ret.is_ok() || matches!(core.value_type(quoted), Some(&ValueType::Sigma { .. }))) && (ret.is_err() || machine.tasks.get(entry_tasks ..).is_some_and(|new_tasks| match core.value_type(quoted) { Some(matched_native_node) => match *matched_native_node {
        ValueType::Stack { input, output } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::StackType, Task::QuotedCompType { quoted: second, frame: second_frame, binders: second_binders }, Task::QuotedCompType { quoted: first, frame: first_frame, binders: first_binders }] if *first == input && *second == output && *first_frame == frame && *second_frame == frame && *first_binders == binders && *second_binders == binders),
        ValueType::List(element) => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::ListType, Task::QuotedValueType { quoted: child, frame: child_frame, binders: child_binders }] if *child == element && *child_frame == frame && *child_binders == binders),
        ValueType::Staged { base, stage } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::StagedType(held), Task::QuotedValueType { quoted: child, frame: child_frame, binders: child_binders }] if *held == stage && *child == base && *child_frame == frame && *child_binders == binders),
        ValueType::Kept { value, region } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::KeptType(held), Task::QuotedValueType { quoted: child, frame: child_frame, binders: child_binders }] if *held == region && *child == value && *child_frame == frame && *child_binders == binders),
        ValueType::World(gandr_core_term::world::WorldType::At { inner, world }) => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::LocatedType(held), Task::QuotedValueType { quoted: child, frame: child_frame, binders: child_binders }] if *held == world && *child == inner && *child_frame == frame && *child_binders == binders),
ValueType::PathUniverse(..) | ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) | ValueType::Unknown | ValueType::Buffer | ValueType::Web | ValueType::World(gandr_core_term::world::WorldType::Capability(_)) => new_tasks.is_empty() && machine.value_types.len() == entry_results.saturating_add(1_usize) && machine.value_types.last() == Some(&quoted),
ValueType::Capability { ref authority, .. } => machine.value_types.len() == entry_results
            && new_tasks.first() == Some(&Task::CapabilityType { source: quoted })
            && new_tasks.len() == authority.types().count().saturating_add(1)
            && new_tasks.iter().skip(1).zip(authority.types().rev()).all(|(task, child)| *task == Task::QuotedValueType { quoted: child, frame, binders }),
ValueType::Product(ref parts) | ValueType::Sum(ref parts) if parts.is_empty() => new_tasks.is_empty() && machine.value_types.len() == entry_results.saturating_add(1_usize) && machine.value_types.last() == Some(&quoted),
ValueType::Product(ref parts) | ValueType::Sum(ref parts) => machine.value_types.len() == entry_results
            && new_tasks.first() == Some(&if matches!(*matched_native_node, ValueType::Product(_)) { Task::ProductType(quoted) } else { Task::SumType(quoted) })
            && new_tasks.len() == parts.len().saturating_add(1)
            && new_tasks.iter().skip(1).zip(parts.iter().rev()).all(|(task, part)| *task == Task::QuotedValueType { quoted: *part, frame, binders }),
ValueType::StaticPi { domain: first, codomain: second } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::StaticPi, Task::QuotedValueType { quoted: second_task, frame: second_task_frame, binders: second_task_binders }, Task::QuotedValueType { quoted: first_task, frame: first_task_frame, binders: first_task_binders }] if *first_task == first && *first_task_frame == frame && *first_task_binders == binders && *second_task == second && *second_task_frame == frame && *second_task_binders == binders),
ValueType::Sigma { first, second } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::SigmaType, Task::QuotedValueType { quoted: second_task, binders: deeper, .. }, Task::QuotedValueType { quoted: first_task, frame: first_task_frame, binders: first_task_binders }] if *first_task == first && *first_task_frame == frame && *first_task_binders == binders && *second_task == second && Some(*deeper) == binders.opened(Zone::Intuitionistic)),
ValueType::Thunk(body) => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::ThunkType, Task::QuotedCompType { quoted: child, frame: child_frame, binders: child_binders }] if *child == body && *child_frame == frame && *child_binders == binders),
ValueType::Lift { inner, ref target } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::LiftType { target: held }, Task::QuotedValueType { quoted: child, frame: child_frame, binders: child_binders }] if domain.level(*held).is_some_and(|level| level.level() == target) && *child == inner && *child_frame == frame && *child_binders == binders),
ValueType::Element { code, ref target } => machine.value_types.len() == entry_results && matches!(new_tasks, [Task::Element { target: held }, Task::QuotedCode { code: child, frame: child_frame, binders: child_binders }] if domain.level(*held).is_some_and(|level| level.level() == target) && *child == code && *child_frame == frame && *child_binders == binders),
ValueType::Data { ref arguments, .. } => machine.value_types.len() == entry_results
            && new_tasks.first() == Some(&Task::DataType(quoted))
            && new_tasks.len() == arguments.len().saturating_add(1)
            && new_tasks.iter().skip(1).zip(arguments.iter().rev()).all(|(task, argument)| *task == Task::QuotedCode { code: *argument, frame, binders }),
ValueType::Record(ref fields) => machine.value_types.len() == entry_results
            && new_tasks.first() == Some(&Task::RecordType(quoted))
            && new_tasks.len() == fields.len().saturating_add(1)
            && new_tasks.iter().skip(1).zip(fields.values().rev()).all(|(task, field)| *task == Task::QuotedValueType { quoted: *field, frame, binders }),
ValueType::Session(ref session) => machine.value_types.len() == entry_results
            && new_tasks.first() == Some(&Task::SessionType(quoted))
            && new_tasks.len() == session.payloads().len().saturating_add(1)
            && new_tasks.iter().skip(1).zip(session.payloads().iter().rev()).all(|(task, payload)| *task == Task::QuotedValueType { quoted: *payload, frame, binders }),
ValueType::Path { carrier, left, right } => machine.value_types.len() == entry_results
            && matches!(new_tasks, [Task::PathType, Task::QuotedCode { code: second, .. }, Task::QuotedCode { code: first, .. }, Task::QuotedValueType { quoted: child, .. }]
                if *second == right && *first == left && *child == carrier),
ValueType::Flow { carrier, source, target } => machine.value_types.len() == entry_results
            && matches!(new_tasks, [Task::FlowType, Task::QuotedCode { code: second, .. }, Task::QuotedCode { code: first, .. }, Task::QuotedValueType { quoted: child, .. }]
                if *second == target && *first == source && *child == carrier),
ValueType::Run(session) => machine.value_types.len() == entry_results
            && matches!(new_tasks, [Task::RunType, Task::QuotedCode { code: child, .. }] if *child == session),
ValueType::Prefix(session) => machine.value_types.len() == entry_results
            && matches!(new_tasks, [Task::PrefixType, Task::QuotedCode { code: child, .. }] if *child == session),
ValueType::Dialogue(session) => machine.value_types.len() == entry_results
            && matches!(new_tasks, [Task::DialogueType, Task::QuotedCode { code: child, .. }] if *child == session),
},
None => false,
})) },
)]
fn step_quoted_value_type(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    quoted: ValueTypeId,
    frame: Frame,
    binders: OpenBinders,
) -> Result<(), ReadbackFault>
{
    let node = core
        .value_type(quoted)
        .ok_or(ReadbackFault::MachineInvariant)?;
    let at = |quoted: ValueTypeId| Task::QuotedValueType {
        quoted,
        frame,
        binders,
    };
    match *node {
        ValueType::Stack { input, output } => {
            machine.tasks.extend([
                Task::StackType,
                Task::QuotedCompType {
                    quoted: output,
                    frame,
                    binders,
                },
                Task::QuotedCompType {
                    quoted: input,
                    frame,
                    binders,
                },
            ]);
        },
        ValueType::List(element) => {
            machine.tasks.push(Task::ListType);
            machine.tasks.push(at(element));
        },
        ValueType::Staged { base, stage } => {
            machine.tasks.push(Task::StagedType(stage));
            machine.tasks.push(at(base));
        },
        ValueType::Kept { value, region } => {
            machine.tasks.push(Task::KeptType(region));
            machine.tasks.push(at(value));
        },
        ValueType::World(gandr_core_term::world::WorldType::At { inner, world }) => {
            machine.tasks.push(Task::LocatedType(world));
            machine.tasks.push(at(inner));
        },
        ValueType::Path {
            carrier,
            left,
            right,
        } => {
            machine.tasks.push(Task::PathType);
            machine.tasks.push(Task::QuotedCode {
                code: right,
                frame,
                binders,
            });
            machine.tasks.push(Task::QuotedCode {
                code: left,
                frame,
                binders,
            });
            machine.tasks.push(at(carrier));
        },
        ValueType::Flow {
            carrier,
            source,
            target,
        } => {
            machine.tasks.push(Task::FlowType);
            machine.tasks.push(Task::QuotedCode {
                code: target,
                frame,
                binders,
            });
            machine.tasks.push(Task::QuotedCode {
                code: source,
                frame,
                binders,
            });
            machine.tasks.push(at(carrier));
        },
        ValueType::Run(session) => {
            machine.tasks.push(Task::RunType);
            machine.tasks.push(Task::QuotedCode {
                code: session,
                frame,
                binders,
            });
        },
        ValueType::Prefix(session) => {
            machine.tasks.push(Task::PrefixType);
            machine.tasks.push(Task::QuotedCode {
                code: session,
                frame,
                binders,
            });
        },
        ValueType::Dialogue(session) => {
            machine.tasks.push(Task::DialogueType);
            machine.tasks.push(Task::QuotedCode {
                code: session,
                frame,
                binders,
            });
        },
        ValueType::PathUniverse(..)
        | ValueType::Base(_)
        | ValueType::Universe { .. }
        | ValueType::Abstract(_)
        | ValueType::Unknown
        | ValueType::Buffer
        | ValueType::Web
        | ValueType::World(gandr_core_term::world::WorldType::Capability(_)) => {
            machine.value_types.push(quoted);
        },
        ValueType::Capability { ref authority, .. } => {
            machine.tasks.push(Task::CapabilityType { source: quoted });
            machine.tasks.extend(authority.types().rev().map(at));
        },
        // The empty product and the empty sum are closed leaves.
        ValueType::Product(ref parts) | ValueType::Sum(ref parts) if parts.is_empty() => {
            machine.value_types.push(quoted);
        },
        ValueType::Data { ref arguments, .. } => {
            machine.tasks.push(Task::DataType(quoted));
            for &code in arguments.iter().rev() {
                machine.tasks.push(Task::QuotedCode {
                    code,
                    frame,
                    binders,
                });
            }
        },
        ValueType::Record(ref fields) => {
            machine.tasks.push(Task::RecordType(quoted));
            machine
                .tasks
                .extend(fields.values().rev().map(|&field| at(field)));
        },
        ValueType::Session(ref session) => {
            machine.tasks.push(Task::SessionType(quoted));
            machine
                .tasks
                .extend(session.payloads().iter().rev().map(|&payload| at(payload)));
        },
        ValueType::Product(ref parts) => {
            machine.tasks.push(Task::ProductType(quoted));
            machine
                .tasks
                .extend(parts.iter().rev().map(|&part| at(part)));
        },
        ValueType::Sum(ref parts) => {
            machine.tasks.push(Task::SumType(quoted));
            machine
                .tasks
                .extend(parts.iter().rev().map(|&part| at(part)));
        },
        // The static Pi opens no binder: its codomain stands in the ambient
        // context, so both halves read in the same frame.
        ValueType::StaticPi {
            domain: from,
            codomain,
        } => {
            machine.tasks.push(Task::StaticPi);
            machine.tasks.push(at(codomain));
            machine.tasks.push(at(from));
        },
        // The dependent pair opens a fresh variable for its second factor, as
        // the dependent arrow does for its codomain.
        ValueType::Sigma { first, second } => {
            let zone = Zone::Intuitionistic;
            let Some(deeper) = binders.opened(zone)
            else {
                return Err(ReadbackFault::BinderCeiling { zone });
            };
            let level = binders.fresh(zone);
            let minted = domain.neutral_node(
                NeutralHead::Variable { zone, level },
                Vec::new(),
                Unfolding::Rigid,
            );
            let neutral = minted.map_err(ReadbackFault::Domain)?;
            let bound = domain
                .value_neutral(neutral, TermFace::Reduced)
                .map_err(ReadbackFault::Domain)?;
            let mut extended = machine.frame(frame)?.clone();
            extended.extend(zone, bound);
            let inside = machine.hold_frame(extended);
            machine.tasks.push(Task::SigmaType);
            machine.tasks.push(Task::QuotedValueType {
                quoted: second,
                frame: inside,
                binders: deeper,
            });
            machine.tasks.push(at(first));
        },
        ValueType::Thunk(body) => {
            machine.tasks.push(Task::ThunkType);
            machine.tasks.push(Task::QuotedCompType {
                quoted: body,
                frame,
                binders,
            });
        },
        ValueType::Lift { inner, ref target } => {
            let target = domain.hold_level(target.clone());
            machine.tasks.push(Task::LiftType { target });
            machine.tasks.push(at(inner));
        },
        ValueType::Element { code, ref target } => {
            let target = domain.hold_level(target.clone());
            machine.tasks.push(Task::Element { target });
            machine.tasks.push(Task::QuotedCode {
                code,
                frame,
                binders,
            });
        },
    }
    Ok(())
}

/// Read one computation type a quote carries.
///
/// A dependent arrow opens a fresh variable for its codomain, exactly as a
/// lambda's body is opened: the codomain is read in a new frame, the quote's
/// environment extended by that variable, one binder further in.
///
/// # Specification
/// - requires: as [`step_quoted_value_type`].
/// - ensures: a composite pushes its children's tasks and its own assembly
///   frame, a dependent arrow's codomain in a frame extended by a fresh
///   variable at the level `binders` has open; a decode pushes its code's
///   evaluation.
/// - provides: the computation-type half of reading a quote back.
/// - fails: [`ReadbackFault::MachineInvariant`] when `quoted` or `frame` does
///   not resolve, [`ReadbackFault::BinderCeiling`] at the level ceiling, and
///   [`ReadbackFault::Domain`] when the fresh variable cannot be minted.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the dependent arrow is the one arm that opens a binder,
///   separated by a quote whose codomain reads it.
/// - witness: `readback::tests::a_quoted_dependent_arrow_reads_its_binder_as_an_index`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_frames = machine.frames.len(), entry_fuel = machine.fuel],
    ensures: |ret| machine.fuel == entry_fuel && (ret.is_err() || machine.tasks.get(entry_tasks ..).is_some_and(|new_tasks| match core.comp_type(quoted) {
        | Some(&CompType::With(ref parts)) => new_tasks.first() == Some(&Task::WithType(quoted))
            && new_tasks.len() == parts.len().saturating_add(1)
            && new_tasks.iter().skip(1).zip(parts.iter().rev()).all(|(task, part)| *task == Task::QuotedCompType { quoted: *part, frame, binders }),
        | Some(&CompType::Codata { ref arguments, .. }) => new_tasks.first() == Some(&Task::CodataType(quoted))
            && new_tasks.len() == arguments.len().saturating_add(1)
            && new_tasks.iter().skip(1).zip(arguments.iter().rev()).all(|(task, argument)| *task == Task::QuotedCode { code: *argument, frame, binders }),
        | Some(&CompType::Returner { result, ref effects }) => new_tasks.first() == Some(&Task::Returner { source: quoted })
            && new_tasks.len() == effects.types().count().saturating_add(2)
            && new_tasks.iter().skip(1).zip(effects.types().rev().chain(core::iter::once(result))).all(|(task, child)| matches!(task, Task::QuotedValueType { quoted, frame: child_frame, binders: child_binders } if *quoted == child && *child_frame == frame && *child_binders == binders)),
        | Some(&CompType::Arrow { domain: from, codomain }) => matches!(new_tasks, [Task::Arrow, Task::QuotedCompType { quoted: second, frame: second_frame, binders: second_binders }, Task::QuotedValueType { quoted: first, frame: first_frame, binders: first_binders }] if *first == from && *first_frame == frame && *first_binders == binders && *second == codomain && *second_frame == frame && *second_binders == binders),
        | Some(&CompType::Element { code, ref target }) => matches!(new_tasks, [Task::CompElement { target: held }, Task::QuotedCode { code: child, frame: child_frame, binders: child_binders }] if domain.level(*held).is_some_and(|level| level.level() == target) && *child == code && *child_frame == frame && *child_binders == binders),
        | Some(&CompType::Pi { domain: from, codomain }) => matches!(new_tasks, [Task::Pi, Task::QuotedCompType { quoted: second, frame: inside, binders: deeper }, Task::QuotedValueType { quoted: first, frame: first_frame, binders: first_binders }] if *first == from && *first_frame == frame && *first_binders == binders && *second == codomain && Some(*deeper) == binders.opened(Zone::Intuitionistic) && inside.0 == entry_frames && machine.frames.len() == entry_frames.saturating_add(1_usize)
        && machine.frames.get(inside.0).zip(machine.frames.get(frame.0)).is_some_and(|(extended, ambient)|
            extended.bindings(Zone::Linear) == ambient.bindings(Zone::Linear)
            && usize::from(extended.depth(Zone::Intuitionistic)) == usize::from(ambient.depth(Zone::Intuitionistic)).saturating_add(1_usize)
            && extended.bindings(Zone::Intuitionistic).get(.. usize::from(ambient.depth(Zone::Intuitionistic))) == Some(ambient.bindings(Zone::Intuitionistic))
            && extended.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)).and_then(|value| domain.value(value)).is_some_and(|node|
                matches!(node, DomainValue::Neutral { neutral, .. } if domain.neutral(*neutral).is_some_and(|held| held.head() == NeutralHead::Variable { zone: Zone::Intuitionistic, level: binders.fresh(Zone::Intuitionistic) })))) ),
        | Some(&CompType::Unknown) => new_tasks.is_empty() && machine.comp_types.last() == Some(&quoted),
        | None => false,
    })),
)]
fn step_quoted_comp_type(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    quoted: CompTypeId,
    frame: Frame,
    binders: OpenBinders,
) -> Result<(), ReadbackFault>
{
    let node = core
        .comp_type(quoted)
        .cloned()
        .ok_or(ReadbackFault::MachineInvariant)?;
    match node {
        CompType::Unknown => machine.comp_types.push(quoted),
        CompType::With(parts) => {
            machine.tasks.push(Task::WithType(quoted));
            machine
                .tasks
                .extend(parts.iter().rev().map(|&part| Task::QuotedCompType {
                    quoted: part,
                    frame,
                    binders,
                }));
        },
        CompType::Codata { arguments, .. } => {
            machine.tasks.push(Task::CodataType(quoted));
            for code in arguments.into_iter().rev() {
                machine.tasks.push(Task::QuotedCode {
                    code,
                    frame,
                    binders,
                });
            }
        },
        CompType::Returner { result, effects } => {
            machine.tasks.push(Task::Returner { source: quoted });
            machine
                .tasks
                .extend(effects.types().rev().map(|quoted| Task::QuotedValueType {
                    quoted,
                    frame,
                    binders,
                }));
            machine.tasks.push(Task::QuotedValueType {
                quoted: result,
                frame,
                binders,
            });
        },
        CompType::Arrow {
            domain: from,
            codomain,
        } => {
            machine.tasks.push(Task::Arrow);
            machine.tasks.push(Task::QuotedCompType {
                quoted: codomain,
                frame,
                binders,
            });
            machine.tasks.push(Task::QuotedValueType {
                quoted: from,
                frame,
                binders,
            });
        },
        CompType::Pi {
            domain: from,
            codomain,
        } => {
            let zone = Zone::Intuitionistic;
            let Some(deeper) = binders.opened(zone)
            else {
                return Err(ReadbackFault::BinderCeiling { zone });
            };
            let level = binders.fresh(zone);
            let minted = domain.neutral_node(
                NeutralHead::Variable { zone, level },
                Vec::new(),
                Unfolding::Rigid,
            );
            let neutral = minted.map_err(ReadbackFault::Domain)?;
            let bound = domain
                .value_neutral(neutral, TermFace::Reduced)
                .map_err(ReadbackFault::Domain)?;
            let mut extended = machine.frame(frame)?.clone();
            extended.extend(zone, bound);
            let inside = machine.hold_frame(extended);
            machine.tasks.push(Task::Pi);
            machine.tasks.push(Task::QuotedCompType {
                quoted: codomain,
                frame: inside,
                binders: deeper,
            });
            machine.tasks.push(Task::QuotedValueType {
                quoted: from,
                frame,
                binders,
            });
        },
        CompType::Element { code, target } => {
            let target = domain.hold_level(target);
            machine.tasks.push(Task::CompElement { target });
            machine.tasks.push(Task::QuotedCode {
                code,
                frame,
                binders,
            });
        },
    }
    Ok(())
}

/// Perform one value task: read one domain value node.
///
/// # Specification
/// - requires: `binders` counts the binders `value` stands under; a literal
///   node's held core id names the core value holding its payload, which is the
///   same cross-arena precondition every domain constructor inherits and which
///   this arm splices rather than re-checks.
/// - ensures: a retained face pushes the source id and mints nothing; a leaf
///   pushes its rebuilt node — a literal by splicing the id that already holds
///   its payload; a composite pushes its children's tasks and its own assembly
///   frame, so the frame runs after them.
/// - provides: the value half of the transition relation. The clause states
///   that a success pushes at least one value result or task and consumes
///   neither result stack; which node was pushed, and which frame was queued
///   after which task, are judgements over the produced term, and the witnesses
///   below carry them.
/// - fails: [`ReadbackFault::Domain`] for an unresolvable node, and whatever
///   entering a thunk's closure or folding a neutral refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the face choice ahead of the
///   nine-arm match, separated by a retained face, and by one case per arm —
///   the two leaves, the pair, the injection, the lift, the thunk, the neutral,
///   the code, and the static lambda.
/// - witness: `readback::tests::an_unreduced_value_reads_back_as_its_own_source`
/// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
/// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
/// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
/// - witness: `readback::tests::a_static_lambda_reads_back_with_its_binder_as_an_index`
// economy: a rebuilt node is minted fresh, with no table keyed on the domain
// node, so a domain value reachable by two paths is read back twice and the
// sharing an environment carried is expanded into a tree. The ceiling is the
// expansion of the domain's own sharing, which a duplicated binder makes
// exponential rather than merely quadratic. Upgrade path: a memo from
// (domain node, open binders) to the minted core id, held on the machine — the
// same sharing decision the duplication parameter owns, which is why it belongs
// behind that parameter rather than inside this walk.
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.comps.len() == entry_comps
            && (machine.values.len() > entry_values || machine.tasks.len() > entry_tasks)),
)]
fn step_value(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    value: DomainValueId,
    binders: OpenBinders,
) -> Result<(), ReadbackFault>
{
    let Some(&node) = domain.value(value)
    else {
        return Err(ReadbackFault::Domain(DomainFault::Dangling));
    };
    if let Some(source) = retained_value(machine.mode, node) {
        machine.values.push(source);
        return Ok(());
    }
    match node {
        DomainValue::Constructor {
            datatype,
            tag,
            fields,
            ..
        } => {
            let closure = domain
                .value_closure(datatype)
                .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
            let crate::ValueBody::ValueType(quoted) = closure.body()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let frame = machine.hold_frame(closure.environment().clone());
            machine.tasks.push(Task::Constructor { tag, fields });
            for &value in domain
                .fields(fields)
                .map_err(ReadbackFault::Domain)?
                .iter()
                .rev()
            {
                machine.tasks.push(Task::Value { value, binders });
            }
            machine.tasks.push(Task::QuotedValueType {
                quoted,
                frame,
                binders,
            });
            Ok(())
        },
        DomainValue::Record { source, fields, .. } => {
            let fields = domain.fields(fields).map_err(ReadbackFault::Domain)?;
            if !matches!(core.value(source), Some(Value::Record(labels)) if labels.len() == fields.len())
            {
                return Err(ReadbackFault::MachineInvariant);
            }
            machine.tasks.push(Task::Record(source));
            for &value in fields.iter().rev() {
                machine.tasks.push(Task::Value { value, binders });
            }
            Ok(())
        },
        DomainValue::Recorded {
            source,
            reading: Reading::Decomposed,
            ..
        } => {
            let Some(&Value::Dialogue(ref moves)) = core.value(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let pieces = crate::eval::decomposition(moves).map_err(ReadbackFault::Eval)?;
            machine.values.push(core.value_web(pieces));
            Ok(())
        },
        DomainValue::Recorded {
            source,
            fields,
            reading: Reading::Written,
            ..
        } => {
            let fields = domain.fields(fields).map_err(ReadbackFault::Domain)?;
            if core
                .value(source)
                .and_then(crate::eval::recording)
                .map(Iterator::count)
                != Some(fields.len())
            {
                return Err(ReadbackFault::MachineInvariant);
            }
            machine.tasks.push(Task::Recorded(source));
            for &value in fields.iter().rev() {
                machine.tasks.push(Task::Value { value, binders });
            }
            Ok(())
        },
        DomainValue::ListNil { .. } => {
            machine.values.push(core.value_list_nil());
            Ok(())
        },
        DomainValue::ListCons { first, second, .. } => {
            machine.tasks.push(Task::ListCons);
            machine.tasks.push(Task::Value {
                value: second,
                binders,
            });
            machine.tasks.push(Task::Value {
                value: first,
                binders,
            });
            Ok(())
        },
        DomainValue::PathCertificate { certificate, .. } => {
            machine.values.push(certificate);
            Ok(())
        },
        DomainValue::PathProduct { first, second, .. } => {
            machine.tasks.push(Task::PathProduct);
            machine.tasks.push(Task::Value {
                value: second,
                binders,
            });
            machine.tasks.push(Task::Value {
                value: first,
                binders,
            });
            Ok(())
        },
        DomainValue::Here { point, .. } => {
            machine.tasks.push(Task::Here);
            machine.tasks.push(Task::Value {
                value: point,
                binders,
            });
            Ok(())
        },
        DomainValue::Univalence {
            record, forward, ..
        } => {
            machine.tasks.push(Task::Univalence);
            machine.tasks.push(Task::Value {
                value: forward,
                binders,
            });
            machine.tasks.push(Task::Value {
                value: record,
                binders,
            });
            Ok(())
        },
        // A held `back` or `then` reads back as the transport that formed it.
        DomainValue::HeldTransport {
            motive,
            path,
            value,
            ..
        } => {
            let family = fresh_motive(domain, machine, motive, binders)?;
            machine.tasks.push(Task::Returned);
            machine.tasks.push(Task::PathTransport);
            machine.tasks.push(Task::Value { value, binders });
            machine.tasks.push(Task::Value {
                value: path,
                binders,
            });
            machine.tasks.push(family);
            Ok(())
        },
        DomainValue::Flow { former, parts, .. } => {
            let parts = domain.fields(parts).map_err(ReadbackFault::Domain)?;
            machine.tasks.push(Task::Flow(former));
            for &value in parts.iter().rev() {
                machine.tasks.push(Task::Value { value, binders });
            }
            Ok(())
        },
        DomainValue::Literal { literal, .. } => {
            // The payload was never copied into the domain: the node names the
            // core value that holds it, and that id is valid whatever the face
            // says, so the readback splices it rather than rebuilding a literal
            // it would have to read back out of the same arena.
            machine.values.push(literal);
            Ok(())
        },
        DomainValue::Tuple { fields, .. } => {
            let components = domain.fields(fields).map_err(ReadbackFault::Domain)?;
            machine.tasks.push(Task::Tuple(components.len()));
            for &value in components.iter().rev() {
                machine.tasks.push(Task::Value { value, binders });
            }
            Ok(())
        },
        DomainValue::Injection { summand, body, .. } => {
            machine.tasks.push(Task::Inject { summand });
            machine.tasks.push(Task::Value {
                value: body,
                binders,
            });
            Ok(())
        },
        DomainValue::Thunk { body, .. } => {
            let whnf = enter(core, domain, machine, body, Entry::Bare)?;
            machine.tasks.push(Task::Thunk);
            machine.tasks.push(Task::Comp {
                comp: whnf,
                binders,
            });
            Ok(())
        },
        DomainValue::Lift { target, body, .. } => {
            machine.tasks.push(Task::Lift { target });
            machine.tasks.push(Task::Value {
                value: body,
                binders,
            });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            step_neutral(core, domain, machine, neutral, Polarity::Value, binders)
        },
        DomainValue::Code { code, .. } => {
            let Some(closure) = domain.value_closure(code)
            else {
                return Err(ReadbackFault::Domain(DomainFault::Dangling));
            };
            let body = closure.body();
            let frame = machine.hold_frame(closure.environment().clone());
            match body {
                crate::ValueBody::ValueType(quoted) => {
                    machine.tasks.push(Task::Quote);
                    machine.tasks.push(Task::QuotedValueType {
                        quoted,
                        frame,
                        binders,
                    });
                },
                crate::ValueBody::CompType(quoted) => {
                    machine.tasks.push(Task::QuoteComputation);
                    machine.tasks.push(Task::QuotedCompType {
                        quoted,
                        frame,
                        binders,
                    });
                },
                crate::ValueBody::Source(body) => match core.value(body) {
                    Some(&Value::Quote(quoted)) => {
                        machine.tasks.push(Task::Quote);
                        machine.tasks.push(Task::QuotedValueType {
                            quoted,
                            frame,
                            binders,
                        });
                    },
                    Some(&Value::QuoteComputation(quoted)) => {
                        machine.tasks.push(Task::QuoteComputation);
                        machine.tasks.push(Task::QuotedCompType {
                            quoted,
                            frame,
                            binders,
                        });
                    },
                    Some(_) | None => return Err(ReadbackFault::MachineInvariant),
                },
            }
            Ok(())
        },
        DomainValue::StaticLambda { lambda, .. } => {
            let (body, deeper) = open_static(core, domain, machine, lambda, binders)?;
            machine.tasks.push(Task::StaticLambda);
            machine.tasks.push(Task::Value {
                value: body,
                binders: deeper,
            });
            Ok(())
        },
    }
}

/// The task reading a one-binder motive back under a fresh variable.
///
/// The motive reads its own binder past the capture, so it is read back one
/// binder deeper, its environment extended by a rigid variable at the next
/// level, as a nominal case's motive is.
///
/// # Specification
/// - requires: `motive` names a value closure of `domain` whose body is a value
///   type.
/// - ensures: a [`Task::QuotedValueType`] over the closure's family, in a frame
///   holding its environment extended by the fresh variable, at `binders` one
///   binder deeper.
/// - provides: the motive half of a transport's or a ride's readback, stuck on
///   a spine or held as a path.
/// - fails: [`ReadbackFault::Domain`] for a dangling closure,
///   [`ReadbackFault::MachineInvariant`] for a closure holding no value type,
///   [`ReadbackFault::BinderCeiling`] past the binder ceiling.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L1 — a stuck transport's motive and a held `back`'s read back
///   with the binder as index zero; a stale environment or a missing binder
///   changes the read-back family.
/// - witness: `identity::tests::transport_along_a_stuck_path_is_stuck`
/// - witness: `identity::tests::a_held_back_reads_back_as_its_transport`
#[spec(ensures: |ret| matches!(&ret, Err(_) | Ok(Task::QuotedValueType { .. })))]
fn fresh_motive(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    motive: crate::arena::ValueClosureId,
    binders: OpenBinders,
) -> Result<Task, ReadbackFault>
{
    let held = domain
        .value_closure(motive)
        .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
    let crate::ValueBody::ValueType(family) = held.body()
    else {
        return Err(ReadbackFault::MachineInvariant);
    };
    let zone = Zone::Intuitionistic;
    let deeper = binders
        .opened(zone)
        .ok_or(ReadbackFault::BinderCeiling { zone })?;
    let mut environment = held.environment().clone();
    let fresh = domain
        .neutral_node(
            NeutralHead::Variable {
                zone,
                level: binders.fresh(zone),
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .map_err(ReadbackFault::Domain)?;
    let bound = domain
        .value_neutral(fresh, TermFace::Reduced)
        .map_err(ReadbackFault::Domain)?;
    environment.extend(zone, bound);
    Ok(Task::QuotedValueType {
        quoted: family,
        frame: machine.hold_frame(environment),
        binders: deeper,
    })
}

/// Perform one computation task: read one weak-head domain computation.
///
/// # Specification
/// - requires: `binders` counts the binders `comp` stands under.
/// - ensures: a retained face pushes the source id; a lambda opens its closure
///   and pushes the body's task under one more binder; a fixpoint closed over
///   nothing that a manifest definition suspends pushes `force` of that
///   definition under [`crate::Recursion::Refolded`]; any other fixpoint opens
///   its body under a fresh self variable the same way; either fixpoint is then
///   applied to its leading arguments, first to last; a returner pushes its
///   value's task; a stuck head starts the spine fold.
/// - provides: the computation half of the transition relation. The clause
///   states that a success pushes at least one computation result or task and
///   consumes neither result stack; which node was pushed, and which frame was
///   queued after which task, are judgements over the produced term, and the
///   witnesses below carry them.
/// - fails: [`ReadbackFault::Domain`] for an unresolvable node, and whatever
///   opening the lambda's closure or folding the spine refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the face choice ahead of the
///   four-arm match, separated by a retained face, a lambda, a fixpoint, a
///   returner and a stuck head.
/// - witness: `readback::tests::an_unreduced_weak_head_reads_back_as_its_own_source`
/// - witness: `eval::tests::a_fixpoint_staged_past_its_first_binder_carries_its_leading_arguments_626`
/// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
/// - witness: `readback::tests::a_fixpoint_reads_back_with_its_self_binder`
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
/// - witness: `readback::tests::a_definition_s_own_recursion_reads_back_as_the_definition`
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.values.len() >= entry_values
            && (machine.comps.len() > entry_comps || machine.tasks.len() > entry_tasks)),
)]
fn step_comp(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    comp: DomainCompId,
    binders: OpenBinders,
) -> Result<(), ReadbackFault>
{
    let Some(&node) = domain.computation(comp)
    else {
        return Err(ReadbackFault::Domain(DomainFault::Dangling));
    };
    if let Some(source) = retained_comp(machine.mode, node) {
        machine.comps.push(source);
        return Ok(());
    }
    match node {
        DomainComp::Lambda { body, .. } => {
            let opened = open(core, domain, machine, body, binders, Zone::Intuitionistic)?;
            let (whnf, deeper) = opened;
            machine.tasks.push(Task::Lambda);
            machine.tasks.push(Task::Comp {
                comp: whnf,
                binders: deeper,
            });
            Ok(())
        },
        DomainComp::Return { value, .. } => {
            machine.tasks.push(Task::Return);
            machine.tasks.push(Task::Value { value, binders });
            Ok(())
        },
        DomainComp::Neutral { neutral, .. } => step_neutral(
            core,
            domain,
            machine,
            neutral,
            Polarity::Computation,
            binders,
        ),
        DomainComp::Fixpoint {
            recursive, leading, ..
        } => {
            // The leading arguments apply to the fixpoint once it is read,
            // first to last: `fix(M) a₀ … aₖ₋₁`.
            for &argument in domain
                .fields(leading)
                .map_err(ReadbackFault::Domain)?
                .iter()
                .rev()
            {
                machine.tasks.push(Task::Apply);
                machine.tasks.push(Task::Value {
                    value: argument,
                    binders,
                });
            }
            let (source, environment) = {
                let held = domain
                    .comp_closure(recursive)
                    .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
                let crate::CompBody::Source(source) = held.body()
                else {
                    return Err(ReadbackFault::MachineInvariant);
                };
                (source, held.environment().clone())
            };
            // A definition's own recursion, closed over nothing, is the
            // definition: under the refolding stance it reads back as the
            // call its source wrote.
            if environment == crate::Environment::new()
                && let Some(constant) = machine.definitions.recursion_of(core, source)
            {
                let named = core.value_constant(constant);
                machine.comps.push(core.computation_force(named));
                return Ok(());
            }
            let Some(&Computation::Fixpoint { body, evidence }) = core.computation(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let closed = domain.comp_closure_node(body, environment);
            let (whnf, deeper) =
                open(core, domain, machine, closed, binders, Zone::Intuitionistic)?;
            machine.tasks.push(Task::Fixpoint(evidence));
            machine.tasks.push(Task::Comp {
                comp: whnf,
                binders: deeper,
            });
            Ok(())
        },
    }
}

/// Force the body a neutral's unfolding face names, recording the force on the
/// neutral.
///
/// # Specification
/// - requires: `neutral` carries [`Unfolding::Unforced`] naming `body`.
/// - ensures: on success the lowered body evaluated in the empty environment,
///   recorded on `neutral` as [`Unfolding::Forced`], with the evaluation's cost
///   taken off the machine's own budget.
/// - provides: the one place a readback lowers nothing and still unfolds: the
///   lowering is the run's, read from the bundle's
///   [`LoweredChain`](crate::LoweredChain), and the force is recorded once, so
///   a neutral read twice evaluates its body once.
/// - fails: [`ReadbackFault::UnloweredBody`] when no entry of the chain names
///   `body`, [`ReadbackFault::Eval`] carrying the evaluation's own refusal —
///   [`EvalFault::UnboundVariable`] for a lowering that is not closed — and
///   [`ReadbackFault::Domain`] when the record is refused.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::UnloweredBody`] — no entry of the chain names `body`.
/// - [`ReadbackFault::Eval`] — evaluating the lowering refused.
/// - [`ReadbackFault::Domain`] — recording the force was refused.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the lowering lookup, the
///   evaluation and the recorded force, separated by a body with no lowering, a
///   lowered body whose own value holds a second unforced definition, and the
///   neutral reading as forced once the readback returns.
/// - witness: `readback::tests::the_unfolding_mode_refuses_a_body_no_chain_entry_names`
/// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
#[spec(
    captures: entry_fuel = u32::from(machine.fuel),
    ensures: |ret| ret.is_err() || u32::from(machine.fuel) <= entry_fuel,
)]
fn force_body(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    neutral: NeutralId,
    body: GlobalIndex,
) -> Result<Glued, ReadbackFault>
{
    let Some(lowered) = machine.definitions.bodies().get(&body).copied()
    else {
        return Err(ReadbackFault::UnloweredBody { body });
    };
    let evaluated = eval_closed_value(core, domain, machine.definitions, machine.fuel, lowered);
    let (value, remaining) = evaluated.map_err(ReadbackFault::Eval)?;
    machine.fuel = remaining;
    let glued = Glued::Value(value);
    domain
        .force_neutral(neutral, glued)
        .map_err(ReadbackFault::Domain)?;
    Ok(glued)
}

/// Start reading a neutral: choose the head, then queue the spine fold.
///
/// # Specification
/// - requires: `binders` counts the binders the neutral stands under; `wanted`
///   is the polarity of the position it stands in; a forced unfolding names a
///   glued form standing in the same scope, which for a definition body is the
///   empty one, because the chain admits no definition with a free occurrence.
/// - ensures: under a mode that spends nothing, a variable, declaration or
///   module head is read as a value term and the fold starts at value polarity,
///   while a hole or a mark head queues its own reading and the fold starts at
///   the polarity of the position the hole or the mark stood in. Under the
///   spending mode, an unforced unfolding is forced first; a forced unfolding
///   then replaces the head by the glued form it was forced to and the fold
///   starts at that form's polarity — which is the reading the unfolding face
///   carries: the face names the **head's** body, so the neutral's own value is
///   that body with this spine re-applied. A value body meets the spine's
///   leading static applications by beta, and the fold resumes past them.
/// - provides: the one site the unfolding face is **spent**, and the site the
///   zero-unfold mode is defined by not spending it. Both modes read the face —
///   the read is one match on a `Copy` field and the mode's own arm is what
///   declines to act on it — and only the spending mode forces one. The clause
///   states the queued fold and, under the mode that spends nothing, the head
///   pushed as one value term unless it is suspended; the polarity the fold
///   starts at rides in the queued task rather than in any stack state, and the
///   witnesses below carry it.
/// - fails: [`ReadbackFault::Domain`] when the neutral does not resolve,
///   whatever forcing an unforced body refuses —
///   [`ReadbackFault::UnloweredBody`] among it — and whatever reading the head
///   refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the mode-by-unfolding table,
///   the static prefix and the starting polarity, separated by each of the
///   three unfolding states under each mode, by a body forced to each polarity,
///   and by an unfolded operator under a static spine.
/// - witness: `readback::tests::the_zero_unfold_mode_leaves_an_unforced_body_unforced`
/// - witness: `readback::tests::the_unfolding_mode_refuses_a_body_no_chain_entry_names`
/// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
/// - witness: `readback::tests::the_unfolding_mode_spends_a_body_already_forced`
/// - witness: `readback::tests::a_spine_that_misses_its_polarity_is_refused`
/// - witness: `readback::tests::an_unfolded_operator_reads_back_reduced`
/// - witness: `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_tasks = machine.tasks.len(),
        suspended = domain.neutral(neutral).is_some_and(|held| matches!(held.head(), NeutralHead::Hole { .. } | NeutralHead::Mark { .. })),
    ],
    ensures: |ret| [
        ret.is_err() || machine.tasks.len() > entry_tasks,
        ret.is_err()
            || machine.mode != ReadbackMode::ZeroUnfold
            || suspended
            || machine.values.len() == entry_values.saturating_add(1_usize),
    ],
)]
fn step_neutral(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    neutral: NeutralId,
    wanted: Polarity,
    binders: OpenBinders,
) -> Result<(), ReadbackFault>
{
    let (head, unfolding) = {
        let Some(held) = domain.neutral(neutral)
        else {
            return Err(ReadbackFault::Domain(DomainFault::Dangling));
        };
        (held.head(), held.unfolding())
    };
    let spent = match machine.mode {
        ReadbackMode::ZeroUnfold => None,
        ReadbackMode::Unfolding => match unfolding {
            Unfolding::Rigid => None,
            Unfolding::Unforced(body) => {
                let forced = force_body(core, domain, machine, neutral, body)?;
                Some(forced)
            },
            Unfolding::Forced(glued) => Some(glued),
        },
    };
    // An unfolded head meets the leading static applications of its spine by
    // beta rather than standing beside them as a redex: the operator's body is
    // re-applied to those arguments here, and the fold resumes past them. This
    // is what makes the spending mode's answer a static normal form.
    let (spent, start) = match spent {
        Some(Glued::Value(body)) => {
            let arguments: Vec<DomainValueId> = {
                let Some(held) = domain.neutral(neutral)
                else {
                    return Err(ReadbackFault::Domain(DomainFault::Dangling));
                };
                held.spine()
                    .iter()
                    .map_while(|elimination| match *elimination {
                        Elimination::StaticApply(argument) => Some(argument),
                        Elimination::Transport(_)
                        | Elimination::ProductTransport(_)
                        | Elimination::PathTransport { .. }
                        | Elimination::OperandTransport { .. }
                        | Elimination::Ride { .. }
                        | Elimination::OperandRide { .. }
                        | Elimination::TelescopeTransport { .. }
                        | Elimination::Apply(_)
                        | Elimination::Force
                        | Elimination::Bind(_)
                        | Elimination::ListFold { .. }
                        | Elimination::ListCase { .. }
                        | Elimination::Case { .. }
                        | Elimination::DataCase(_)
                        | Elimination::Split(_)
                        | Elimination::Projection(_)
                        | Elimination::Fixpoint { .. } => None,
                    })
                    .collect()
            };
            if arguments.is_empty() {
                (Some(Glued::Value(body)), SpineOffset::innermost())
            }
            else {
                let applied = apply_static_within(
                    core,
                    domain,
                    machine.definitions,
                    machine.fuel,
                    body,
                    &arguments,
                );
                let (reduced, remaining) = applied.map_err(ReadbackFault::Eval)?;
                machine.fuel = remaining;
                (Some(Glued::Value(reduced)), SpineOffset(arguments.len()))
            }
        },
        None | Some(Glued::Computation(_)) => (spent, SpineOffset::innermost()),
    };
    let polarity = match spent {
        None => match head {
            NeutralHead::Hole {
                closure: Suspended::Computation(_),
                ..
            }
            | NeutralHead::Mark {
                closure: Suspended::Computation(_),
                ..
            } => Polarity::Computation,
            NeutralHead::Hole {
                closure: Suspended::Value(_),
                ..
            }
            | NeutralHead::Mark {
                closure: Suspended::Value(_),
                ..
            }
            | NeutralHead::Variable { .. }
            | NeutralHead::Constant(_)
            | NeutralHead::Module(_)
            | NeutralHead::Returned(_) => Polarity::Value,
        },
        Some(Glued::Value(_)) => Polarity::Value,
        Some(Glued::Computation(_)) => Polarity::Computation,
    };
    machine.tasks.push(Task::Spine(SpineStep {
        neutral,
        at: start,
        polarity,
        wanted,
        binders,
    }));
    match spent {
        None => match head {
            NeutralHead::Hole { hole, closure } => machine.tasks.push(Task::Suspended {
                closure,
                kind: SuspendedKind::Hole(hole),
                binders,
            }),
            NeutralHead::Mark { closure, .. } => machine.tasks.push(Task::Suspended {
                closure,
                kind: SuspendedKind::Mark,
                binders,
            }),
            NeutralHead::Returned(computation) => {
                machine.tasks.push(Task::Returned);
                machine.tasks.push(Task::Comp {
                    comp: computation,
                    binders,
                });
            },
            NeutralHead::Variable { .. } | NeutralHead::Constant(_) | NeutralHead::Module(_) => {
                let term = head_term(core, head, binders)?;
                machine.values.push(term);
            },
        },
        Some(Glued::Value(value)) => machine.tasks.push(Task::Value { value, binders }),
        Some(Glued::Computation(comp)) => machine.tasks.push(Task::Comp { comp, binders }),
    }
    Ok(())
}

/// Fold one of a neutral's eliminations onto the term beneath it.
///
/// # Specification
/// - requires: the term the fold has built so far is on the result stack of
///   `spine`'s current polarity; its position counts within or one past the
///   spine.
/// - ensures: an exhausted spine leaves that term where it is, having checked
///   it stands at `wanted`; otherwise the elimination's operands are queued and
///   the frame that consumes them is queued after them, with the next position
///   queued after that. A `force` and a case walk the fold from value to
///   computation polarity; an application and a bind keep it there, and a
///   static application keeps it at value polarity.
/// - provides: the whole of "a neutral is a head with eliminations stacked on
///   it", read back as the applications, forces, binds, cases and static
///   applications that could not fire. The clause states that an exhausted
///   spine queues nothing and an unexhausted one queues at least one task, with
///   both result stacks left as they were; which operands and frames are
///   queued, and in which order, are judgements over the produced term, and the
///   witnesses below carry them.
/// - fails: [`ReadbackFault::Domain`] when the neutral does not resolve,
///   [`ReadbackFault::NeutralPolarity`] when an elimination is stacked where
///   its operand's polarity is not what the fold holds or when the finished
///   fold does not stand at `wanted`, and whatever opening a branch refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the five elimination arms, the
///   per-arm polarity guard and the end guard, separated by a spine carrying
///   one of each computation elimination in a valid order, a static spine, an
///   application stacked at value polarity, and a computation-position neutral
///   with an empty spine.
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
/// - witness: `readback::tests::a_stuck_bind_and_case_read_back_their_branches`
/// - witness: `readback::tests::a_spine_that_misses_its_polarity_is_refused`
/// - witness: `eval::tests::normalization_preserves_a_stuck_application`
#[spec(
    requires: [
        match spine.polarity {
            | Polarity::Value => !machine.values.is_empty(),
            | Polarity::Computation => !machine.comps.is_empty(),
        },
        domain
            .neutral(spine.neutral)
            .is_none_or(|held| spine.at.0 <= held.spine().len()),
    ],
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
        entry_exhausted = domain
            .neutral(spine.neutral)
            .is_none_or(|held| held.spine().get(spine.at.0).is_none()),
    ],
    ensures: |ret| ret.is_err()
        || (machine.values.len() == entry_values
            && machine.comps.len() == entry_comps
            && (if entry_exhausted {
                machine.tasks.len() == entry_tasks
            } else {
                machine.tasks.len() > entry_tasks
            })),
)]
fn step_spine(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    spine: SpineStep,
) -> Result<(), ReadbackFault>
{
    let neutral = spine.neutral;
    let binders = spine.binders;
    let stacked = {
        let Some(held) = domain.neutral(neutral)
        else {
            return Err(ReadbackFault::Domain(DomainFault::Dangling));
        };
        held.spine().get(spine.at.0).copied()
    };
    let Some(elimination) = stacked
    else {
        return expect_polarity(spine.polarity, spine.wanted, neutral);
    };
    let onward = Task::Spine(spine.onward(Polarity::Computation));
    match elimination {
        Elimination::Projection(source) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Projection(source));
            Ok(())
        },
        // The fold holds the stuck argument; the fixpoint reads back as
        // itself applied to its leading arguments, `fix(M) a₀ … aₖ₋₁`, and is
        // applied to it.
        Elimination::Fixpoint { recursive, leading } => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let fixpoint = domain.comp_fixpoint(recursive, leading, CompTermFace::Reduced);
            machine.tasks.push(onward);
            machine.tasks.push(Task::Apply);
            machine.tasks.push(Task::Comp {
                comp: fixpoint,
                binders,
            });
            Ok(())
        },
        Elimination::DataCase(closure) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let held = domain
                .comp_closure(closure)
                .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
            let crate::CompBody::Source(source) = held.body()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let Some(matched_native_node) = core.computation(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let Computation::DataCase {
                ref motive,
                ref branches,
                ..
            } = *matched_native_node
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let zone = Zone::Intuitionistic;
            let deeper = binders
                .opened(zone)
                .ok_or(ReadbackFault::BinderCeiling { zone })?;
            let mut environment = held.environment().clone();
            let fresh = domain
                .neutral_node(
                    NeutralHead::Variable {
                        zone,
                        level: binders.fresh(zone),
                    },
                    Vec::new(),
                    Unfolding::Rigid,
                )
                .map_err(ReadbackFault::Domain)?;
            let bound = domain
                .value_neutral(fresh, TermFace::Reduced)
                .map_err(ReadbackFault::Domain)?;
            environment.extend(zone, bound);
            let frame = machine.hold_frame(environment);
            machine.tasks.push(onward);
            machine.tasks.push(Task::DataCase(source));
            for &branch in branches.iter().rev() {
                let environment = domain
                    .comp_closure(closure)
                    .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?
                    .environment()
                    .clone();
                let evaluated = crate::eval::eval_body_within(
                    core,
                    domain,
                    machine.definitions,
                    machine.fuel,
                    crate::CompBody::Source(branch),
                    environment,
                );
                let (comp, remaining) = evaluated.map_err(ReadbackFault::Eval)?;
                machine.fuel = remaining;
                machine.tasks.push(Task::Comp { comp, binders });
            }
            machine.tasks.push(Task::QuotedCompType {
                quoted: *motive,
                frame,
                binders: deeper,
            });
            Ok(())
        },
        Elimination::Split(closure) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let held = domain
                .comp_closure(closure)
                .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
            let crate::CompBody::Source(source) = held.body()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let Some(&Computation::Split {
                arity,
                motive,
                body,
                ..
            }) = core.computation(source)
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let environment = held.environment().clone();
            let opened_body = domain.comp_closure_node(body, environment.clone());
            let (opened, deeper) = open_many(core, domain, machine, opened_body, binders, arity)?;
            machine.tasks.push(onward);
            let read_body = Task::Comp {
                comp: opened,
                binders: deeper,
            };
            match motive {
                SplitMotive::Ambient => machine.tasks.extend([Task::Split(arity), read_body]),
                // A dependent split's motive reads back under one fresh
                // variable standing for the scrutinee, as a data case's does.
                SplitMotive::Scrutinee(motive) => {
                    let zone = Zone::Intuitionistic;
                    let under = binders
                        .opened(zone)
                        .ok_or(ReadbackFault::BinderCeiling { zone })?;
                    let fresh = domain
                        .neutral_node(
                            NeutralHead::Variable {
                                zone,
                                level: binders.fresh(zone),
                            },
                            Vec::new(),
                            Unfolding::Rigid,
                        )
                        .map_err(ReadbackFault::Domain)?;
                    let bound = domain
                        .value_neutral(fresh, TermFace::Reduced)
                        .map_err(ReadbackFault::Domain)?;
                    let mut extended = environment;
                    extended.extend(zone, bound);
                    let frame = machine.hold_frame(extended);
                    machine.tasks.extend([
                        Task::DependentSplit(arity),
                        read_body,
                        Task::QuotedCompType {
                            quoted: motive,
                            frame,
                            binders: under,
                        },
                    ]);
                },
            }
            Ok(())
        },
        Elimination::ListFold {
            element,
            result,
            on_nil,
            on_cons,
        } => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let closure = domain
                .comp_closure(on_nil)
                .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
            let frame = machine.hold_frame(closure.environment().clone());
            let empty = enter(core, domain, machine, on_nil, Entry::Bare)?;
            let (cell, deeper) = open_many(
                core,
                domain,
                machine,
                on_cons,
                binders,
                gandr_core_term::ComponentCount::from(2_usize),
            )?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::ListFold);
            machine.tasks.push(Task::Comp {
                comp: cell,
                binders: deeper,
            });
            machine.tasks.push(Task::Comp {
                comp: empty,
                binders,
            });
            machine.tasks.push(Task::QuotedValueType {
                quoted: result,
                frame,
                binders,
            });
            machine.tasks.push(Task::QuotedValueType {
                quoted: element,
                frame,
                binders,
            });
            Ok(())
        },
        Elimination::ListCase { on_nil, on_cons } => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let empty = enter(core, domain, machine, on_nil, Entry::Bare)?;
            let (cell, deeper) = open_many(
                core,
                domain,
                machine,
                on_cons,
                binders,
                gandr_core_term::ComponentCount::from(2_usize),
            )?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::ListCase);
            machine.tasks.push(Task::Comp {
                comp: cell,
                binders: deeper,
            });
            machine.tasks.push(Task::Comp {
                comp: empty,
                binders,
            });
            Ok(())
        },
        Elimination::Transport(value) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Transport);
            machine.tasks.push(Task::Value { value, binders });
            Ok(())
        },
        Elimination::ProductTransport(path) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::ProductTransport);
            machine.tasks.push(Task::Value {
                value: path,
                binders,
            });
            Ok(())
        },
        Elimination::PathTransport { motive, value } | Elimination::Ride { motive, value } => {
            let assemble = if matches!(elimination, Elimination::Ride { .. }) {
                Task::Ride
            }
            else {
                Task::PathTransport
            };
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let family = fresh_motive(domain, machine, motive, binders)?;
            machine.tasks.push(onward);
            machine.tasks.push(assemble);
            machine.tasks.push(Task::Value { value, binders });
            machine.tasks.push(family);
            Ok(())
        },
        // The operand is the head; the path or flow is read above it.
        Elimination::OperandTransport {
            motive,
            path: along,
        }
        | Elimination::OperandRide {
            motive,
            flow: along,
        } => {
            let assemble = if matches!(elimination, Elimination::OperandRide { .. }) {
                Task::OperandRide
            }
            else {
                Task::OperandTransport
            };
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let family = fresh_motive(domain, machine, motive, binders)?;
            machine.tasks.push(onward);
            machine.tasks.push(assemble);
            machine.tasks.push(Task::Value {
                value: along,
                binders,
            });
            machine.tasks.push(family);
            Ok(())
        },
        // The motive's arrows bind the telescope, so it is read back at the
        // spine's own depth.
        Elimination::TelescopeTransport {
            motive,
            start,
            over,
            value,
        } => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let held = domain
                .value_closure(motive)
                .ok_or(ReadbackFault::Domain(DomainFault::Dangling))?;
            let crate::ValueBody::CompType(telescope) = held.body()
            else {
                return Err(ReadbackFault::MachineInvariant);
            };
            let frame = machine.hold_frame(held.environment().clone());
            machine.tasks.push(onward);
            machine.tasks.push(Task::TelescopeTransport);
            for operand in [value, over, start] {
                machine.tasks.push(Task::Value {
                    value: operand,
                    binders,
                });
            }
            machine.tasks.push(Task::QuotedCompType {
                quoted: telescope,
                frame,
                binders,
            });
            Ok(())
        },
        Elimination::Force => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Force);
            Ok(())
        },
        Elimination::Apply(argument) => {
            expect_polarity(spine.polarity, Polarity::Computation, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Apply);
            machine.tasks.push(Task::Value {
                value: argument,
                binders,
            });
            Ok(())
        },
        Elimination::StaticApply(argument) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            machine
                .tasks
                .push(Task::Spine(spine.onward(Polarity::Value)));
            machine.tasks.push(Task::StaticApply);
            machine.tasks.push(Task::Value {
                value: argument,
                binders,
            });
            Ok(())
        },
        Elimination::Bind(body) => {
            expect_polarity(spine.polarity, Polarity::Computation, neutral)?;
            let opened = open(core, domain, machine, body, binders, Zone::Intuitionistic)?;
            let (whnf, deeper) = opened;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Bind);
            machine.tasks.push(Task::Comp {
                comp: whnf,
                binders: deeper,
            });
            Ok(())
        },
        Elimination::Case(branches) => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let count = domain
                .branches(branches)
                .map_err(ReadbackFault::Domain)?
                .len();
            let mut opened = Vec::with_capacity(count);
            for index in 0_usize .. count {
                let branch = domain
                    .branches(branches)
                    .ok()
                    .and_then(|held| held.get(index).copied())
                    .ok_or(ReadbackFault::MachineInvariant)?;
                opened.push(open(
                    core,
                    domain,
                    machine,
                    branch,
                    binders,
                    Zone::Intuitionistic,
                )?);
            }
            machine.tasks.push(onward);
            machine.tasks.push(Task::Case(opened.len()));
            for (comp, under) in opened.into_iter().rev() {
                machine.tasks.push(Task::Comp {
                    comp,
                    binders: under,
                });
            }
            Ok(())
        },
    }
}

#[cfg(test)]
mod tests;
