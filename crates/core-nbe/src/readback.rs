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
//! Readback resolves domain ids constantly and reads **no** core node: it mints
//! into the core arena and splices ids the domain already holds. So a
//! domain-arena miss arrives as [`ReadbackFault::Domain`] carrying the domain's
//! own refusal, and the only way a core-arena miss can arise is inside an
//! evaluation the readback drives — opening a closure or forcing a lowered
//! body — where it arrives as [`ReadbackFault::Eval`] carrying
//! [`EvalFault::DanglingTerm`]. Neither is translated into the other's
//! vocabulary.
//!
//! # Fuel, because readback drives evaluation
//!
//! Going under a binder evaluates the closure's body to weak head, and forcing
//! a body evaluates its lowering, so readback is a normalizer and inherits
//! every way normalization fails to stop. The machine carries a [`Fuel`]
//! budget, spends one unit per task it pops, and hands the remainder to each
//! evaluation it drives so the two share one budget rather than each holding
//! its own.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::Side;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::closure::Environment;
use crate::domain::BinderLevel;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::LiftTarget;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::eval_closed_value;
use crate::eval::eval_comp_within;
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
    #[inline]
    fn depth(
        self,
        zone: Zone,
    ) -> ZoneDepth
    {
        match zone {
            | Zone::Intuitionistic => self.intuitionistic,
            | Zone::Linear => self.linear,
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
            deeper.intuitionistic.0 == self.intuitionistic.0.saturating_add(1_u32)
                && deeper.linear.0 == self.linear.0
        },
        | (Zone::Linear, Some(deeper)) => {
            deeper.linear.0 == self.linear.0.saturating_add(1_u32)
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
            | Zone::Intuitionistic => Self {
                intuitionistic: deeper,
                linear: self.linear,
            },
            | Zone::Linear => Self {
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
    /// Every elimination is a computation eliminator, so whatever polarity the
    /// fold stood at before, it stands at computation polarity after one.
    ///
    /// # Specification
    /// - requires: nothing; a position past the spine's end is admissible and
    ///   ends the fold at the lookup.
    /// - ensures: the same neutral, wanted polarity, and open binders, the
    ///   position advanced by one, and computation polarity — for the reason
    ///   the paragraph above states.
    /// - provides: the one step the spine fold advances by, so no rule
    ///   recomputes the polarity an elimination leaves behind.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn onward(self) -> Self
    {
        Self {
            neutral: self.neutral,
            at: self.at.next(),
            polarity: Polarity::Computation,
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
    /// Assemble a pair from the two value terms its own tasks produced.
    Pair,
    /// Assemble a sum injection.
    Inject
    {
        /// The side injected into.
        side: Side,
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
    /// Assemble a returner from the value term on the stack.
    Return,
    /// Fold one more of a neutral's eliminations onto the term beneath it.
    Spine(SpineStep),
    /// Assemble a `force` over the value term on the stack.
    Force,
    /// Assemble an application over the computation and value terms.
    Apply,
    /// Assemble a bind over the two computation terms.
    Bind,
    /// Assemble a sum elimination over the value term and the two branches.
    Case,
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
    /// Assemble a product type from the two types on the stack.
    Product,
    /// Assemble a sum type from the two types on the stack.
    Sum,
    /// Assemble a thunk type from the computation type on the stack.
    ThunkType,
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
    /// Assemble a returner type from the value type on the stack.
    Returner,
    /// Assemble an arrow from the two types on the stacks.
    Arrow,
    /// Assemble a dependent arrow from the two types on the stacks.
    Pi,
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
        }
    }

    /// Hold an environment a quoted type is read in, and name it.
    ///
    /// # Specification
    /// trivial.
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
    /// - ensures: the most recent value type, which is no longer on the stack.
    /// - provides: the one read of the value-type result stack.
    /// - fails: [`ReadbackFault::MachineInvariant`] when the stack is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the stack was empty.
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
    /// - ensures: the most recent computation type, which is no longer on the
    ///   stack.
    /// - provides: the one read of the computation-type result stack.
    /// - fails: [`ReadbackFault::MachineInvariant`] when the stack is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ReadbackFault::MachineInvariant`] — the stack was empty.
    fn pop_comp_type(&mut self) -> Result<CompTypeId, ReadbackFault>
    {
        self.comp_types.pop().ok_or(ReadbackFault::MachineInvariant)
    }

    /// Pop one value result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent value term, which is no longer on the stack.
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
        ensures: |ret| ret.as_ref().ok().copied() == entry_last
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
    /// - ensures: the most recent computation term, which is no longer on the
    ///   stack.
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
        ensures: |ret| ret.as_ref().ok().copied() == entry_last
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
        | (ReadbackMode::ZeroUnfold, TermFace::Source(source)) => Some(source),
        | (ReadbackMode::ZeroUnfold, TermFace::Reduced) | (ReadbackMode::Unfolding, _) => None,
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
        | (ReadbackMode::ZeroUnfold, CompTermFace::Source(source)) => Some(source),
        | (ReadbackMode::ZeroUnfold, CompTermFace::Reduced) | (ReadbackMode::Unfolding, _) => None,
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
        | (Polarity::Value, Polarity::Value) | (Polarity::Computation, Polarity::Computation) => {
            Ok(())
        },
        | (Polarity::Value, Polarity::Computation) | (Polarity::Computation, Polarity::Value) => {
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
        | Entry::Bare => {},
        | Entry::Under { zone, bound } => environment.extend(zone, bound),
    }
    let evaluated = eval_comp_within(
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
///   when the level counts at or past the binders open in its zone.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::LevelOutOfScope`] — the level names no open binder.
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
})]
fn head_term(
    core: &mut CoreArena,
    head: NeutralHead,
    binders: OpenBinders,
) -> Result<ValueId, ReadbackFault>
{
    match head {
        | NeutralHead::Variable { zone, level } => {
            let Some(index) = binders.index(zone, level)
            else {
                return Err(ReadbackFault::LevelOutOfScope { zone, level });
            };
            Ok(core.value_variable(zone, index))
        },
        | NeutralHead::Constant(constant) | NeutralHead::Module(constant) => {
            Ok(core.value_constant(constant))
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
/// - witness: `readback_terms::readback_terms::an_unreduced_term_reads_back_as_the_id_it_was_evaluated_from`
/// - witness: `deep_readback::deep_readback::a_deep_value_reads_back_inside_a_small_stack`
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
/// - witness: `readback_terms::readback_terms::a_redex_normalizes_to_the_term_written_out_by_hand`
/// - witness: `readback_terms::readback_terms::a_redex_under_a_binder_normalizes_to_the_term_written_out_by_hand`
/// - witness: `readback_terms::readback_terms::a_case_that_fires_normalizes_to_the_branch_it_took`
/// - witness: `readback_terms::readback_terms::a_stuck_elimination_normalizes_to_the_spine_written_out_by_hand`
/// - witness: `deep_readback::deep_readback::a_deep_computation_reads_back_inside_a_small_stack`
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
/// - witness: `deep_readback::deep_readback::a_deep_value_reads_back_inside_a_small_stack`
/// - witness: `deep_readback::deep_readback::a_deep_computation_reads_back_inside_a_small_stack`
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
///   former plus one per assembly frame. This block stays prose: an assembly
///   frame pops its operands in the same step that pushes its result, so no
///   relation between the entry and exit stack lengths states that the result
///   is pushed on the stack of its own polarity, and the operand precondition
///   is a statement about the frame that popped the task.
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
fn step(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    task: Task,
) -> Result<(), ReadbackFault>
{
    match task {
        | Task::Value { value, binders } => step_value(core, domain, machine, value, binders),
        | Task::Comp { comp, binders } => step_comp(core, domain, machine, comp, binders),
        | Task::Pair => {
            let second = machine.pop_value()?;
            let first = machine.pop_value()?;
            machine.values.push(core.value_pair(first, second));
            Ok(())
        },
        | Task::Inject { side } => {
            let body = machine.pop_value()?;
            machine.values.push(core.value_injection(side, body));
            Ok(())
        },
        | Task::Lift { target } => {
            let body = machine.pop_value()?;
            let Some(held) = domain.level(target)
            else {
                return Err(ReadbackFault::Domain(DomainFault::Dangling));
            };
            let level = held.level().clone();
            machine.values.push(core.value_lift(level, body));
            Ok(())
        },
        | Task::Thunk => {
            let body = machine.pop_comp()?;
            machine.values.push(core.value_thunk(body));
            Ok(())
        },
        | Task::Lambda => {
            let body = machine.pop_comp()?;
            machine.comps.push(core.computation_lambda(body));
            Ok(())
        },
        | Task::Return => {
            let produced = machine.pop_value()?;
            machine.comps.push(core.computation_return(produced));
            Ok(())
        },
        | Task::Spine(spine) => step_spine(core, domain, machine, spine),
        | Task::Force => {
            let forced = machine.pop_value()?;
            machine.comps.push(core.computation_force(forced));
            Ok(())
        },
        | Task::Apply => {
            let argument = machine.pop_value()?;
            let head = machine.pop_comp()?;
            machine
                .comps
                .push(core.computation_application(head, argument));
            Ok(())
        },
        | Task::Bind => {
            let body = machine.pop_comp()?;
            let bound = machine.pop_comp()?;
            machine.comps.push(core.computation_bind(bound, body));
            Ok(())
        },
        | Task::Case => {
            let on_right = machine.pop_comp()?;
            let on_left = machine.pop_comp()?;
            let scrutinee = machine.pop_value()?;
            machine
                .comps
                .push(core.computation_case(scrutinee, on_left, on_right));
            Ok(())
        },
        | Task::QuotedValueType {
            quoted,
            frame,
            binders,
        } => step_quoted_value_type(core, domain, machine, quoted, frame, binders),
        | Task::QuotedCompType {
            quoted,
            frame,
            binders,
        } => step_quoted_comp_type(core, domain, machine, quoted, frame, binders),
        | Task::QuotedCode {
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
        | Task::Quote => {
            let quoted = machine.pop_value_type()?;
            machine.values.push(core.value_quote(quoted));
            Ok(())
        },
        | Task::QuoteComputation => {
            let quoted = machine.pop_comp_type()?;
            machine.values.push(core.value_quote_computation(quoted));
            Ok(())
        },
        | Task::Product => {
            let second = machine.pop_value_type()?;
            let first = machine.pop_value_type()?;
            machine
                .value_types
                .push(core.value_type_product(first, second));
            Ok(())
        },
        | Task::Sum => {
            let second = machine.pop_value_type()?;
            let first = machine.pop_value_type()?;
            machine.value_types.push(core.value_type_sum(first, second));
            Ok(())
        },
        | Task::ThunkType => {
            let body = machine.pop_comp_type()?;
            machine.value_types.push(core.value_type_thunk(body));
            Ok(())
        },
        | Task::LiftType { target } => {
            let inner = machine.pop_value_type()?;
            let level = held_level(domain, target)?;
            machine.value_types.push(core.value_type_lift(inner, level));
            Ok(())
        },
        | Task::Element { target } => {
            let code = machine.pop_value()?;
            let level = held_level(domain, target)?;
            machine
                .value_types
                .push(core.value_type_element(code, level));
            Ok(())
        },
        | Task::CompElement { target } => {
            let code = machine.pop_value()?;
            let level = held_level(domain, target)?;
            machine.comp_types.push(core.comp_type_element(code, level));
            Ok(())
        },
        | Task::Returner => {
            let result = machine.pop_value_type()?;
            machine.comp_types.push(core.comp_type_returner(result));
            Ok(())
        },
        | Task::Arrow => {
            let codomain = machine.pop_comp_type()?;
            let domain_type = machine.pop_value_type()?;
            machine
                .comp_types
                .push(core.comp_type_arrow(domain_type, codomain));
            Ok(())
        },
        | Task::Pi => {
            let codomain = machine.pop_comp_type()?;
            let domain_type = machine.pop_value_type()?;
            machine
                .comp_types
                .push(core.comp_type_pi(domain_type, codomain));
            Ok(())
        },
    }
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
/// leaf that holds no code is spliced as it stands, and a decode's code is
/// evaluated in the frame and read back, so a code that unfolds comes back as
/// what it unfolds to and a decode of a quote comes back as the quoted type.
///
/// # Specification
/// - requires: `frame` binds every variable `quoted` reads past its own
///   dependent arrows, and `binders` counts the binders open where it stands.
/// - ensures: a leaf pushes itself; a composite pushes its children's tasks and
///   its own assembly frame; a decode pushes its code's evaluation.
/// - provides: the value-type half of reading a quote back.
/// - fails: [`ReadbackFault::MachineInvariant`] when `quoted` does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ReadbackFault::MachineInvariant`] — the type does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — one case per former, separated by a quote of a leaf, a
///   quote whose decode unfolds, and a quote over a dependent arrow.
/// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
/// - witness: `readback::tests::a_quoted_decode_unfolds_to_the_quoted_type`
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
        .cloned()
        .ok_or(ReadbackFault::MachineInvariant)?;
    let at = |quoted: ValueTypeId| Task::QuotedValueType {
        quoted,
        frame,
        binders,
    };
    match node {
        | ValueType::Base(_)
        | ValueType::Unit
        | ValueType::Universe { .. }
        | ValueType::Abstract(_) => {
            machine.value_types.push(quoted);
        },
        | ValueType::Product(first, second) => {
            machine.tasks.push(Task::Product);
            machine.tasks.push(at(second));
            machine.tasks.push(at(first));
        },
        | ValueType::Sum(first, second) => {
            machine.tasks.push(Task::Sum);
            machine.tasks.push(at(second));
            machine.tasks.push(at(first));
        },
        | ValueType::Thunk(body) => {
            machine.tasks.push(Task::ThunkType);
            machine.tasks.push(Task::QuotedCompType {
                quoted: body,
                frame,
                binders,
            });
        },
        | ValueType::Lift { inner, target } => {
            let target = domain.hold_level(target);
            machine.tasks.push(Task::LiftType { target });
            machine.tasks.push(at(inner));
        },
        | ValueType::Element { code, target } => {
            let target = domain.hold_level(target);
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
        | CompType::Returner(result) => {
            machine.tasks.push(Task::Returner);
            machine.tasks.push(Task::QuotedValueType {
                quoted: result,
                frame,
                binders,
            });
        },
        | CompType::Arrow {
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
        | CompType::Pi {
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
        | CompType::Element { code, target } => {
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
///   seven-arm match, separated by a retained face, and by one case per arm —
///   the two leaves, the pair, the injection, the lift, the thunk, and the
///   neutral.
/// - witness: `readback::tests::an_unreduced_value_reads_back_as_its_own_source`
/// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
/// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
/// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
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
        | DomainValue::Unit { .. } => {
            machine.values.push(core.value_unit());
            Ok(())
        },
        | DomainValue::Literal { literal, .. } => {
            // The payload was never copied into the domain: the node names the
            // core value that holds it, and that id is valid whatever the face
            // says, so the readback splices it rather than rebuilding a literal
            // it would have to read back out of the same arena.
            machine.values.push(literal);
            Ok(())
        },
        | DomainValue::Pair { first, second, .. } => {
            machine.tasks.push(Task::Pair);
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
        | DomainValue::Injection { side, body, .. } => {
            machine.tasks.push(Task::Inject { side });
            machine.tasks.push(Task::Value {
                value: body,
                binders,
            });
            Ok(())
        },
        | DomainValue::Thunk { body, .. } => {
            let whnf = enter(core, domain, machine, body, Entry::Bare)?;
            machine.tasks.push(Task::Thunk);
            machine.tasks.push(Task::Comp {
                comp: whnf,
                binders,
            });
            Ok(())
        },
        | DomainValue::Lift { target, body, .. } => {
            machine.tasks.push(Task::Lift { target });
            machine.tasks.push(Task::Value {
                value: body,
                binders,
            });
            Ok(())
        },
        | DomainValue::Neutral { neutral, .. } => {
            step_neutral(core, domain, machine, neutral, Polarity::Value, binders)
        },
        | DomainValue::Code { code, .. } => {
            let Some(closure) = domain.value_closure(code)
            else {
                return Err(ReadbackFault::Domain(DomainFault::Dangling));
            };
            let body = closure.body();
            let frame = machine.hold_frame(closure.environment().clone());
            match core.value(body) {
                | Some(&Value::Quote(quoted)) => {
                    machine.tasks.push(Task::Quote);
                    machine.tasks.push(Task::QuotedValueType {
                        quoted,
                        frame,
                        binders,
                    });
                },
                | Some(&Value::QuoteComputation(quoted)) => {
                    machine.tasks.push(Task::QuoteComputation);
                    machine.tasks.push(Task::QuotedCompType {
                        quoted,
                        frame,
                        binders,
                    });
                },
                | Some(_) | None => return Err(ReadbackFault::MachineInvariant),
            }
            Ok(())
        },
    }
}

/// Perform one computation task: read one weak-head domain computation.
///
/// # Specification
/// - requires: `binders` counts the binders `comp` stands under.
/// - ensures: a retained face pushes the source id; a lambda opens its closure
///   and pushes the body's task under one more binder; a returner pushes its
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
///   three-arm match, separated by a retained face, a lambda, a returner and a
///   stuck head.
/// - witness: `readback::tests::an_unreduced_weak_head_reads_back_as_its_own_source`
/// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
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
        | DomainComp::Lambda { body, .. } => {
            let opened = open(core, domain, machine, body, binders, Zone::Intuitionistic)?;
            let (whnf, deeper) = opened;
            machine.tasks.push(Task::Lambda);
            machine.tasks.push(Task::Comp {
                comp: whnf,
                binders: deeper,
            });
            Ok(())
        },
        | DomainComp::Return { value, .. } => {
            machine.tasks.push(Task::Return);
            machine.tasks.push(Task::Value { value, binders });
            Ok(())
        },
        | DomainComp::Neutral { neutral, .. } => step_neutral(
            core,
            domain,
            machine,
            neutral,
            Polarity::Computation,
            binders,
        ),
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
/// - ensures: under a mode that spends nothing, the head is read as a value
///   term and the fold starts at value polarity. Under the spending mode, an
///   unforced unfolding is forced first; a forced unfolding then replaces the
///   head by the glued form it was forced to and the fold starts at that form's
///   polarity — which is the reading the unfolding face carries: the face names
///   the **head's** body, so the neutral's own value is that body with this
///   spine re-applied.
/// - provides: the one site the unfolding face is **spent**, and the site the
///   zero-unfold mode is defined by not spending it. Both modes read the face —
///   the read is one match on a `Copy` field and the mode's own arm is what
///   declines to act on it — and only the spending mode forces one. The clause
///   states the queued fold and, under the mode that spends nothing, the head
///   pushed as one value term; the polarity the fold starts at rides in the
///   queued task rather than in any stack state, and the witnesses below carry
///   it.
/// - fails: [`ReadbackFault::Domain`] when the neutral does not resolve,
///   whatever forcing an unforced body refuses —
///   [`ReadbackFault::UnloweredBody`] among it — and whatever reading the head
///   refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the mode-by-unfolding table and
///   the starting polarity, separated by each of the three unfolding states
///   under each mode, and by a body forced to each polarity.
/// - witness: `readback::tests::the_zero_unfold_mode_leaves_an_unforced_body_unforced`
/// - witness: `readback::tests::the_unfolding_mode_refuses_a_body_no_chain_entry_names`
/// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
/// - witness: `readback::tests::the_unfolding_mode_spends_a_body_already_forced`
/// - witness: `readback::tests::a_spine_that_misses_its_polarity_is_refused`
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| [
        ret.is_err() || machine.tasks.len() > entry_tasks,
        ret.is_err()
            || machine.mode != ReadbackMode::ZeroUnfold
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
        | ReadbackMode::ZeroUnfold => None,
        | ReadbackMode::Unfolding => match unfolding {
            | Unfolding::Rigid => None,
            | Unfolding::Unforced(body) => {
                let forced = force_body(core, domain, machine, neutral, body)?;
                Some(forced)
            },
            | Unfolding::Forced(glued) => Some(glued),
        },
    };
    let polarity = match spent {
        | None | Some(Glued::Value(_)) => Polarity::Value,
        | Some(Glued::Computation(_)) => Polarity::Computation,
    };
    machine.tasks.push(Task::Spine(SpineStep {
        neutral,
        at: SpineOffset::innermost(),
        polarity,
        wanted,
        binders,
    }));
    match spent {
        | None => {
            let term = head_term(core, head, binders)?;
            machine.values.push(term);
        },
        | Some(Glued::Value(value)) => machine.tasks.push(Task::Value { value, binders }),
        | Some(Glued::Computation(comp)) => machine.tasks.push(Task::Comp { comp, binders }),
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
///   computation polarity; an application and a bind keep it there.
/// - provides: the whole of "a neutral is a head with eliminations stacked on
///   it", read back as the applications, forces, binds and cases that could not
///   fire. The clause states that an exhausted spine queues nothing and an
///   unexhausted one queues at least one task, with both result stacks left as
///   they were; which operands and frames are queued, and in which order, are
///   judgements over the produced term, and the witnesses below carry them.
/// - fails: [`ReadbackFault::Domain`] when the neutral does not resolve,
///   [`ReadbackFault::NeutralPolarity`] when an elimination is stacked where
///   its operand's polarity is not what the fold holds or when the finished
///   fold does not stand at `wanted`, and whatever opening a branch refuses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the four elimination arms, the
///   per-arm polarity guard and the end guard, separated by a spine carrying
///   one of each elimination in a valid order, an application stacked at value
///   polarity, and a computation-position neutral with an empty spine.
/// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
/// - witness: `readback::tests::a_stuck_bind_and_case_read_back_their_branches`
/// - witness: `readback::tests::a_spine_that_misses_its_polarity_is_refused`
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
    let onward = Task::Spine(spine.onward());
    match elimination {
        | Elimination::Force => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Force);
            Ok(())
        },
        | Elimination::Apply(argument) => {
            expect_polarity(spine.polarity, Polarity::Computation, neutral)?;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Apply);
            machine.tasks.push(Task::Value {
                value: argument,
                binders,
            });
            Ok(())
        },
        | Elimination::Bind(body) => {
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
        | Elimination::Case { on_left, on_right } => {
            expect_polarity(spine.polarity, Polarity::Value, neutral)?;
            let opened = open(
                core,
                domain,
                machine,
                on_left,
                binders,
                Zone::Intuitionistic,
            )?;
            let (left, under_left) = opened;
            let opened = open(
                core,
                domain,
                machine,
                on_right,
                binders,
                Zone::Intuitionistic,
            )?;
            let (right, under_right) = opened;
            machine.tasks.push(onward);
            machine.tasks.push(Task::Case);
            machine.tasks.push(Task::Comp {
                comp: right,
                binders: under_right,
            });
            machine.tasks.push(Task::Comp {
                comp: left,
                binders: under_left,
            });
            Ok(())
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use core::convert::Infallible;

    use gandr_core_term::CompType;
    use gandr_core_term::Computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Transparency;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    use super::OpenBinders;
    use super::ReadbackFault;
    use super::ReadbackMode;
    use super::ZoneDepth;
    use super::read_comp_under;
    use super::read_value_under;
    use super::readback_computation;
    use super::readback_value;
    use crate::arena::DomainArena;
    use crate::arena::DomainCompId;
    use crate::arena::DomainFault;
    use crate::closure::Environment;
    use crate::domain::BinderLevel;
    use crate::domain::CompTermFace;
    use crate::domain::DomainComp;
    use crate::domain::DomainValue;
    use crate::domain::Elimination;
    use crate::domain::Glued;
    use crate::domain::NeutralHead;
    use crate::domain::TermFace;
    use crate::domain::Unfolding;
    use crate::eval::Definitions;
    use crate::eval::EvalFault;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_computation;
    use crate::eval::eval_value;

    /// Ample fuel for every case that is meant to finish.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a budget far above the step count any fixture below needs, so
    ///   an exhaustion refusal in one of them is a defect rather than a tight
    ///   budget.
    /// - provides: the budget every finishing case is run with; the
    ///   budget-sensitive cases name their own.
    /// - panics: none.
    fn ample() -> Fuel
    {
        Fuel::from(4_096_u32)
    }

    /// The index at the innermost binder.
    ///
    /// # Specification
    /// trivial.
    fn innermost() -> DeBruijnIndex
    {
        DeBruijnIndex::from(0_u32)
    }

    /// An empty chain and environment, which unfold nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an empty chain and an empty definitional environment, so
    ///   every constant reads as not manifest and no run unfolds.
    /// - provides: the definition side of every fixture that is about
    ///   rebuilding rather than unfolding.
    /// - panics: none.
    fn nothing_unfolds() -> (LoweredChain, DefinitionalEnvironment)
    {
        (LoweredChain::new(), DefinitionalEnvironment::new())
    }

    /// The number of bind links in the body each suspension of the
    /// shared-budget witness holds.
    ///
    /// It is the structural bound that witness measures against: the machine
    /// spends one unit of fuel per task and the body has this many bind nodes
    /// to visit, so evaluating it cannot cost fewer units than this under
    /// any accounting. Large enough that the handful of tasks one extra
    /// suspension costs the readback's *own* stack cannot be mistaken for
    /// it.
    const SUSPENDED_LINKS: u32 = 32_u32;

    /// A budget no case here needs, bounding the search for the least
    /// sufficient one so a machine that never finishes fails the search rather
    /// than running forever.
    const BUDGET_CEILING: u32 = 4_096_u32;

    /// `x ← …; return ⟨⟩` nested [`SUSPENDED_LINKS`] deep: a body whose
    /// evaluation visits at least that many nodes and whose weak head is one
    /// returner, so what it costs is large and what it produces is small.
    ///
    /// # Specification
    /// - requires: `core` is the arena the returned id will be read against.
    /// - ensures: a computation whose weak head is one returner and whose
    ///   evaluation visits at least [`SUSPENDED_LINKS`] bind nodes, so its cost
    ///   is large while its result is small.
    /// - provides: the body the shared-budget witness measures a suspension's
    ///   cost against.
    /// - panics: none.
    fn suspended_body(core: &mut CoreArena) -> ComputationId
    {
        let produced = core.value_unit();
        let mut sequenced = core.computation_return(produced);
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let pass_on = core.computation_return(occurrence);
        let mut remaining = SUSPENDED_LINKS;
        while remaining > 0_u32 {
            sequenced = core.computation_bind(sequenced, pass_on);
            remaining = remaining.saturating_sub(1_u32);
        }
        sequenced
    }

    /// Read `evaluated` back at `fuel`, discarding every core node the readback
    /// minted.
    ///
    /// The discard is [`CoreArena::truncate_to`] at a mark taken before the
    /// call, which is exactly the recovery [`readback_computation`] documents
    /// for a refusal — so the search below can run one weak head at many
    /// budgets without each attempt's leavings paying for the next.
    ///
    /// # Specification
    /// - requires: `core` and `domain` are the arenas `evaluated` was produced
    ///   against, and no core id minted after the entry mark is retained by the
    ///   caller.
    /// - ensures: on success the readback ran to completion at `fuel`; either
    ///   way `core` is truncated back to the mark taken before the call, so one
    ///   weak head can be read at many budgets without an attempt's leavings
    ///   paying for the next.
    /// - provides: the repeatable single attempt the budget search below is
    ///   built from.
    /// - fails: propagates the readback's own refusal unchanged, the exhaustion
    ///   one included, which is what the search reads as "not yet sufficient".
    /// - panics: none.
    ///
    /// [`CoreArena::truncate_to`]: gandr_core_term::CoreArena::truncate_to
    fn read_at(
        core: &mut CoreArena,
        domain: &mut DomainArena,
        definitions: Definitions<'_>,
        evaluated: DomainCompId,
        fuel: Fuel,
    ) -> Result<(), ReadbackFault>
    {
        let mark = core.watermark();
        let read = readback_computation(
            core,
            domain,
            definitions,
            ReadbackMode::Unfolding,
            fuel,
            evaluated,
        );
        core.truncate_to(mark);
        read.map(|_| ())
    }

    /// The least budget at which reading `evaluated` back succeeds, or `None`
    /// when [`BUDGET_CEILING`] does not suffice.
    ///
    /// Success is monotone in the budget — fuel only gates, and the machine is
    /// deterministic — so the first success the scan meets is the least one.
    ///
    /// # Specification
    /// - requires: `core` and `domain` are the arenas `evaluated` was produced
    ///   against.
    /// - ensures: the least budget at which the readback succeeds, and nothing
    ///   when no budget at or below [`BUDGET_CEILING`] does. The first success
    ///   is the least one for the monotonicity the paragraph above states.
    /// - provides: the measured cost the shared-budget witnesses compare.
    /// - fails: yields nothing at the ceiling, so a machine that never finishes
    ///   fails the search rather than running forever.
    /// - panics: none.
    fn least_sufficient(
        core: &mut CoreArena,
        domain: &mut DomainArena,
        definitions: Definitions<'_>,
        evaluated: DomainCompId,
    ) -> Option<Fuel>
    {
        let mut budget = 1_u32;
        while budget <= BUDGET_CEILING {
            let fuel = Fuel::from(budget);
            if read_at(core, domain, definitions, evaluated, fuel).is_ok() {
                return Some(fuel);
            }
            budget = budget.saturating_add(1_u32);
        }
        None
    }

    /// One binder open in the intuitionistic zone.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one binder open in the intuitionistic zone and none in the
    ///   linear one.
    /// - provides: the under-a-binder position the level and index fixtures
    ///   below are read at.
    /// - panics: never in practice — the first binder of a zone is far below
    ///   the depth ceiling, and the expectation names that reason.
    fn under_one() -> OpenBinders
    {
        OpenBinders::none()
            .opened(Zone::Intuitionistic)
            .expect("the first binder is far below the ceiling")
    }

    #[test]
    fn opening_a_binder_counts_one_zone_and_leaves_the_other()
    {
        let none = OpenBinders::none();
        assert_eq!(
            BinderLevel::from(0_u32),
            none.fresh(Zone::Intuitionistic),
            "the first binder of a zone takes level zero"
        );

        let structural = under_one();
        assert_eq!(
            BinderLevel::from(1_u32),
            structural.fresh(Zone::Intuitionistic),
            "the next binder of that zone takes the level after it"
        );
        assert_eq!(
            BinderLevel::from(0_u32),
            structural.fresh(Zone::Linear),
            "and the other zone is untouched, because the zones count separately"
        );

        let linear = none
            .opened(Zone::Linear)
            .expect("the first linear binder is far below the ceiling");
        assert_eq!(
            BinderLevel::from(0_u32),
            linear.fresh(Zone::Intuitionistic),
            "extending one zone did not deepen the other"
        );
        assert_eq!(BinderLevel::from(1_u32), linear.fresh(Zone::Linear));
    }

    #[test]
    fn the_binder_ceiling_is_refused_rather_than_reused()
    {
        let ceiling = OpenBinders {
            intuitionistic: ZoneDepth(u32::MAX),
            linear: ZoneDepth::default(),
        };
        assert_eq!(
            None,
            ceiling.opened(Zone::Intuitionistic),
            "a zone at the level ceiling cannot open another binder"
        );
        assert!(
            ceiling.opened(Zone::Linear).is_some(),
            "while the zone that is not at the ceiling still has room"
        );

        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let body = core.computation_return(produced);
        let lambda = core.computation_lambda(body);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
            .expect("a lambda is already a weak head");
        assert_eq!(
            Err(ReadbackFault::BinderCeiling {
                zone: Zone::Intuitionistic,
            }),
            read_comp_under(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                ample(),
                evaluated,
                ceiling,
            ),
            "and a lambda opened at the ceiling is refused rather than binding a second \
             variable at the ceiling level"
        );
    }

    #[test]
    fn a_level_becomes_the_index_counting_the_other_way()
    {
        let two = under_one()
            .opened(Zone::Intuitionistic)
            .expect("the second binder is far below the ceiling");
        assert_eq!(
            Some(DeBruijnIndex::from(1_u32)),
            two.index(Zone::Intuitionistic, BinderLevel::from(0_u32)),
            "the outermost of two binders is one index out"
        );
        assert_eq!(
            Some(innermost()),
            two.index(Zone::Intuitionistic, BinderLevel::from(1_u32)),
            "and the innermost is index zero, so the two orders are inverses"
        );
        assert_eq!(
            None,
            two.index(Zone::Intuitionistic, BinderLevel::from(2_u32)),
            "the first level at the depth names no open binder"
        );
        assert_eq!(
            None,
            two.index(Zone::Intuitionistic, BinderLevel::from(3_u32)),
            "nor does one past it"
        );
        assert_eq!(
            None,
            two.index(Zone::Linear, BinderLevel::from(0_u32)),
            "and a zone with nothing open binds no level at all"
        );
    }

    #[test]
    fn a_level_outside_the_open_binders_is_refused()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let level = BinderLevel::from(0_u32);
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level,
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a variable head mints rigid");
        let stood = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");

        assert_eq!(
            Err(ReadbackFault::LevelOutOfScope {
                zone: Zone::Intuitionistic,
                level,
            }),
            readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::ZeroUnfold,
                ample(),
                stood,
            ),
            "with no binder open, level zero names nothing and is refused rather than wrapped"
        );

        let read = read_value_under(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stood,
            under_one(),
        )
        .expect("one binder open answers level zero");
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            core.value(read),
            "and there it is the innermost index"
        );
    }

    #[test]
    fn an_unreduced_value_reads_back_as_its_own_source()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let pair = core.value_pair(first, second);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), pair)
            .expect("a closed pair of units evaluates");

        let mark = core.watermark();
        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("an unreduced pair reads back");
        assert_eq!(
            pair, read,
            "the face named the source node, so the readback answered with it"
        );
        assert_eq!(
            mark,
            core.watermark(),
            "and minted nothing, which is what reading back without rebuilding means"
        );
    }

    #[test]
    fn an_unreduced_weak_head_reads_back_as_its_own_source()
    {
        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let returner = core.computation_return(produced);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), returner)
            .expect("a closed returner evaluates");

        let mark = core.watermark();
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("an unreduced returner reads back");
        assert_eq!(
            returner, read,
            "the negative face is chosen the same way the positive one is"
        );
        assert_eq!(mark, core.watermark(), "and mints nothing either");
    }

    #[test]
    fn a_reduced_value_is_rebuilt_from_the_domain()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let held = core.value_unit();
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let pair = core.value_pair(bound, held);
        let body = core.computation_return(pair);
        let lambda = core.computation_lambda(body);
        let redex = core.computation_application(lambda, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), redex)
            .expect("the redex fires");
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };

        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            value,
        )
        .expect("a substituted pair reads back");
        assert_ne!(
            pair, read,
            "the source no longer denotes the value, so the pair was rebuilt"
        );
        assert_eq!(
            Some(&Value::Pair(argument, held)),
            core.value(read),
            "with the substituted child spliced by the id it denotes and the untouched child \
             by its own — in that order, so the assembly frame did not swap its operands"
        );
    }

    #[test]
    fn the_unfolding_mode_rebuilds_a_kept_face()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let pair = core.value_pair(first, second);
        let returner = core.computation_return(pair);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), returner)
            .expect("a closed returner evaluates");

        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the rebuilding mode reads it back");
        assert_ne!(
            returner, read,
            "the rebuilding mode ignores the face it was handed, on the negative side"
        );
        let Some(&Computation::Return(rebuilt)) = core.computation(read)
        else {
            panic!("the rebuilt weak head is a returner");
        };
        assert_ne!(
            pair, rebuilt,
            "and on the positive side, so a kept face buys nothing in this mode"
        );
        let Some(&Value::Pair(left, right)) = core.value(rebuilt)
        else {
            panic!("the rebuilt value is a pair");
        };
        assert_eq!(Some(&Value::Unit), core.value(left));
        assert_eq!(
            Some(&Value::Unit),
            core.value(right),
            "and both children came back as fresh nodes of the right shape"
        );
    }

    #[test]
    fn the_leaf_and_lift_arms_read_back_into_the_core_arena()
    {
        let mut core = CoreArena::new();
        let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let lifted = core.value_unit();
        let target = Level::zero().succ().expect("level one exists");
        let lift = core.value_lift(target.clone(), lifted);
        let pair = core.value_pair(literal, lift);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), pair)
            .expect("a pair of a literal and a lift evaluates");

        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the leaf and lift arms read back");
        let Some(&Value::Pair(first, second)) = core.value(read)
        else {
            panic!("the rebuilt value is a pair");
        };
        assert_eq!(
            literal, first,
            "the payload never left the core arena, so the literal arm splices the id \
             holding it rather than copying the payload out and back"
        );
        let Some(node) = core.value(second)
        else {
            panic!("the second component resolves");
        };
        let Value::Lift {
            target: ref held,
            body,
        } = *node
        else {
            panic!("the second component is a lift");
        };
        assert_eq!(
            &target, held,
            "the level came back out of the domain's own level table"
        );
        assert_eq!(
            Some(&Value::Unit),
            core.value(body),
            "and the lifted body was rebuilt under it"
        );
    }

    #[test]
    fn a_pair_and_an_injection_rebuild_from_their_children()
    {
        let mut core = CoreArena::new();
        let left_leaf = core.value_unit();
        let right_leaf = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let pair = core.value_pair(left_leaf, right_leaf);
        let injected = core.value_injection(Side::Right, pair);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), injected)
            .expect("an injection of a pair evaluates");

        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the composite arms read back");
        let Some(&Value::Injection(side, body)) = core.value(read)
        else {
            panic!("the rebuilt value is an injection");
        };
        assert_eq!(
            Side::Right,
            side,
            "the side rode through the frame rather than being defaulted"
        );
        let Some(&Value::Pair(first, second)) = core.value(body)
        else {
            panic!("the injected value is a pair");
        };
        assert_eq!(
            Some(&Value::Unit),
            core.value(first),
            "the unit is the first component"
        );
        assert_eq!(
            right_leaf, second,
            "and the literal the second, so the pair frame kept its operands in order"
        );
    }

    #[test]
    fn a_thunk_reads_back_through_the_body_it_suspends()
    {
        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let returner = core.computation_return(produced);
        let thunk = core.value_thunk(returner);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), thunk)
            .expect("a thunk over the empty environment evaluates");

        let retained = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("the retaining mode reads the thunk back");
        assert_eq!(
            thunk, retained,
            "the closure captured nothing, so the source thunk still denotes it and the \
             suspended body is never entered"
        );

        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the rebuilding mode reads the thunk back");
        let Some(&Value::Thunk(body)) = core.value(read)
        else {
            panic!("the rebuilt value is a thunk");
        };
        assert_ne!(
            returner, body,
            "the rebuilding mode entered the closure rather than answering with the source"
        );
        let Some(&Computation::Return(rebuilt)) = core.computation(body)
        else {
            panic!("the suspended body is a returner");
        };
        assert_eq!(
            Some(&Value::Unit),
            core.value(rebuilt),
            "and the body it evaluated to came back as its own term"
        );
    }

    #[test]
    fn a_lambda_reads_back_with_its_binder_as_an_index()
    {
        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let body = core.computation_return(occurrence);
        let lambda = core.computation_lambda(body);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
            .expect("a lambda is already a weak head");

        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the rebuilding mode opens the binder");
        let Some(&Computation::Lambda(rebuilt)) = core.computation(read)
        else {
            panic!("the rebuilt weak head is a lambda");
        };
        let Some(&Computation::Return(produced)) = core.computation(rebuilt)
        else {
            panic!("the body is a returner");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            core.value(produced),
            "the binder was opened at a level and the occurrence came back as the index \
             counting the other way"
        );
    }

    #[test]
    fn nested_binders_read_back_as_the_indices_that_name_them()
    {
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        for named in [0_u32, 1_u32] {
            let mut core = CoreArena::new();
            let occurrence = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(named));
            let body = core.computation_return(occurrence);
            let inner = core.computation_lambda(body);
            let outer = core.computation_lambda(inner);

            let mut domain = DomainArena::new();
            let evaluated = eval_computation(&core, &mut domain, definitions, ample(), outer)
                .expect("a lambda is already a weak head");
            let read = readback_computation(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                ample(),
                evaluated,
            )
            .expect("two binders open and close");

            let Some(&Computation::Lambda(under_outer)) = core.computation(read)
            else {
                panic!("the rebuilt weak head is a lambda");
            };
            let Some(&Computation::Lambda(under_inner)) = core.computation(under_outer)
            else {
                panic!("and so is its body");
            };
            let Some(&Computation::Return(produced)) = core.computation(under_inner)
            else {
                panic!("whose body is a returner");
            };
            assert_eq!(
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(named),
                }),
                core.value(produced),
                "each binder came back as the index that named it, so the two levels did \
                 not collapse onto one"
            );
        }
    }

    #[test]
    fn a_module_head_and_a_declaration_head_read_back_alike()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let position = ConstantIndex::from(2_usize);
        for head in [
            NeutralHead::Module(position),
            NeutralHead::Constant(position),
        ] {
            let neutral = domain
                .neutral_node(head, Vec::new(), Unfolding::Rigid)
                .expect("a rigid head mints without a body");
            let stood = domain
                .value_neutral(neutral, TermFace::Reduced)
                .expect("a spineless neutral stands in a value position");
            let read = readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::ZeroUnfold,
                ample(),
                stood,
            )
            .expect("a rigid head reads back");
            assert_eq!(
                Some(&Value::Constant(position)),
                core.value(read),
                "the core value vocabulary has one reference former, and one admission \
                 position admits one declaration, so the collapse loses nothing"
            );
        }
    }

    #[test]
    fn a_stuck_spine_reads_back_as_its_eliminations()
    {
        let mut core = CoreArena::new();
        let position = ConstantIndex::from(0_usize);
        let opaque = core.value_constant(position);
        let argument = core.value_unit();
        let forced = core.computation_force(opaque);
        let applied = core.computation_application(forced, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
            .expect("an eliminator over a rigid constant gets stuck");

        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("a stuck spine reads back");
        let Some(&Computation::Application(head, spliced)) = core.computation(read)
        else {
            panic!("the outermost elimination is the application");
        };
        assert_eq!(
            argument, spliced,
            "the argument kept its source face and was spliced rather than rebuilt"
        );
        let Some(&Computation::Force(thunked)) = core.computation(head)
        else {
            panic!("and the innermost is the force, so the spine folded innermost first");
        };
        assert_eq!(
            Some(&Value::Constant(position)),
            core.value(thunked),
            "over the head the spine was stacked on"
        );
        assert_ne!(
            opaque, thunked,
            "which was rebuilt from the neutral rather than spliced, because a stuck \
             computation carries no source face"
        );
    }

    #[test]
    fn a_stuck_bind_and_case_read_back_their_branches()
    {
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let position = ConstantIndex::from(0_usize);

        let mut core = CoreArena::new();
        let opaque = core.value_constant(position);
        let forced = core.computation_force(opaque);
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let continuation = core.computation_return(occurrence);
        let sequenced = core.computation_bind(forced, continuation);

        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), sequenced)
            .expect("a bind over a stuck computation gets stuck");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("a stuck bind reads back");
        let Some(&Computation::Bind(bound, body)) = core.computation(read)
        else {
            panic!("the outermost elimination is the bind");
        };
        assert!(
            matches!(core.computation(bound), Some(&Computation::Force(_))),
            "the bound computation is what the spine had beneath it"
        );
        let Some(&Computation::Return(produced)) = core.computation(body)
        else {
            panic!("the continuation is a returner");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            core.value(produced),
            "and the continuation's own binder was opened and closed again as an index"
        );

        let mut core = CoreArena::new();
        let opaque = core.value_constant(position);
        let taken = core.value_unit();
        let on_left = core.computation_return(taken);
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let on_right = core.computation_return(occurrence);
        let cased = core.computation_case(opaque, on_left, on_right);

        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased)
            .expect("a case over a stuck scrutinee gets stuck");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("a stuck case reads back");
        let Some(&Computation::Case {
            scrutinee,
            on_left: left,
            on_right: right,
        }) = core.computation(read)
        else {
            panic!("the elimination is the case");
        };
        assert_eq!(
            Some(&Value::Constant(position)),
            core.value(scrutinee),
            "the scrutinee is the stuck head the case could not fire on"
        );
        assert!(
            matches!(
                core.computation(left),
                Some(&Computation::Return(produced)) if matches!(core.value(produced), Some(&Value::Unit))
            ),
            "the left branch is the one that returns the unit"
        );
        let Some(&Computation::Return(produced)) = core.computation(right)
        else {
            panic!("the right branch is a returner");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            core.value(produced),
            "and the right branch is the one that reads its binder, so the two were not \
             swapped on the way out"
        );
    }

    #[test]
    fn a_spine_that_misses_its_polarity_is_refused()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let position = ConstantIndex::from(0_usize);

        let bare = domain
            .neutral_node(
                NeutralHead::Constant(position),
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a rigid declaration head mints");
        let stuck = domain.comp_neutral(bare, CompTermFace::Reduced);
        assert_eq!(
            Err(ReadbackFault::NeutralPolarity { neutral: bare }),
            readback_computation(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::ZeroUnfold,
                ample(),
                stuck,
            ),
            "a head with nothing stacked on it is a value, so it cannot stand where a \
             computation is expected"
        );

        let unit = domain.value_unit(TermFace::Reduced);
        let applied = domain
            .neutral_node(
                NeutralHead::Constant(position),
                Vec::from([Elimination::Apply(unit)]),
                Unfolding::Rigid,
            )
            .expect("a spined neutral mints");
        let stuck = domain.comp_neutral(applied, CompTermFace::Reduced);
        assert_eq!(
            Err(ReadbackFault::NeutralPolarity { neutral: applied }),
            readback_computation(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::ZeroUnfold,
                ample(),
                stuck,
            ),
            "and an application stacked straight onto a value head is refused rather than \
             folded over whatever the computation stack happened to hold"
        );
    }

    #[test]
    fn the_zero_unfold_mode_leaves_an_unforced_body_unforced()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let position = ConstantIndex::from(0_usize);
        let body = GlobalIndex::from(9_u32);
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(position),
                Vec::new(),
                Unfolding::Unforced(body),
            )
            .expect("a declaration head may carry a body");
        let stood = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");

        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stood,
        )
        .expect("the zero-unfold mode reads the neutral form");
        assert_eq!(
            Some(&Value::Constant(position)),
            core.value(read),
            "the neutral form is the answer, whatever the unfolding face holds"
        );
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert_eq!(
            Unfolding::Unforced(body),
            held.unfolding(),
            "and the body is still unforced when the readback returns, which is the \
             property a conversion comparing neutral forms stands on"
        );
    }

    #[test]
    fn the_unfolding_mode_refuses_a_body_no_chain_entry_names()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let body = GlobalIndex::from(9_u32);
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::new(),
                Unfolding::Unforced(body),
            )
            .expect("a declaration head may carry a body");
        let stood = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");

        assert_eq!(
            Err(ReadbackFault::UnloweredBody { body }),
            readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                ample(),
                stood,
            ),
            "the spending mode declines a body no entry of the run's chain names rather \
             than answering the neutral form under a mode that promised to unfold it"
        );
    }

    #[test]
    fn the_unfolding_mode_spends_a_body_already_forced()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let position = ConstantIndex::from(0_usize);
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(position),
                Vec::new(),
                Unfolding::Unforced(GlobalIndex::from(9_u32)),
            )
            .expect("a declaration head may carry a body");
        let stood = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");
        let unfolded = domain.value_unit(TermFace::Reduced);
        assert_eq!(
            Ok(()),
            domain.force_neutral(neutral, Glued::Value(unfolded)),
            "the body is forced by the caller, because lowering it is not this crate's job"
        );

        let retained = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stood,
        )
        .expect("the zero-unfold mode reads the neutral form");
        assert_eq!(
            Some(&Value::Constant(position)),
            core.value(retained),
            "the zero-unfold mode still answers the neutral form, even where a body has \
             been forced"
        );

        let spent = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            stood,
        )
        .expect("the spending mode reads the unfolded body");
        assert_eq!(
            Some(&Value::Unit),
            core.value(spent),
            "while the spending mode answers with the body it was forced to"
        );
    }

    #[test]
    fn a_lowered_definition_body_unfolds_through_readback()
    {
        let mut core = CoreArena::new();
        let inner = ConstantIndex::from(0_usize);
        let outer = ConstantIndex::from(1_usize);
        let inner_entry = GlobalIndex::from(3_u32);
        let outer_entry = GlobalIndex::from(7_u32);

        // `inner := ⟨⟩` and `outer := (inner, ⟨⟩)`, both lowered into `core`.
        let unit = core.value_unit();
        let mention = core.value_constant(inner);
        let outer_body = core.value_pair(mention, unit);
        let reference = core.value_constant(outer);

        let mut chain = DefinitionChain::new();
        let defined = chain.define(inner, inner_entry, Transparency::Manifest, &[]);
        assert!(defined.is_ok());
        let defined = chain.define(outer, outer_entry, Transparency::Manifest, &[inner]);
        assert!(defined.is_ok());
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let chain = LoweredChain::lower(chain, |entry| match entry.constant() {
            | position if position == inner => Ok(unit),
            | position if position == outer => Ok(outer_body),
            | position => Err(position),
        })
        .expect("both bodies lower");
        let definitions = Definitions::new(&chain, &environment, scope);

        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), reference)
            .expect("a constant evaluates to a neutral");
        let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
        else {
            panic!("a manifest constant is stuck until a readback spends it");
        };

        let kept = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("the zero-unfold mode reads the neutral form");
        assert_eq!(
            Some(&Value::Constant(outer)),
            core.value(kept),
            "a held lowering changes nothing for the mode that spends nothing"
        );

        let before = domain.watermark();
        let mut marks = [before; 2];
        for (attempt, mark) in ["first", "second"].into_iter().zip(marks.iter_mut()) {
            let unfolded = readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                ample(),
                evaluated,
            )
            .expect("the spending mode forces both lowered bodies");
            let Some(&Value::Pair(first, second)) = core.value(unfolded)
            else {
                panic!("the {attempt} reading is the outer body's pair");
            };
            assert_ne!(
                outer_body, unfolded,
                "the {attempt} reading is rebuilt from the domain rather than spliced from \
                 the lowering's id"
            );
            assert_eq!(
                (Some(&Value::Unit), Some(&Value::Unit)),
                (core.value(first), core.value(second)),
                "and in the {attempt} reading the inner constant unfolded too, through its \
                 own lowering"
            );
            let held = domain.neutral(neutral).expect("the neutral resolves");
            assert!(
                matches!(held.unfolding(), Unfolding::Forced(Glued::Value(_))),
                "the force is recorded on the neutral, not discarded with the readback"
            );
            *mark = domain.watermark();
        }
        let [first_mark, second_mark] = marks;
        assert_ne!(
            before, first_mark,
            "the first reading evaluated the lowered bodies"
        );
        assert_eq!(
            first_mark, second_mark,
            "and the second reading evaluates neither body again"
        );
    }

    #[test]
    fn a_quote_reads_back_through_its_environment()
    {
        // `λ. return ⌜El(#0)⌝`: the quote reads the lambda's binder.
        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let decoded = core.value_type_element(occurrence, Level::zero());
        let quote = core.value_quote(decoded);
        let returned = core.computation_return(quote);
        let lambda = core.computation_lambda(returned);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
            .expect("a lambda is already a weak head");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the lambda reads back");

        let Some(&Computation::Lambda(body)) = core.computation(read)
        else {
            panic!("the rebuilt computation is a lambda");
        };
        let Some(&Computation::Return(value)) = core.computation(body)
        else {
            panic!("its body is a returner");
        };
        assert_ne!(quote, value, "the quote was rebuilt, not spliced");
        let Some(&Value::Quote(quoted)) = core.value(value)
        else {
            panic!("the returned value is a quote");
        };
        let Some(&ValueType::Element { code, ref target }) = core.value_type(quoted)
        else {
            panic!("the quoted type is a decode");
        };
        assert_eq!(&Level::zero(), target, "at the level it was written at");
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            core.value(code),
            "and its code is the lambda's binder again, read through the quote's environment"
        );
    }

    #[test]
    fn a_quoted_decode_unfolds_to_the_quoted_type()
    {
        // `code := ⌜Unit⌝`, and the quote `⌜El(code)⌝` reads it.
        let mut core = CoreArena::new();
        let code = ConstantIndex::from(0_usize);
        let unit = core.value_type_unit();
        let body = core.value_quote(unit);
        let mention = core.value_constant(code);
        let decoded = core.value_type_element(mention, Level::zero());
        let quote = core.value_quote(decoded);

        let mut chain = DefinitionChain::new();
        let defined = chain.define(code, GlobalIndex::from(0_u32), Transparency::Manifest, &[]);
        assert!(defined.is_ok());
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let chain = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(body))
            .unwrap_or_else(|never| match never {});
        let definitions = Definitions::new(&chain, &environment, scope);

        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), quote)
            .expect("a closed quote evaluates");
        let kept = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("the zero-unfold mode reads the quote");
        assert_eq!(quote, kept, "a closed quote still denotes its source");

        let unfolded = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the unfolding mode reads the quote");
        let Some(&Value::Quote(quoted)) = core.value(unfolded)
        else {
            panic!("the read value is a quote");
        };
        assert_eq!(
            Some(&ValueType::Unit),
            core.value_type(quoted),
            "the decode's code unfolded to a quote, and decoding it on mint left the quoted type"
        );
    }

    #[test]
    fn a_quoted_dependent_arrow_reads_its_binder_as_an_index()
    {
        // `λ. return ⌜Thunk(Π(_ : El(#0)). El(#0) ⊸ El(#1))⌝`, written with
        // the codomain's `#1` naming the lambda's binder past the arrow's.
        let mut core = CoreArena::new();
        let outer = core.value_variable(Zone::Intuitionistic, innermost());
        let from = core.value_type_element(outer, Level::zero());
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let near = core.value_type_element(bound, Level::zero());
        let past = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let far = core.comp_type_element(past, Level::zero());
        let arrow = core.comp_type_arrow(near, far);
        let pi = core.comp_type_pi(from, arrow);
        let thunk = core.value_type_thunk(pi);
        let quote = core.value_quote(thunk);
        let returned = core.computation_return(quote);
        let lambda = core.computation_lambda(returned);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
            .expect("a lambda is already a weak head");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the lambda reads back");

        let Some(&Computation::Lambda(body)) = core.computation(read)
        else {
            panic!("a lambda");
        };
        let Some(&Computation::Return(value)) = core.computation(body)
        else {
            panic!("returning");
        };
        let Some(&Value::Quote(quoted)) = core.value(value)
        else {
            panic!("a quote");
        };
        let Some(&ValueType::Thunk(suspended)) = core.value_type(quoted)
        else {
            panic!("of a thunk type");
        };
        let Some(&CompType::Pi {
            domain: read_from,
            codomain,
        }) = core.comp_type(suspended)
        else {
            panic!("over a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain: read_near,
            codomain: read_far,
        }) = core.comp_type(codomain)
        else {
            panic!("whose codomain is an arrow");
        };
        let code_of_value = |core: &CoreArena, ty| match core.value_type(ty) {
            | Some(&ValueType::Element { code, .. }) => core.value(code).cloned(),
            | _ => None,
        };
        let variable = |index: u32| {
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index),
            })
        };
        assert_eq!(
            variable(0_u32),
            code_of_value(&core, read_from),
            "outside the arrow's binder, the lambda's is innermost"
        );
        assert_eq!(
            variable(0_u32),
            code_of_value(&core, read_near),
            "inside it, the arrow's own binder is innermost"
        );
        let Some(&CompType::Element { code: far_code, .. }) = core.comp_type(read_far)
        else {
            panic!("the arrow's codomain is a decode");
        };
        assert_eq!(
            variable(1_u32).as_ref(),
            core.value(far_code),
            "and the lambda's binder is one further out, so the fresh variable the readback \
             opened for the arrow counts as a binder"
        );
    }

    #[test]
    fn a_readback_declines_on_fuel_rather_than_running_on()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let pair = core.value_pair(first, second);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), pair)
            .expect("a closed pair of units evaluates");

        assert_eq!(
            Err(ReadbackFault::OutOfFuel),
            readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                Fuel::from(2_u32),
                evaluated,
            ),
            "rebuilding the pair takes four tasks, so a budget of two runs out on the \
             readback's own stack"
        );

        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let inner_force = core.computation_force(occurrence);
        let self_application = core.computation_application(inner_force, occurrence);
        let looping = core.computation_lambda(self_application);
        let looper = core.value_thunk(looping);
        let outer_force = core.computation_force(looper);
        let omega = core.computation_application(outer_force, looper);
        let suspended = core.computation_lambda(omega);

        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), suspended)
            .expect("a lambda is already a weak head, whatever its body does");
        assert_eq!(
            Err(ReadbackFault::Eval(EvalFault::OutOfFuel)),
            readback_computation(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                Fuel::from(500_u32),
                evaluated,
            ),
            "and opening a binder over a body that loops exhausts the same budget inside \
             the evaluation, which says so under evaluation's own name"
        );
    }

    #[test]
    fn one_budget_bounds_the_readback_and_the_evaluations_it_drives()
    {
        // Two terms differing only in how many suspensions of the *same* body
        // the readback must enter: `return ⟨thunk B⟩` drives one evaluation of
        // B, and `return ⟨(thunk B, thunk B)⟩` drives two.
        //
        // Under one shared budget the second costs the first plus a whole
        // evaluation of B. Under a budget handed fresh to each driven
        // evaluation it costs the first plus only the few tasks the extra
        // suspension takes on the readback's own stack — however large B is —
        // because each evaluation would receive the whole budget again. So the
        // gap between the two least sufficient budgets is what separates the
        // two accountings, and B's own link count is the structural bound the
        // gap is measured against rather than a number read off a run.
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        let body = suspended_body(&mut core);
        let only = core.value_thunk(body);
        let one_suspension = core.computation_return(only);

        let body = suspended_body(&mut core);
        let first = core.value_thunk(body);
        let body = suspended_body(&mut core);
        let second = core.value_thunk(body);
        let both = core.value_pair(first, second);
        let two_suspensions = core.computation_return(both);

        // Evaluation is not what the budgets below are about, so it runs once
        // with fuel to spare and the search reads its weak head back many
        // times. Both weak heads are one returner over suspensions evaluation
        // never entered, which is why the whole cost lands on the readback.
        let mut domain = DomainArena::new();
        let evaluated_one =
            eval_computation(&core, &mut domain, definitions, ample(), one_suspension)
                .expect("a returner over one suspension has a weak head");
        let evaluated_two =
            eval_computation(&core, &mut domain, definitions, ample(), two_suspensions)
                .expect("a returner over a pair of suspensions has a weak head");

        let one = least_sufficient(&mut core, &mut domain, definitions, evaluated_one)
            .expect("one suspension fits below the search ceiling");
        let two = least_sufficient(&mut core, &mut domain, definitions, evaluated_two)
            .expect("two suspensions fit below the search ceiling");
        let gap = u32::from(two)
            .checked_sub(u32::from(one))
            .expect("a second suspension cannot make the readback cheaper");
        assert!(
            gap >= SUSPENDED_LINKS,
            "the second suspension cost a whole evaluation of its body, which is at least \
             one unit per bind link; a budget handed fresh to each driven evaluation would \
             have charged only the few tasks the suspension itself takes"
        );

        assert_eq!(
            Err(ReadbackFault::OutOfFuel),
            read_at(
                &mut core,
                &mut domain,
                definitions,
                evaluated_two,
                Fuel::from(u32::from(two).saturating_sub(1_u32)),
            ),
            "one unit short of sufficient, the last task of the readback's own stack cannot \
             run"
        );

        assert_eq!(
            Err(ReadbackFault::Eval(EvalFault::OutOfFuel)),
            read_at(
                &mut core,
                &mut domain,
                definitions,
                evaluated_two,
                Fuel::from(u32::from(one).saturating_add(1_u32)),
            ),
            "and one unit past what a single suspension needs, the shared budget reaches the \
             second suspension's evaluation with nothing left to spend inside it — which is \
             the reading a fresh budget per driven evaluation could not produce, because it \
             would hand that evaluation the whole budget over again"
        );
    }

    #[test]
    fn a_value_from_another_domain_arena_is_refused()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        let mut other = DomainArena::new();
        let mut stranger = other.value_unit(TermFace::Reduced);
        let mut remaining = 8_usize;
        while remaining > 0 {
            stranger = other.value_pair(stranger, stranger, TermFace::Reduced);
            remaining = remaining.saturating_sub(1_usize);
        }

        let mut domain = DomainArena::new();
        let _padding = domain.value_unit(TermFace::Reduced);
        assert_eq!(
            Err(ReadbackFault::Domain(DomainFault::Dangling)),
            readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::ZeroUnfold,
                ample(),
                stranger,
            ),
            "a domain id minted by one arena names no node of another, and the refusal \
             names the domain arena rather than blaming the core one"
        );
    }

    #[test]
    fn an_opened_closure_reports_the_evaluations_own_fault()
    {
        let mut core = CoreArena::new();
        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        let mut other = CoreArena::new();
        let produced = other.value_unit();
        let mut stranger = other.computation_return(produced);
        let mut remaining = 8_usize;
        while remaining > 0 {
            stranger = other.computation_bind(stranger, stranger);
            remaining = remaining.saturating_sub(1_usize);
        }

        let mut domain = DomainArena::new();
        let closure = domain.comp_closure_node(stranger, Environment::new());
        let thunk = domain.value_thunk(closure, TermFace::Reduced);
        assert_eq!(
            Err(ReadbackFault::Eval(EvalFault::DanglingTerm)),
            readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::ZeroUnfold,
                ample(),
                thunk,
            ),
            "the core-arena miss reaches a readback only through the evaluation an opened \
             closure drives, and it arrives under that machine's own name"
        );
    }

    #[test]
    fn a_manifest_definition_reads_back_as_the_reference_it_came_from()
    {
        let mut core = CoreArena::new();
        let position = ConstantIndex::from(0_usize);
        let reference = core.value_constant(position);
        let unfolded = core.value_unit();

        let mut chain = DefinitionChain::new();
        let body = GlobalIndex::from(9_u32);
        let defined = chain.define(position, body, Transparency::Manifest, &[]);
        assert_eq!(Ok(()), defined.map(|_| ()), "the definition is admitted");
        let chain =
            LoweredChain::lower(chain, |_| Ok::<_, Infallible>(unfolded)).expect("the body lowers");
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), reference)
            .expect("a constant evaluates to a neutral");
        let mark = core.watermark();
        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("the zero-unfold mode reads it back");
        assert_eq!(
            reference, read,
            "an evaluated constant keeps its source face, so the readback answers with \
             the reference rather than rebuilding one"
        );
        assert_eq!(mark, core.watermark(), "and mints nothing to do it");
    }
}
