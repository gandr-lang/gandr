//! The **defunctionalized checking machine**: bidirectional type checking that
//! re-derives every obligation and grants the producer no credence.
//!
//! # Bidirectional, annotation-free
//!
//! Terms carry no type annotations, so checking is bidirectional. The
//! introductions — lambda, injection, pair, thunk, return — **check** against
//! an expected type flowing down from the declaration's declared type; the
//! eliminators and atoms — variable, constant, application, force, bind, case,
//! literal, lift — **synthesize** a type flowing up. A synthesizing term used
//! where a type is expected triggers a conversion at the mode switch. This
//! needs no metavariable and no inference.
//!
//! # Arena-native: ids, never owned types
//!
//! Every type the machine touches is a `Copy` id into the environment's arena:
//! the declared type, a context slot, a synthesized type, an expected type
//! flowing into a check. Eliminating a type former is a read of its child ids.
//! Synthesized types are minted into the arena as checker intermediates, which
//! the admission choke point truncates after the verdict.
//!
//! # Terms live in types, and four rules change because of it
//!
//! The universe-decoding former carries a value, so a type can mention a bound
//! variable. Four consequences are load-bearing here and each is one arm:
//!
//! - **A context slot is no longer closed.** A slot was recorded against the
//!   context prefix that preceded it, so a variable synthesis raises it past
//!   the binders between the slot and the use site before returning it.
//! - **An application substitutes into the codomain.** At a dependent head the
//!   codomain is instantiated at the argument rather than produced as it
//!   stands.
//! - **The formation walk carries a context.** A dependent arrow's codomain is
//!   formed under the domain's binder, so the walk pushes and pops slots
//!   exactly as the checking machine does.
//! - **The formation walk owes obligations it cannot discharge.** Deciding a
//!   code's type is the checking machine's job, and having formation call it
//!   would make the two walks mutually recursive. Formation records what it
//!   owes; [`drain_code_obligations`] drains the record through the checking
//!   machine; and a check that owes more codes appends to the same worklist.
//!   **Neither walk reaches the other**, and the drain is a loop with a ceiling
//!   rather than an open recursion.
//!
//! # Totality by defunctionalization, with no depth budget
//!
//! The checker runs as an explicit machine over a goal register, a produced
//! register, a heap frame stack, and an explicit typing-context stack — never
//! mutually recursive methods bounded by a depth budget — so it is total on
//! adversarial depth, which matters because decode can build an arbitrarily
//! deep term from bytes. Type formation is its own iterative walk the machine
//! calls directly, as it calls the already-iterative conversion.
//!
//! # Correspondence: recursive arm to machine step
//!
//! This table is the trusted-base audit artifact. Each arm of the recursive
//! presentation the machine replaces maps to exactly one goal expansion plus,
//! for a multi-child arm, one continuation frame. A reviewer confirms the
//! machine **is** the judgement by walking it.
//!
//! | recursive arm                          | goal push                    | frames                                              |
//! | -------------------------------------- | ---------------------------- | --------------------------------------------------- |
//! | `value_type_level` Base / Unit         | leaf, level zero             | —                                                   |
//! | `value_type_level` Universe            | leaf, scope then successor   | —                                                   |
//! | `value_type_level` Abstract            | leaf, kind lookup            | —                                                   |
//! | `value_type_level` Element             | leaf, level read, code owed  | —                                                   |
//! | `value_type_level` Product / Sum       | `ValueLevel(first)`          | `MaxSecondValue`, then `MaxWith`                    |
//! | `value_type_level` Thunk               | `CompLevel(body)`            | — (the level passes through)                        |
//! | `value_type_level` Lift                | `ValueLevel(inner)`          | `LiftCheck`                                         |
//! | `comp_type_level` Returner             | `ValueLevel(result)`         | — (the level passes through)                        |
//! | `comp_type_level` Arrow                | `ValueLevel(domain)`         | `MaxSecondComp`, then `MaxWith`                     |
//! | `comp_type_level` Pi                   | `ValueLevel(domain)`         | `MaxSecondCompUnder`, `ScopeExit`, then `MaxWith`   |
//! | `synth_value` Var                      | leaf, slot lookup then shift | —                                                   |
//! | `synth_value` Const / Unit / Lit       | leaf, resolve or mint        | —                                                   |
//! | `synth_value` Pair                     | `SynthValue(first)`          | `SynthPairFirst`, then `SynthPairSecond`            |
//! | `synth_value` Thunk                    | `SynthComp(body)`            | `SynthThunk`                                        |
//! | `synth_value` Lift                     | `SynthValue(body)`           | `SynthLift`                                         |
//! | `synth_value` Injection                | leaf, not inferable          | —                                                   |
//! | `check_value` Injection                | `CheckValue(body, summand)`  | —                                                   |
//! | `check_value` Pair                     | `CheckValue(first, first_t)` | `CheckPairSecond`                                   |
//! | `check_value` Thunk                    | `CheckComp(body, codomain)`  | —                                                   |
//! | `check_value` synth fallthrough        | `SynthValue(value)`          | `ConvertValue`                                      |
//! | `synth_comp` Application, Arrow head   | `SynthComp(head)`            | `SynthApply`, then `ProduceComp`                    |
//! | `synth_comp` Application, Pi head      | `SynthComp(head)`            | `SynthApply`, then `ProduceComp` at the instance    |
//! | `synth_comp` Force                     | `SynthValue(value)`          | `SynthForce`                                        |
//! | `synth_comp` Return                    | `SynthValue(value)`          | `SynthReturn`                                       |
//! | `synth_comp` Bind                      | `SynthComp(bound)`           | `SynthBind`, `ScopeExit`                            |
//! | `synth_comp` Case                      | `SynthValue(scrutinee)`      | `SynthCaseScrutinee` / `AfterLeft` / `AfterRight`, `ScopeExit` |
//! | `synth_comp` Lambda                    | leaf, not inferable          | —                                                   |
//! | `check_comp` Lambda, Arrow / Pi        | `CheckComp(body, codomain)`  | `ScopeExit`                                         |
//! | `check_comp` Return                    | `CheckValue(value, result)`  | —                                                   |
//! | `check_comp` Bind                      | `SynthComp(bound)`           | `CheckBind`, `ScopeExit`                            |
//! | `check_comp` Case                      | `SynthValue(scrutinee)`      | `CheckCaseScrutinee` / `AfterLeft`, `ScopeExit`     |
//! | `check_comp` synth fallthrough         | `SynthComp(computation)`     | `ConvertComp`                                       |
//!
//! **The `Element` row is the one arm that answers without descending.** It
//! reads the level off the node and records the code obligation; it pushes no
//! goal and holds no frame, because the code is a *term* and the formation walk
//! decides no term. The obligation leaves this table and re-enters it at
//! [`drain_code_obligations`], which starts a fresh `CheckValue` goal against
//! the universe the node named — one loop below the two machines rather than a
//! step inside either.
//!
//! # The memo is the default path on **both** machines
//!
//! Admitting one declaration runs two iterative machines over the shared graph:
//! this module's goal loop over the body, and [`type_level`]'s formation walk
//! over the declared type. Both consult the memo. A memo covering only the term
//! half would ship a small constant against an exponential capability, because
//! type formation would keep expanding once per occurrence.
//!
//! The memo is reached through a statically dispatched seam whose activity is
//! an associated constant, so the memoless path is **the same function at a
//! different type parameter** rather than a second implementation — which is
//! what makes the differential a genuine one and what makes the memoless path a
//! permanent rollback target rather than dead code.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::OrderedMemo;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::Side;
use gandr_kernel_term::TableEntryCount;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::census::ExpansionCensus;
use crate::census::ExpansionKind;
use crate::conv::Convertibility;
use crate::conv::case_branch_mismatch;
use crate::conv::convert_comp_type;
use crate::conv::convert_value_type;
use crate::conv::convertible_comp_types;
use crate::encoding::SupportGoal;
use crate::env::AdmittedDeclaration;
use crate::env::projected_atoms;
use crate::error::ExpectedComputationShape;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::error::NonInferableForm;
use crate::error::RegisterFault;
use crate::levels::LevelContext;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_comp_type;
use crate::support::NodeOutcome;
use crate::support::NodeSupport;
use crate::support::SupportContext;
use crate::support::SupportPlane;
use crate::witness::comp_type_witness;
use crate::witness::value_type_witness;

/// The memo an unsupplied check builds for itself: the default path.
pub type DefaultMemo = OrderedMemo<NodeSupport, NodeOutcome>;

/// Resolve a value id, or the fail-closed arena fault.
///
/// The clone is shallow — a node's children are `Copy` ids — so it costs a
/// constant and releases the arena borrow before synthesis mints into it.
///
/// # Specification
/// - requires: nothing; an id that resolves to nothing is admissible input and
///   is refused.
/// - ensures: a shallow clone of the node at `id`, which releases the arena
///   borrow before synthesis mints into it.
/// - provides: the fail-closed read every value rule goes through.
/// - fails: `KernelError::ArenaFault` for an id that resolves to no node, so a
///   resolution defect rejects the declaration rather than proceeding on a
///   fabricated node.
/// - panics: none.
#[inline]
fn read_value(
    arena: &TermArena,
    id: ValueId,
) -> Result<Value, KernelError>
{
    arena.value(id).cloned().ok_or(KernelError::ArenaFault)
}

/// Resolve a computation id, or the fail-closed arena fault.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as `read_value`, on the computation plane.
/// - provides: the fail-closed read every computation rule goes through.
/// - fails: `KernelError::ArenaFault` for an id that resolves to no node.
/// - panics: none.
#[inline]
fn read_computation(
    arena: &TermArena,
    id: ComputationId,
) -> Result<Computation, KernelError>
{
    arena
        .computation(id)
        .cloned()
        .ok_or(KernelError::ArenaFault)
}

/// A value-type shape mismatch, with a content witness of the offending type.
///
/// # Specification
/// trivial.
#[inline]
fn value_shape_mismatch(
    arena: &TermArena,
    expected: ExpectedValueShape,
    actual: ValueTypeId,
) -> KernelError
{
    KernelError::ValueShapeMismatch {
        expected,
        actual: value_type_witness(arena, actual),
    }
}

/// A computation-type shape mismatch, with a content witness.
///
/// # Specification
/// trivial.
#[inline]
fn comp_shape_mismatch(
    arena: &TermArena,
    expected: ExpectedComputationShape,
    actual: CompTypeId,
) -> KernelError
{
    KernelError::ComputationShapeMismatch {
        expected,
        actual: comp_type_witness(arena, actual),
    }
}

/// The two read-only inputs every judgement of one declaration stands on: the
/// environment's admission log and this declaration's admitted level context.
///
/// Grouped because they travel together through both machines and are constant
/// for the whole of one check, which is also why neither is in a memo key.
#[derive(Clone, Copy, Debug)]
pub struct Judgement<'session>
{
    /// The environment's admitted declarations, for constant and atom
    /// resolution.
    entries: &'session [AdmittedDeclaration],
    /// This declaration's admitted level context.
    levels: &'session LevelContext,
}

impl<'session> Judgement<'session>
{
    /// Pair an admission log with a level context.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        entries: &'session [AdmittedDeclaration],
        levels: &'session LevelContext,
    ) -> Self
    {
        Self { entries, levels }
    }
}

/// The mutable state one declaration's check threads through both machines:
/// the memo, the session its keys are derived against, the expansion census,
/// and the code obligations the formation walk owes.
///
/// Grouped because the four travel together everywhere and are meaningful only
/// as a set — the memo is keyed against the session, the census counts what the
/// memo did not serve, and the obligations are what a walk could not answer on
/// its own. The read-only half of a judgement is [`Judgement`]; this is the
/// half that changes.
struct Recording<'session, M>
{
    /// The check memo, at whichever instantiation this run takes.
    memo: &'session mut M,
    /// The session the memo's keys are derived against.
    session: &'session mut SupportContext,
    /// The per-plane expansion census.
    census: &'session mut ExpansionCensus,
    /// The code obligations the formation walk deferred.
    owed: &'session mut Vec<CodeObligation>,
}

/// A pending type-formation obligation — the goal of the [`type_level`] walk.
#[derive(Clone, Copy, Debug)]
enum TypeLevelGoal
{
    /// The level of a value type.
    Value(ValueTypeId),
    /// The level of a computation type.
    Comp(CompTypeId),
}

impl TypeLevelGoal
{
    /// This goal in the memo's support vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn support(self) -> SupportGoal
    {
        match self {
            | Self::Value(id) => SupportGoal::ValueTypeLevel(id),
            | Self::Comp(id) => SupportGoal::CompTypeLevel(id),
        }
    }
}

/// A code obligation the formation walk deferred: this value must check against
/// the universe the type that carried it named.
///
/// **The deferral is what keeps the two machines two machines.** Deciding a
/// code's type is the checking machine's job, and having the formation walk
/// call it would make the two mutually recursive — the shape the recursion ban
/// exists to forbid. Instead formation records what it owes, the driver drains
/// the record through the checking machine, and neither walk reaches the other.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CodeObligation
{
    /// The code whose type is owed.
    code: ValueId,
    /// The universe it must inhabit.
    level: Level,
    /// The typing context the code stands in, outermost first.
    context: Vec<ValueTypeId>,
}

/// The ceiling on how many code obligations one declaration's check may drain.
///
/// A drained obligation runs the checking machine, which can form a synthesized
/// type over nodes it just minted and owe codes that were never table entries,
/// so **the obligation count is not bounded by the artifact's entry count** and
/// the constant is a ceiling rather than a derivation. What the format's entry
/// cap supplies is a scale that moves with the artifact sizes the kernel
/// accepts, so retuning the cap retunes this with it and no second magic number
/// enters the trusted base. Past the ceiling the declaration is refused rather
/// than pursued, which is the fail-closed posture the rest of the kernel takes
/// toward a condition it cannot bound.
const MAX_CODE_OBLIGATIONS: TableEntryCount = gandr_kernel_term::MAX_TABLE_ENTRIES;

/// A continuation of the type-formation walk.
#[derive(Debug)]
enum TypeLevelFrame
{
    /// The first operand's level is in the register; take the second value
    /// operand next — a product or a sum.
    MaxSecondValue(ValueTypeId),
    /// The first operand's level is in the register; take the second
    /// computation operand next — an arrow, whose codomain stands in the same
    /// context the arrow does.
    MaxSecondComp(CompTypeId),
    /// The domain's level is in the register; take the codomain next, **under
    /// the domain's binder** — a dependent arrow.
    MaxSecondCompUnder(ValueTypeId, CompTypeId),
    /// A formation binder closes: pop the innermost context slot.
    ScopeExit,
    /// The second operand's level is in the register; join with the first.
    MaxWith(Level),
    /// The inner level is in the register; check the lift's strictness and
    /// replace it with the target.
    LiftCheck(Level),
    /// The goal this frame was pushed for is now answered; record it.
    ///
    /// Pushed **before** the goal's own continuations, so it pops after all of
    /// them — which is exactly when the register holds that goal's final
    /// answer, by the machine's own unwinding invariant.
    Memoize(NodeSupport),
}

/// The universe level of a well-formed value or computation type: the
/// well-formedness gate, computed iteratively so it is total on any depth.
///
/// # Specification
/// - requires: nothing — an unreadable root refuses rather than panicking.
/// - ensures: `Ok(level)` — the type's universe level — exactly when every
///   embedded level is in scope, every lift strictly raises, every sealed atom
///   resolves to an admitted abstract-type declaration, and no successor
///   overflows; a bare universe at `l` forms at `l + 1`. The walk is iterative
///   over an explicit heap frame stack, so it is total on any type depth.
/// - provides: type formation for the declared type and for the machine's lift
///   synthesis, with the memo consulted on **this** plane so the type half's
///   collapse is real rather than assumed. Formation remains prose-only: the
///   level and admission judgement requires the full formation walk; repeating
///   it would neither independently validate the result nor establish totality.
/// - fails: [`KernelError::LevelVariableOutOfScope`],
///   [`KernelError::LevelArithmetic`], [`KernelError::UniverseViolation`],
///   [`KernelError::LevelOracleFault`], [`KernelError::NotAnAbstractType`],
///   [`KernelError::AbstractTypeKindNotUniverse`], [`KernelError::ArenaFault`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the composite level is pinned by the join over one
///   type of every former; the L3 residues are the universe successor, the
///   arrow join, the lift-strictness boundary and the atom lookup, each pinned
///   by a unit golden or its negative.
/// - witness: `check::tests::a_universe_forms_one_level_up`
/// - witness: `check::tests::a_lift_requires_a_strictly_higher_target`
/// - witness: `check::tests::an_arrow_forms_at_the_join_of_its_children`
/// - witness: `check::tests::a_dependent_arrow_forms_checks_and_eliminates_like_an_arrow`
/// - witness: `check::tests::a_dependent_identity_checks_through_its_codes`
/// - witness: `check::tests::an_abstract_type_forms_at_its_declared_universe`
fn type_level<M>(
    arena: &TermArena,
    judgement: Judgement<'_>,
    root: TypeLevelGoal,
    mut context: Vec<ValueTypeId>,
    recording: Recording<'_, M>,
) -> Result<Level, KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let Recording {
        memo,
        session,
        census,
        owed,
    } = recording;
    let mut frames: Vec<TypeLevelFrame> = Vec::new();
    let mut goal = root;
    'expand: loop {
        // A type's level depends on the type node and on the binder slice its
        // codes reach, so the support carries the same reached telescope a term
        // goal's does. When the memo is inactive this whole block is a
        // constant-false branch that monomorphization removes.
        let mut recalled: Option<Level> = None;
        if matches!(M::ACTIVITY, MemoActivity::Active) {
            let support = NodeSupport::build(arena, session, goal.support(), context.as_slice());
            match memo.recall(&support) {
                | Some(hit) => match *hit.outcome() {
                    | NodeOutcome::Formed(ref level) => recalled = Some(level.clone()),
                    // A term-shaped answer cannot have come from this walk. The
                    // memo is shared between the two machines, and a shape
                    // disagreement means the entry was not this machine's:
                    // decline it and recompute, which costs one expansion and
                    // cannot fabricate a level.
                    | NodeOutcome::Checked
                    | NodeOutcome::ValueType(_)
                    | NodeOutcome::CompType(_) => {
                        frames.push(TypeLevelFrame::Memoize(support));
                    },
                },
                | None => frames.push(TypeLevelFrame::Memoize(support)),
            }
        }
        census.record(SupportPlane::Type, match recalled {
            | Some(_) => ExpansionKind::Recalled,
            | None => ExpansionKind::Expanded,
        });
        let mut produced: Level = match recalled {
            | Some(level) => level,
            | None => match goal {
                | TypeLevelGoal::Value(id) => {
                    let value_type = arena.value_type(id).ok_or(KernelError::ArenaFault)?;
                    match *value_type {
                        | ValueType::Base(_) | ValueType::Unit => Level::zero(),
                        | ValueType::Universe(ref level) => {
                            judgement.levels.check_level_scope(level)?;
                            level.succ()?
                        },
                        // A sealed atom forms at the level its own
                        // declaration's kind fixes. The lookup is the whole
                        // rule: nothing is inferred, nothing unfolds, and a
                        // position that does not resolve to an abstract-type
                        // declaration is refused here rather than trusted.
                        | ValueType::Abstract(atom) => {
                            abstract_atom_level(arena, judgement.entries, atom)?
                        },
                        // A code's type is the checking machine's question, so
                        // the level is read off the node and the obligation is
                        // recorded for the driver to drain. Reading it is not
                        // trusting it: nothing admits until the recorded
                        // obligation has been checked.
                        | ValueType::Element { code, ref target } => {
                            judgement.levels.check_level_scope(target)?;
                            owed.push(CodeObligation {
                                code,
                                level: target.clone(),
                                context: context.clone(),
                            });
                            target.clone()
                        },
                        | ValueType::Product(first, second) | ValueType::Sum(first, second) => {
                            frames.push(TypeLevelFrame::MaxSecondValue(second));
                            goal = TypeLevelGoal::Value(first);
                            continue 'expand;
                        },
                        | ValueType::Thunk(body) => {
                            goal = TypeLevelGoal::Comp(body);
                            continue 'expand;
                        },
                        | ValueType::Lift { inner, ref target } => {
                            frames.push(TypeLevelFrame::LiftCheck(target.clone()));
                            goal = TypeLevelGoal::Value(inner);
                            continue 'expand;
                        },
                    }
                },
                | TypeLevelGoal::Comp(id) => {
                    let comp_type = arena.comp_type(id).ok_or(KernelError::ArenaFault)?;
                    match *comp_type {
                        | CompType::Returner(result) => {
                            goal = TypeLevelGoal::Value(result);
                            continue 'expand;
                        },
                        // Both arrows form at the join of their two children's
                        // levels, and the dependent one needs no context to do
                        // it: no type former is indexed by a value term, so a
                        // codomain's level is a function of its own node however
                        // many binders it stands under.
                        | CompType::Arrow { domain, codomain } => {
                            frames.push(TypeLevelFrame::MaxSecondComp(codomain));
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                        // The dependent arrow's codomain is formed under the
                        // domain's binder, so the walk carries a context of its
                        // own — the half of "types in the context stop being
                        // closed" that formation pays.
                        | CompType::Pi { domain, codomain } => {
                            frames.push(TypeLevelFrame::MaxSecondCompUnder(domain, codomain));
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                    }
                },
            },
        };
        loop {
            let Some(frame) = frames.pop()
            else {
                return Ok(produced);
            };
            match frame {
                | TypeLevelFrame::Memoize(support) => {
                    // A memo at its ceiling declines to record. The check
                    // proceeds unmemoized from there, which costs collapse and
                    // never correctness.
                    let _recorded = memo.remember(support, NodeOutcome::Formed(produced.clone()));
                },
                | TypeLevelFrame::MaxSecondValue(second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    goal = TypeLevelGoal::Value(second);
                    continue 'expand;
                },
                | TypeLevelFrame::MaxSecondComp(second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    goal = TypeLevelGoal::Comp(second);
                    continue 'expand;
                },
                | TypeLevelFrame::MaxSecondCompUnder(domain, second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    frames.push(TypeLevelFrame::ScopeExit);
                    context.push(domain);
                    goal = TypeLevelGoal::Comp(second);
                    continue 'expand;
                },
                | TypeLevelFrame::ScopeExit => {
                    let _popped = context.pop();
                },
                | TypeLevelFrame::MaxWith(first) => {
                    produced = first.max(&produced);
                },
                | TypeLevelFrame::LiftCheck(target) => {
                    judgement.levels.check_level_scope(&target)?;
                    judgement.levels.check_universe_below(&produced, &target)?;
                    produced = target;
                },
            }
        }
    }
}

/// The universe level of a sealed abstract type, read off its declaration's
/// kind.
///
/// This is the **whole** formation rule for a sealed atom, and its shape is the
/// point: a lookup, not an inference. The kernel resolves the position,
/// requires the declaration it finds to be an abstract type, and reads the
/// level out of a kind that admission already pinned to a universe. No branch
/// consults the atom's representation, because none is recorded — which is what
/// "an atom with no unfolding rule" means operationally.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| match
///   entries.get(usize::from(atom)).map(AdmittedDeclaration::content) {
///   Some(&DeclarationContent::AbstractType { kind }) =>
///   arena.value_type(kind).map_or_else(|| ret.is_err(), |node| match *node {
///   ValueType::Universe(ref level) => ret.as_ref().is_ok_and(|actual| actual
///   == level), _ => ret.is_err() }), _ => ret.is_err() }` — success carries
///   the declared universe level exactly when `atom` names an admitted abstract
///   type whose kind resolves to a universe.
/// - provides: the atom's formation level.
/// - fails: [`KernelError::NotAnAbstractType`] for an out-of-range position, a
///   forward reference, or a definition or axiom at that position;
///   [`KernelError::AbstractTypeKindNotUniverse`] when the kind is not a
///   universe, which admission pins and which is therefore surfaced rather than
///   trusted; [`KernelError::ArenaFault`] on an unreadable kind.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2 — an atom typed at its declared universe is pinned by the
///   admission witness; the L3 residues are the three refusal arms, each pinned
///   by its own negative witness.
/// - witness: `check::tests::an_abstract_type_forms_at_its_declared_universe`
/// - witness: `check::tests::an_atom_naming_a_definition_is_not_an_abstract_type`
/// - witness: `check::tests::a_forward_atom_reference_is_not_an_abstract_type`
#[spec(ensures: |ret| match entries.get(usize::from(atom)).map(AdmittedDeclaration::content) { Some(&DeclarationContent::AbstractType { kind }) => arena.value_type(kind).map_or_else(|| ret.is_err(), |node| match *node { ValueType::Universe(ref level) => ret.as_ref().is_ok_and(|actual| actual == level), _ => ret.is_err() }), _ => ret.is_err() })]
fn abstract_atom_level(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    atom: ConstantIndex,
) -> Result<Level, KernelError>
{
    let entry = entries
        .get(usize::from(atom))
        .ok_or(KernelError::NotAnAbstractType { index: atom })?;
    let DeclarationContent::AbstractType { kind } = *entry.content()
    else {
        return Err(KernelError::NotAnAbstractType { index: atom });
    };
    let kind_node = arena.value_type(kind).ok_or(KernelError::ArenaFault)?;
    match *kind_node {
        | ValueType::Universe(ref level) => Ok(level.clone()),
        | ValueType::Base(_)
        | ValueType::Unit
        | ValueType::Product(..)
        | ValueType::Sum(..)
        | ValueType::Thunk(_)
        | ValueType::Lift { .. }
        | ValueType::Element { .. }
        | ValueType::Abstract(_) => Err(KernelError::AbstractTypeKindNotUniverse {
            actual: value_type_witness(arena, kind),
        }),
    }
}

/// A result the checker machine produced into its register.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Produced
{
    /// A synthesized value type.
    ValueType(ValueTypeId),
    /// A synthesized computation type.
    CompType(CompTypeId),
    /// A check succeeded; no type is carried.
    Checked,
}

impl Produced
{
    /// This answer in the memo's outcome vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn outcome(self) -> NodeOutcome
    {
        match self {
            | Self::ValueType(id) => NodeOutcome::ValueType(id),
            | Self::CompType(id) => NodeOutcome::CompType(id),
            | Self::Checked => NodeOutcome::Checked,
        }
    }

    /// Read a memo outcome back as a register value.
    ///
    /// A formation level cannot be the answer to a term goal, so it is treated
    /// as a **miss** rather than trusted: declining costs one recomputation and
    /// cannot fabricate a verdict.
    ///
    /// # Specification
    /// - requires: nothing; an outcome of the formation machine is admissible
    ///   input.
    /// - ensures: the register value a term goal's answer carries, and nothing
    ///   for a formation level, which is not an answer to a term goal.
    /// - provides: the guard that makes a shared memo safe between the two
    ///   machines: a support carrying the wrong shape is declined and
    ///   recomputed rather than trusted, which costs one recomputation and
    ///   cannot fabricate a verdict.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    const fn of_outcome(outcome: &NodeOutcome) -> Option<Self>
    {
        match *outcome {
            | NodeOutcome::ValueType(id) => Some(Self::ValueType(id)),
            | NodeOutcome::CompType(id) => Some(Self::CompType(id)),
            | NodeOutcome::Checked => Some(Self::Checked),
            | NodeOutcome::Formed(_) => None,
        }
    }

    /// Project a synthesized value type out of the register.
    ///
    /// # Specification
    /// - requires: the register was set by a value-synthesizing goal, which the
    ///   module's correspondence table is the wiring audit for.
    /// - ensures: `Ok(id)` — the produced value-type id.
    /// - provides: the fail-closed projection every value-consuming frame
    ///   takes. The const API stays prose-only: the pinned `anodized` expansion
    ///   calls a non-const evaluator (`E0015`).
    /// - fails: [`KernelError::CheckerRegisterFault`] on a non-value register,
    ///   which is unreachable when the machine is wired as its table states and
    ///   is surfaced rather than trusted, so a wiring defect rejects the
    ///   declaration instead of fabricating a type that could wrongly convert.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::CheckerRegisterFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fault arm is unreachable through the public
    ///   surface by construction, so it is pinned directly at the projection.
    /// - witness: `check::tests::register_polarity_faults_fail_closed`
    #[inline]
    const fn value_type(self) -> Result<ValueTypeId, KernelError>
    {
        match self {
            | Self::ValueType(id) => Ok(id),
            | Self::CompType(_) | Self::Checked => Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedValueType,
            )),
        }
    }

    /// Project a synthesized computation type out of the register.
    ///
    /// # Specification
    /// - requires: the register was set by a computation-synthesizing goal.
    /// - ensures: `Ok(id)` — the produced computation-type id.
    /// - provides: the fail-closed projection every computation-consuming frame
    ///   takes; see [`Self::value_type`] for the posture. The const API stays
    ///   prose-only: the pinned `anodized` expansion calls a non-const
    ///   evaluator (`E0015`).
    /// - fails: [`KernelError::CheckerRegisterFault`] on a non-computation
    ///   register.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::CheckerRegisterFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::value_type`].
    /// - witness: `check::tests::register_polarity_faults_fail_closed`
    #[inline]
    const fn comp_type(self) -> Result<CompTypeId, KernelError>
    {
        match self {
            | Self::CompType(id) => Ok(id),
            | Self::ValueType(_) | Self::Checked => Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedCompType,
            )),
        }
    }
}

/// A checking obligation over a term node — the goal of the machine.
#[derive(Clone, Copy, Debug)]
enum Goal
{
    /// Synthesize a value's type.
    SynthValue(ValueId),
    /// Check a value against an expected value type.
    CheckValue(ValueId, ValueTypeId),
    /// Synthesize a computation's type.
    SynthComp(ComputationId),
    /// Check a computation against an expected computation type.
    CheckComp(ComputationId, CompTypeId),
}

impl Goal
{
    /// This goal in the memo's support vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn support(self) -> SupportGoal
    {
        match self {
            | Self::SynthValue(id) => SupportGoal::SynthValue(id),
            | Self::CheckValue(id, expected) => SupportGoal::CheckValue(id, expected),
            | Self::SynthComp(id) => SupportGoal::SynthComp(id),
            | Self::CheckComp(id, expected) => SupportGoal::CheckComp(id, expected),
        }
    }
}

/// A continuation of the checker machine. Every held type is a `Copy` id.
#[derive(Debug)]
enum Frame
{
    /// A pair synthesis: the first component is synthesizing; the second source
    /// is held.
    SynthPairFirst(ValueId),
    /// A pair synthesis: the first component is synthesized; the second is.
    SynthPairSecond(ValueTypeId),
    /// A thunk synthesis: the body computation is synthesizing.
    SynthThunk,
    /// A lift synthesis: the body is synthesizing; the target level is held.
    SynthLift(Level),
    /// A pair check: the first component checked; check the second against the
    /// held component type.
    CheckPairSecond(ValueId, ValueTypeId),
    /// A value mode switch: the value synthesized; convert against the held
    /// expected type.
    ConvertValue(ValueTypeId),
    /// An application: the head is synthesized; the argument source is held.
    SynthApply(ValueId),
    /// An application: the argument checked; produce the held codomain.
    ProduceComp(CompTypeId),
    /// A force: the value is synthesized.
    SynthForce,
    /// A returner synthesis: the value is synthesized.
    SynthReturn,
    /// A bind synthesis: the bound computation is synthesized; the body source
    /// is held, and the body's type becomes the bind's.
    SynthBind(ComputationId),
    /// A case synthesis: the scrutinee is synthesized; both branch sources are
    /// held.
    SynthCaseScrutinee(ComputationId, ComputationId),
    /// A case synthesis: the left branch synthesized; its type and the right
    /// summand are held while the right branch synthesizes.
    SynthCaseAfterLeft
    {
        /// The right branch source.
        on_right: ComputationId,
        /// The right summand, a context slot for the right branch.
        right: ValueTypeId,
    },
    /// A case synthesis: both branches synthesized; the left type is held for
    /// the convergence check.
    SynthCaseAfterRight
    {
        /// The left branch's synthesized type.
        left_type: CompTypeId,
    },
    /// A computation mode switch: the computation synthesized; convert against
    /// the held expected type.
    ConvertComp(CompTypeId),
    /// A bind check: the bound computation synthesized; the body source and the
    /// expected type are held.
    CheckBind(ComputationId, CompTypeId),
    /// A case check: the scrutinee synthesized; the branch sources and expected
    /// type are held.
    CheckCaseScrutinee
    {
        /// The left branch source.
        on_left: ComputationId,
        /// The right branch source.
        on_right: ComputationId,
        /// The expected type both branches check against.
        expected: CompTypeId,
    },
    /// A case check: the left branch checked; the right source, right summand
    /// and expected type are held.
    CheckCaseAfterLeft
    {
        /// The right branch source.
        on_right: ComputationId,
        /// The right summand, a context slot for the right branch.
        right: ValueTypeId,
        /// The expected type the right branch checks against.
        expected: CompTypeId,
    },
    /// A binder scope closes: pop the innermost context slot.
    ScopeExit,
    /// The goal this frame was pushed for is now answered; record it.
    ///
    /// Pushed **before** the goal's own continuations, so it pops after all of
    /// them — which is exactly when the produced register holds that goal's
    /// final answer, by the machine's own unwinding invariant.
    Memoize(NodeSupport),
}

/// The value type bound at de Bruijn `index`, if in scope. The context head is
/// index zero.
///
/// # Specification
/// - requires: `context` is the machine's typing context, outermost first, so
///   index zero names its last slot.
/// - ensures: the slot `index` names when it is in scope, and nothing when the
///   index reaches past the context.
/// - provides: the raw context lookup `lookup` raises into the use site's
///   context.
/// - fails: never — an out-of-scope index is the absence, which the caller
///   refuses on.
/// - panics: none.
#[inline]
fn slot(
    context: &[ValueTypeId],
    index: DeBruijnIndex,
) -> Option<ValueTypeId>
{
    let steps = usize::try_from(u32::from(index)).ok()?;
    let last = context.len().checked_sub(1)?;
    let position = last.checked_sub(steps)?;
    context.get(position).copied()
}

/// The value type bound at de Bruijn `index`, **read into the context the
/// variable stands in**.
///
/// A slot was recorded against the context prefix that preceded it, so a slot
/// reached across `index` binders is written one context shorter for each of
/// them and has to be raised past all of them before it means anything at the
/// use site. That is the shift the dependent arrow makes necessary and the
/// reason a context of types stops being a context of closed things.
///
/// # Specification
/// - requires: `context` is the machine's typing context, outermost first.
/// - ensures: `Some(type)` — the slot raised past the binders between it and
///   the use site — exactly when `index` names a slot in scope; `None` when it
///   reaches past the context, which the caller refuses on.
/// - provides: the variable rule's whole content. The context's provenance and
///   raised-content equality remain prose-only: the context carries no origin
///   token, and checking the shifted result would repeat the mutating rewrite
///   or require an allocating entry snapshot.
/// - fails: never — an out-of-scope index is the `None`, not an error here.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the slot lookup and the raise, separated
///   by a variable naming a closed slot (the slot itself, unshifted because
///   raising a closed type is the identity) and by the shifting machine's own
///   witnesses at a family where indices occur.
/// - witness: `check::tests::a_variable_synthesizes_its_context_type`
#[inline]
fn lookup(
    arena: &mut TermArena,
    session: &mut SupportContext,
    context: &[ValueTypeId],
    index: DeBruijnIndex,
) -> Option<ValueTypeId>
{
    let found = slot(context, index)?;
    let amount = BinderDepth::past(BinderDepth::from(u32::from(index)));
    let (table, rewrites) = session.rewrite_parts();
    Some(shift_value_type(
        arena,
        table,
        rewrites,
        found,
        BinderDepth::NONE,
        amount,
    ))
}

/// The declared value type of a prior admitted declaration.
///
/// # Specification
/// - requires: `entries` is the environment's admission log, in admission
///   order.
/// - ensures: the declared value-type root of the declaration at `index`, and
///   nothing for a position the log does not hold — which is what makes a
///   forward reference into the append-only log a refusal rather than a
///   resolution.
/// - provides: the constant rule's resolution step.
/// - fails: never — an unresolved position is the absence, which the caller
///   refuses on.
/// - panics: none.
#[inline]
fn resolve_constant(
    entries: &[AdmittedDeclaration],
    index: ConstantIndex,
) -> Option<ValueTypeId>
{
    entries
        .get(usize::from(index))
        .map(AdmittedDeclaration::declared_id)
}

/// Run the checker machine from an initial goal and context to a verdict,
/// minting synthesized types into `arena`.
///
/// # Specification
/// - requires: `context` is the initial typing context, empty for a
///   declaration's body; `entries` is the environment's admission log.
/// - ensures: `Ok(produced)` — a synthesized type for a synthesis goal, or the
///   checked answer for a checking goal — exactly when the term checks or
///   synthesizes under this subset's rules. The walk is iterative over a heap
///   frame stack and an explicit context stack, so it is total on any term
///   depth. Synthesized types are minted into `arena` as intermediates the
///   caller truncates after the verdict. The verdict is **independent of the
///   memo**: the same function at the null memo returns the same answer.
/// - provides: the shared engine of every checking and synthesis judgement. The
///   typing, context-origin, totality, and memo-independence claims remain
///   prose-only: they require rule derivations and comparisons of whole
///   executions, not a predicate over one return value.
/// - fails: any [`KernelError`] a rule surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L2/L3 — the differential over the corpus pins memoized against
///   memoless, verdict for verdict, and the golden corpus pins acceptance of
///   well-typed declarations against rejection of ill-typed ones; the L3
///   residues are each rule's failure arm, pinned by negative unit goldens, and
///   totality on adversarial depth, pinned by a small-stack deep-chain witness.
/// - witness: `check::tests::a_variable_synthesizes_its_context_type`
/// - witness: `check::tests::an_injection_is_not_inferable`
/// - witness: `check::tests::an_injection_checks_against_its_sum`
/// - witness: `check::tests::a_pair_propagates_into_a_checking_component`
/// - witness: `check::tests::an_application_produces_the_codomain`
/// - witness: `check::tests::a_dependent_arrow_forms_checks_and_eliminates_like_an_arrow`
/// - witness: `check::tests::an_application_instantiates_a_dependent_codomain`
/// - witness: `check::tests::a_force_unwraps_a_thunk`
/// - witness: `check::tests::a_case_requires_convergent_branches`
/// - witness: `check::tests::a_case_propagates_the_expected_type`
/// - witness: `check::tests::a_bind_binds_the_returned_value`
fn run<M>(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    mut context: Vec<ValueTypeId>,
    initial: Goal,
    recording: Recording<'_, M>,
) -> Result<Produced, KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let Recording {
        memo,
        session,
        census,
        owed,
    } = recording;
    let mut frames: Vec<Frame> = Vec::new();
    let mut goal = initial;
    'expand: loop {
        // Consult the memo for this goal's support before reading the node.
        // When the memo is inactive this whole block — the support
        // construction included — is a constant-false branch that
        // monomorphization removes, so the memoless path keeps the code it had
        // before the seam existed.
        let mut recalled: Option<Produced> = None;
        if matches!(M::ACTIVITY, MemoActivity::Active) {
            let support = NodeSupport::build(arena, session, goal.support(), context.as_slice());
            if let Some(hit) = memo.recall(&support) {
                recalled = Produced::of_outcome(hit.outcome());
            }
            if recalled.is_none() {
                frames.push(Frame::Memoize(support));
            }
        }
        census.record(SupportPlane::Term, match recalled {
            | Some(_) => ExpansionKind::Recalled,
            | None => ExpansionKind::Expanded,
        });
        let mut produced: Produced = match recalled {
            | Some(outcome) => outcome,
            | None => match goal {
                | Goal::SynthValue(id) => match read_value(arena, id)? {
                    | Value::Variable(index) => {
                        let synthesized = lookup(arena, session, context.as_slice(), index)
                            .ok_or(KernelError::UnboundVariable { index })?;
                        Produced::ValueType(synthesized)
                    },
                    | Value::Constant(index) => {
                        let synthesized = resolve_constant(judgement.entries, index)
                            .ok_or(KernelError::UnboundConstant { index })?;
                        Produced::ValueType(synthesized)
                    },
                    | Value::Unit => Produced::ValueType(arena.value_type_unit()),
                    | Value::Literal(ref literal) => {
                        Produced::ValueType(arena.value_type_base(literal.base_type()))
                    },
                    | Value::Pair(first, second) => {
                        frames.push(Frame::SynthPairFirst(second));
                        goal = Goal::SynthValue(first);
                        continue 'expand;
                    },
                    | Value::Thunk(body) => {
                        frames.push(Frame::SynthThunk);
                        goal = Goal::SynthComp(body);
                        continue 'expand;
                    },
                    | Value::Lift { target, body } => {
                        frames.push(Frame::SynthLift(target));
                        goal = Goal::SynthValue(body);
                        continue 'expand;
                    },
                    | Value::Injection(..) => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::Injection,
                        });
                    },
                },
                | Goal::CheckValue(id, expected) => match read_value(arena, id)? {
                    | Value::Injection(side, body) => match arena.value_type(expected) {
                        | Some(&ValueType::Sum(left, right)) => {
                            let summand = match side {
                                | Side::Left => left,
                                | Side::Right => right,
                            };
                            goal = Goal::CheckValue(body, summand);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Sum,
                                expected,
                            ));
                        },
                    },
                    | Value::Pair(first, second) => match arena.value_type(expected) {
                        | Some(&ValueType::Product(first_type, second_type)) => {
                            frames.push(Frame::CheckPairSecond(second, second_type));
                            goal = Goal::CheckValue(first, first_type);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Product,
                                expected,
                            ));
                        },
                    },
                    | Value::Thunk(body) => match arena.value_type(expected) {
                        | Some(&ValueType::Thunk(codomain)) => {
                            goal = Goal::CheckComp(body, codomain);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Thunk,
                                expected,
                            ));
                        },
                    },
                    | Value::Variable(_)
                    | Value::Constant(_)
                    | Value::Unit
                    | Value::Literal(_)
                    | Value::Lift { .. } => {
                        frames.push(Frame::ConvertValue(expected));
                        goal = Goal::SynthValue(id);
                        continue 'expand;
                    },
                },
                | Goal::SynthComp(id) => match read_computation(arena, id)? {
                    | Computation::Application(head, argument) => {
                        frames.push(Frame::SynthApply(argument));
                        goal = Goal::SynthComp(head);
                        continue 'expand;
                    },
                    | Computation::Force(value) => {
                        frames.push(Frame::SynthForce);
                        goal = Goal::SynthValue(value);
                        continue 'expand;
                    },
                    | Computation::Return(value) => {
                        frames.push(Frame::SynthReturn);
                        goal = Goal::SynthValue(value);
                        continue 'expand;
                    },
                    | Computation::Bind(bound, body) => {
                        frames.push(Frame::SynthBind(body));
                        goal = Goal::SynthComp(bound);
                        continue 'expand;
                    },
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => {
                        frames.push(Frame::SynthCaseScrutinee(on_left, on_right));
                        goal = Goal::SynthValue(scrutinee);
                        continue 'expand;
                    },
                    | Computation::Lambda(_) => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::Lambda,
                        });
                    },
                },
                | Goal::CheckComp(id, expected) => match read_computation(arena, id)? {
                    // A lambda checks against either arrow the same way: push
                    // the domain as the innermost context slot and check the
                    // body against the codomain. The dependent arrow's codomain
                    // is already written under that binder, which is exactly the
                    // context the push establishes, so the two arms are one.
                    | Computation::Lambda(body) => match arena.comp_type(expected) {
                        | Some(
                            &CompType::Arrow { domain, codomain }
                            | &CompType::Pi { domain, codomain },
                        ) => {
                            context.push(domain);
                            frames.push(Frame::ScopeExit);
                            goal = Goal::CheckComp(body, codomain);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Arrow,
                                expected,
                            ));
                        },
                    },
                    | Computation::Return(value) => match arena.comp_type(expected) {
                        | Some(&CompType::Returner(result)) => {
                            goal = Goal::CheckValue(value, result);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Returner,
                                expected,
                            ));
                        },
                    },
                    | Computation::Bind(bound, body) => {
                        frames.push(Frame::CheckBind(body, expected));
                        goal = Goal::SynthComp(bound);
                        continue 'expand;
                    },
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => {
                        frames.push(Frame::CheckCaseScrutinee {
                            on_left,
                            on_right,
                            expected,
                        });
                        goal = Goal::SynthValue(scrutinee);
                        continue 'expand;
                    },
                    | Computation::Application(..) | Computation::Force(_) => {
                        frames.push(Frame::ConvertComp(expected));
                        goal = Goal::SynthComp(id);
                        continue 'expand;
                    },
                },
            },
        };
        loop {
            let Some(frame) = frames.pop()
            else {
                return Ok(produced);
            };
            match frame {
                | Frame::Memoize(support) => {
                    // A memo at its ceiling declines to record; see the same
                    // note in `type_level`.
                    let _recorded = memo.remember(support, produced.outcome());
                },
                | Frame::SynthPairFirst(second) => {
                    let first_type = produced.value_type()?;
                    frames.push(Frame::SynthPairSecond(first_type));
                    goal = Goal::SynthValue(second);
                    continue 'expand;
                },
                | Frame::SynthPairSecond(first_type) => {
                    let second_type = produced.value_type()?;
                    produced =
                        Produced::ValueType(arena.value_type_product(first_type, second_type));
                },
                | Frame::SynthThunk => {
                    let body_type = produced.comp_type()?;
                    produced = Produced::ValueType(arena.value_type_thunk(body_type));
                },
                | Frame::SynthLift(target) => {
                    let body_type = produced.value_type()?;
                    let body_level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(body_type),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    judgement.levels.check_level_scope(&target)?;
                    judgement
                        .levels
                        .check_universe_below(&body_level, &target)?;
                    produced = Produced::ValueType(arena.value_type_lift(body_type, target));
                },
                | Frame::CheckPairSecond(second, second_type) => {
                    goal = Goal::CheckValue(second, second_type);
                    continue 'expand;
                },
                | Frame::ConvertValue(expected) => {
                    let synthesized = produced.value_type()?;
                    convert_value_type(arena, expected, synthesized)?;
                    produced = Produced::Checked;
                },
                | Frame::SynthApply(argument) => {
                    let head_type = produced.comp_type()?;
                    match arena.comp_type(head_type) {
                        // An application eliminates either arrow: check the
                        // argument against the domain and produce the codomain.
                        | Some(&CompType::Arrow { domain, codomain }) => {
                            frames.push(Frame::ProduceComp(codomain));
                            goal = Goal::CheckValue(argument, domain);
                            continue 'expand;
                        },
                        // **The dependent arm instantiates the codomain at the
                        // argument**, which is the whole difference between the
                        // two eliminations: a codomain that mentions its binder
                        // through a code names the argument after this step, and
                        // a codomain that mentions nothing is handed back
                        // unchanged at no cost.
                        | Some(&CompType::Pi { domain, codomain }) => {
                            let (table, rewrites) = session.rewrite_parts();
                            let instantiated =
                                substitute_comp_type(arena, table, rewrites, codomain, argument);
                            frames.push(Frame::ProduceComp(instantiated));
                            goal = Goal::CheckValue(argument, domain);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Arrow,
                                head_type,
                            ));
                        },
                    }
                },
                | Frame::ProduceComp(codomain) => {
                    produced = Produced::CompType(codomain);
                },
                | Frame::SynthForce => {
                    let value_type = produced.value_type()?;
                    match arena.value_type(value_type) {
                        | Some(&ValueType::Thunk(codomain)) => {
                            produced = Produced::CompType(codomain);
                        },
                        | _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Thunk,
                                value_type,
                            ));
                        },
                    }
                },
                | Frame::SynthReturn => {
                    let result_type = produced.value_type()?;
                    produced = Produced::CompType(arena.comp_type_returner(result_type));
                },
                | Frame::SynthBind(body) => {
                    let bound_type = produced.comp_type()?;
                    match arena.comp_type(bound_type) {
                        | Some(&CompType::Returner(result)) => {
                            context.push(result);
                            frames.push(Frame::ScopeExit);
                            goal = Goal::SynthComp(body);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Returner,
                                bound_type,
                            ));
                        },
                    }
                },
                | Frame::SynthCaseScrutinee(on_left, on_right) => {
                    let scrutinee_type = produced.value_type()?;
                    match arena.value_type(scrutinee_type) {
                        | Some(&ValueType::Sum(left, right)) => {
                            context.push(left);
                            frames.push(Frame::SynthCaseAfterLeft { on_right, right });
                            frames.push(Frame::ScopeExit);
                            goal = Goal::SynthComp(on_left);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Sum,
                                scrutinee_type,
                            ));
                        },
                    }
                },
                | Frame::SynthCaseAfterLeft { on_right, right } => {
                    let left_type = produced.comp_type()?;
                    context.push(right);
                    frames.push(Frame::SynthCaseAfterRight { left_type });
                    frames.push(Frame::ScopeExit);
                    goal = Goal::SynthComp(on_right);
                    continue 'expand;
                },
                | Frame::SynthCaseAfterRight { left_type } => {
                    let right_type = produced.comp_type()?;
                    match convertible_comp_types(arena, left_type, right_type) {
                        | Convertibility::Convertible => {
                            produced = Produced::CompType(left_type);
                        },
                        | Convertibility::Distinct => {
                            return Err(case_branch_mismatch(arena, left_type, right_type));
                        },
                    }
                },
                | Frame::ConvertComp(expected) => {
                    let synthesized = produced.comp_type()?;
                    convert_comp_type(arena, expected, synthesized)?;
                    produced = Produced::Checked;
                },
                | Frame::CheckBind(body, expected) => {
                    let bound_type = produced.comp_type()?;
                    match arena.comp_type(bound_type) {
                        | Some(&CompType::Returner(result)) => {
                            context.push(result);
                            frames.push(Frame::ScopeExit);
                            goal = Goal::CheckComp(body, expected);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Returner,
                                bound_type,
                            ));
                        },
                    }
                },
                | Frame::CheckCaseScrutinee {
                    on_left,
                    on_right,
                    expected,
                } => {
                    let scrutinee_type = produced.value_type()?;
                    match arena.value_type(scrutinee_type) {
                        | Some(&ValueType::Sum(left, right)) => {
                            context.push(left);
                            frames.push(Frame::CheckCaseAfterLeft {
                                on_right,
                                right,
                                expected,
                            });
                            frames.push(Frame::ScopeExit);
                            goal = Goal::CheckComp(on_left, expected);
                            continue 'expand;
                        },
                        | _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Sum,
                                scrutinee_type,
                            ));
                        },
                    }
                },
                | Frame::CheckCaseAfterLeft {
                    on_right,
                    right,
                    expected,
                } => {
                    context.push(right);
                    frames.push(Frame::ScopeExit);
                    goal = Goal::CheckComp(on_right, expected);
                    continue 'expand;
                },
                | Frame::ScopeExit => {
                    let _popped = context.pop();
                },
            }
        }
    }
}

/// Check a declaration's sealing provenance against its declared type.
///
/// The slot claims which atoms a sealing projection rebound; this re-derives
/// that claim rather than accepting it. Two obligations, and both are about
/// making the slot **falsifiable**: every claimed atom occurs in the declared
/// type, so the recorded extent of the projection is observable in what the
/// projection produced; and the entries are strictly ascending, so the slot is
/// a set with one spelling and a repeat cannot inflate an extent.
///
/// What is deliberately *not* checked: that sealing happened, that a signature
/// was matched, or that the producer did anything in particular. Those are
/// claims about a history the kernel did not witness and cannot re-derive.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(())` exactly when the provenance is strictly ascending and
///   every entry occurs as a sealed atom reachable from the declared type.
/// - provides: the choke point's sealing-provenance gate.
/// - fails: [`KernelError::SealingProvenanceNotCanonical`],
///   [`KernelError::SealingProvenanceNotProjected`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2 — a sealed member whose provenance matches its type admits;
///   the L3 residues are the two refusal arms, each pinned by a negative
///   witness naming the exact offending atom.
/// - witness: `check::tests::sealing_provenance_must_occur_in_the_declared_type`
/// - witness: `check::tests::sealing_provenance_must_be_strictly_ascending`
// The predicate covers the ascending half, stated as a sortedness test rather
// than through the body's own previous-index loop. The occurrence half would
// mean re-deriving the projected-atom set, doubling a walk over the declared
// type at the choke point, so it stays with the witnesses.
#[spec(ensures: |ret| ret.is_err()
    || provenance.is_sorted_by(|left, right| usize::from(*left) < usize::from(*right)))]
fn check_sealing_provenance(
    arena: &TermArena,
    declared: ValueTypeId,
    provenance: &[ConstantIndex],
) -> Result<(), KernelError>
{
    if provenance.is_empty() {
        return Ok(());
    }
    let mut previous: Option<ConstantIndex> = None;
    for &atom in provenance {
        if let Some(last) = previous
            && usize::from(atom) <= usize::from(last)
        {
            return Err(KernelError::SealingProvenanceNotCanonical { atom });
        }
        previous = Some(atom);
    }
    let projected = projected_atoms(arena, declared);
    for &atom in provenance {
        if !projected.contains(&atom) {
            return Err(KernelError::SealingProvenanceNotProjected { atom });
        }
    }
    Ok(())
}

/// Check a declaration through the default path: a fresh live memo, built here
/// and dropped here.
///
/// This is the entry the admission choke point calls, and it takes **no memo
/// parameter** — which is the structural form of the lifetime rule. A caller
/// cannot hand admission a memo, so nothing an earlier call recorded can reach
/// a later one through the checked entry.
///
/// # Specification
/// - requires: `declaration`'s content roots were minted into `arena`;
///   `entries` is the environment's admission log.
/// - ensures: `Ok(())` exactly when the declared type forms, the sealing
///   provenance re-derives, and a definition's body checks against its declared
///   type in the empty context. An axiom checks only its type; a sealed atom
///   checks only that its kind is a universe. Synthesized intermediates are
///   minted into `arena` for the caller to truncate.
/// - provides: the body check the choke point runs, with the memo on by default
///   on both machines. Arena and admission-log provenance carry no runtime
///   identity token; the typing and formation judgement requires an independent
///   checker. These clauses remain prose-only rather than repeat the checked
///   computation.
/// - fails: any [`KernelError`] the checker surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L2 — the corpus pins acceptance of well-typed declarations and
///   rejection of ill-typed ones, and the memo adds no decision surface of its
///   own, so its adequacy is the differential's: the memoized answer is the
///   memoless answer. The L3 residues are the three content arms.
/// - witness: `check::tests::an_identity_thunk_checks`
/// - witness: `check::tests::a_dependent_identity_checks_through_its_codes`
/// - witness: `check::tests::a_code_that_is_not_of_its_declared_universe_refuses`
/// - witness: `check::tests::an_axiom_checks_only_its_type`
/// - witness: `check::tests::a_sealed_atom_checks_only_its_kind`
#[inline]
pub fn check_declaration(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    levels: &LevelContext,
    declaration: &Declaration,
) -> Result<(), KernelError>
{
    let mut memo: DefaultMemo = DefaultMemo::new();
    let mut session = SupportContext::new();
    let mut census = ExpansionCensus::new();
    check_declaration_with_memo(
        arena,
        entries,
        levels,
        declaration,
        &mut memo,
        &mut session,
        &mut census,
    )
}

/// Check a declaration against a caller-supplied memo — the **opt-in** entry.
///
/// # This entry admits nothing, and that is the seam
///
/// It returns a verdict and never a checked id, so a caller reaching it cannot
/// get a declaration into an environment. Admission goes through
/// [`check_declaration`], which builds its own memo; there is no admitting
/// entry that accepts one. So the memo's lifetime being a single call is a
/// property of the surface rather than a discipline a caller has to remember.
///
/// # Why the lifetime rule survives the content key
///
/// Under an arena-identity key the one-call lifetime was a *consequence*: ids
/// dangle once the choke point truncates. A content key dissolves that reason,
/// so the rule now rests on the two-wall discipline directly — **a hit claims
/// only its own history, and no kernel-checked support discipline exists**.
/// Until one does, or its impossibility is recorded, nothing here persists. The
/// content key removed the fence, not the rule.
///
/// A second reason survives independently and is worth naming: an *outcome*
/// still carries arena ids even though the key does not, so an entry outliving
/// its arena would hand back a synthesized type that no longer resolves.
///
/// # Specification
/// - requires: as [`check_declaration`]; additionally, `memo` holds only
///   entries recorded during this same call against this same arena.
/// - ensures: the verdict is **independent of `memo`** — the same as
///   [`check_declaration`] and the same as running at the null memo. On success
///   `memo` holds one entry per distinct support the check covered, and
///   `census` counts one expansion or one recall per goal, per plane.
/// - provides: the memoized checking path, and the memoless path the
///   differential compares it against, as one function at two type parameters.
///   Session provenance, memo independence, and per-goal accounting remain
///   prose-only: neither an event trace nor an independent execution is
///   available to a return predicate.
/// - fails: any [`KernelError`] the checker surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L2 — the differential over the corpus pins memoized against
///   memoless, verdict for verdict; the L3 residue is the stale-entry hazard,
///   pinned by poisoned-memo witnesses that provably change an answer in both
///   directions and on both planes.
/// - witness: `acceptance::acceptance::memoized_checking_agrees_with_memoless_checking`
/// - witness: `acceptance::acceptance::a_poisoned_term_entry_turns_a_refusal_into_an_acceptance`
/// - witness: `acceptance::acceptance::a_poisoned_type_entry_turns_admission_into_a_universe_refusal`
#[inline]
pub fn check_declaration_with_memo<M>(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    levels: &LevelContext,
    declaration: &Declaration,
    memo: &mut M,
    session: &mut SupportContext,
    census: &mut ExpansionCensus,
) -> Result<(), KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let declared = declaration.declared_id();
    let judgement = Judgement::new(entries, levels);
    let mut owed: Vec<CodeObligation> = Vec::new();
    let _level = type_level(
        arena,
        judgement,
        TypeLevelGoal::Value(declared),
        Vec::new(),
        Recording {
            memo,
            session,
            census,
            owed: &mut owed,
        },
    )?;
    check_sealing_provenance(arena, declared, declaration.provenance())?;
    let verdict = match *declaration.content() {
        | DeclarationContent::Def { declared, body } => {
            let context: Vec<ValueTypeId> = Vec::new();
            let _checked = run(
                arena,
                judgement,
                context,
                Goal::CheckValue(body, declared),
                Recording {
                    memo,
                    session,
                    census,
                    owed: &mut owed,
                },
            )?;
            Ok(())
        },
        | DeclarationContent::Axiom { .. } => Ok(()),
        // A sealed atom's whole admission obligation is that its kind is a
        // universe. There is no body to check and no inhabitant claimed, so the
        // kernel takes on nothing further — the property the atom route was
        // chosen for.
        | DeclarationContent::AbstractType { kind } => {
            let kind_node = arena.value_type(kind).ok_or(KernelError::ArenaFault)?;
            match *kind_node {
                | ValueType::Universe(_) => Ok(()),
                | ValueType::Base(_)
                | ValueType::Unit
                | ValueType::Product(..)
                | ValueType::Sum(..)
                | ValueType::Thunk(_)
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_) => Err(KernelError::AbstractTypeKindNotUniverse {
                    actual: value_type_witness(arena, kind),
                }),
            }
        },
    };
    verdict?;
    drain_code_obligations(arena, judgement, memo, session, census, owed)
}

/// Check every code a formation walk owed, and every code those checks owe in
/// turn.
///
/// # Specification
/// - requires: `owed` holds the obligations the declaration's own walks
///   recorded, each with the context its code stands in.
/// - ensures: `Ok(())` exactly when every reachable code checks against the
///   universe the type that carried it named. The drain is a loop over an
///   explicit worklist, not recursion, and a check it runs may append further
///   obligations to the same worklist.
/// - provides: the half of type formation the formation walk deferred, run
///   through the checking machine so the two walks never call one another.
///   Obligation provenance and recursive closure remain prose-only: the
///   worklist is consumed and extended during checking, so a predicate would
///   need a copied worklist and another complete check.
/// - fails: [`KernelError::CodeObligationCeiling`] when the drain exceeds
///   [`MAX_CODE_OBLIGATIONS`]; any [`KernelError`] a code's check surfaces.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the drain is a loop over an explicit worklist, not recursion.
/// - measure: the ceiling minus the number of obligations already drained,
///   which strictly falls at every iteration and is checked before the body
///   runs.
/// - boundedness: a check that owes more obligations than the ceiling allows is
///   refused rather than pursued, so the loop cannot run more than
///   [`MAX_CODE_OBLIGATIONS`] times whatever the artifact contains.
/// - input recursion: none — a drained check appends to this worklist rather
///   than re-entering this function.
///
/// # Adequacy
/// - hypothesis: L3 — the drain's surface is separated by a code that checks
///   (admission) and a code that does not (the code's own refusal reaching the
///   caller), and the drain is shown to reach the checking machine at all by an
///   expansion-count inequality against the same shape with closed types. **The
///   ceiling arm carries no witness, and two things about it are recorded
///   findings rather than omissions.** First, tripping it needs a workload
///   whose obligation count clears a quarter of a million; the count is not
///   bounded by the artifact's entry count — a drained check forms types over
///   nodes it just minted — so a case that reached the arm would be a
///   constructed pathology sized to the constant rather than a separation of
///   the arm. Second, the count is **occurrence-based**: an obligation is
///   pushed per expansion, and a memo hit skips the push, so the memoized and
///   memoless paths reach the ceiling at different workloads. That divergence
///   is confined to the refusal direction — the memoized path pushes no more
///   obligations than the memoless one, so it can only refuse later, never
///   accept something the memoless path refuses — and at this constant neither
///   path reaches it, which is why the zero-drift differential is silent on it
///   rather than failing.
/// - witness: `check::tests::a_dependent_identity_checks_through_its_codes`
/// - witness: `check::tests::a_code_that_is_not_of_its_declared_universe_refuses`
/// - witness: `acceptance::acceptance::draining_code_obligations_reaches_the_checking_machine`
fn drain_code_obligations<M>(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    memo: &mut M,
    session: &mut SupportContext,
    census: &mut ExpansionCensus,
    mut owed: Vec<CodeObligation>,
) -> Result<(), KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let mut drained: usize = 0;
    while let Some(obligation) = owed.pop() {
        if drained >= usize::from(MAX_CODE_OBLIGATIONS) {
            return Err(KernelError::CodeObligationCeiling {
                ceiling: MAX_CODE_OBLIGATIONS,
            });
        }
        drained = drained.saturating_add(1);
        let universe = arena.value_type_universe(obligation.level);
        let _checked = run(
            arena,
            judgement,
            obligation.context,
            Goal::CheckValue(obligation.code, universe),
            Recording {
                memo,
                session,
                census,
                owed: &mut owed,
            },
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::ComputationId;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::LevelParamCount;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::ValueTypeId;

    use super::Goal;
    use super::Judgement;
    use super::Produced;
    use super::Recording;
    use super::TypeLevelGoal;
    use super::run;
    use super::type_level;
    use crate::census::ExpansionCensus;
    use crate::env::AdmittedDeclaration;
    use crate::env::Environment;
    use crate::error::ExpectedValueShape;
    use crate::error::KernelError;
    use crate::error::NonInferableForm;
    use crate::error::RegisterFault;
    use crate::levels::LevelContext;
    use crate::support::SupportContext;

    /// No prior declarations.
    ///
    /// # Specification
    /// trivial.
    fn no_entries() -> Vec<AdmittedDeclaration>
    {
        Vec::new()
    }

    /// An unconstrained level context over `params` prenex parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level context over `params` prenex parameters with no
    ///   declared constraints, whose universe judgements are the free-fragment
    ///   oracle's.
    /// - provides: the level context the machine cases run under.
    /// - fails: never.
    /// - panics: when admission refuses, which an empty constraint set never
    ///   does.
    fn level_context(params: LevelParamCount) -> LevelContext
    {
        LevelContext::admit(params, Vec::new()).expect("an unconstrained context admits")
    }

    /// The constant level `value`.
    ///
    /// # Specification
    /// trivial.
    fn level(value: LevelConstant) -> Level
    {
        Level::constant(value)
    }

    /// Synthesize a value's type in a bare arena under `context`.
    ///
    /// # Specification
    /// - requires: `context` is the typing context the value stands in, and
    ///   `arena` holds it.
    /// - ensures: the machine's answer for a value-synthesis goal, run at the
    ///   null memo with a fresh session and census, so the case observes the
    ///   unmemoized path.
    /// - provides: the synthesis fixture the value rules are asserted through.
    /// - fails: whatever the machine refuses the goal with.
    /// - panics: none.
    fn synth_value(
        arena: &mut TermArena,
        context: Vec<ValueTypeId>,
        value: ValueId,
    ) -> Result<Produced, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        run(
            arena,
            Judgement::new(&entries, &context_levels),
            context,
            Goal::SynthValue(value),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    /// Check a value against an expected type in a bare arena.
    ///
    /// # Specification
    /// - requires: `context` is the typing context the value stands in, and
    ///   `arena` holds both the value and `expected`.
    /// - ensures: the machine's answer for a checking goal, run at the null
    ///   memo with a fresh session and census.
    /// - provides: the checking fixture the value rules are asserted through.
    /// - fails: whatever the machine refuses the goal with.
    /// - panics: none.
    fn check_value(
        arena: &mut TermArena,
        context: Vec<ValueTypeId>,
        value: ValueId,
        expected: ValueTypeId,
    ) -> Result<Produced, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        run(
            arena,
            Judgement::new(&entries, &context_levels),
            context,
            Goal::CheckValue(value, expected),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    /// Synthesize a computation's type in a bare arena.
    ///
    /// # Specification
    /// - requires: `context` is the typing context the computation stands in,
    ///   and `arena` holds it.
    /// - ensures: the machine's answer for a computation-synthesis goal, run at
    ///   the null memo with a fresh session and census.
    /// - provides: the synthesis fixture the computation rules are asserted
    ///   through.
    /// - fails: whatever the machine refuses the goal with.
    /// - panics: none.
    fn synth_comp(
        arena: &mut TermArena,
        context: Vec<ValueTypeId>,
        computation: ComputationId,
    ) -> Result<Produced, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        run(
            arena,
            Judgement::new(&entries, &context_levels),
            context,
            Goal::SynthComp(computation),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    /// The level of a value type in a bare arena.
    ///
    /// # Specification
    /// - requires: `arena` holds `root`.
    /// - ensures: the universe level the formation walk reads off `root`, run
    ///   at the null memo with a fresh session and census and with its code
    ///   obligations discarded.
    /// - provides: the formation fixture the type rules are asserted through.
    /// - fails: whatever the formation walk refuses the type with.
    /// - panics: none.
    fn value_level(
        arena: &TermArena,
        root: ValueTypeId,
    ) -> Result<Level, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        type_level(
            arena,
            Judgement::new(&entries, &context_levels),
            TypeLevelGoal::Value(root),
            Vec::new(),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    #[test]
    fn a_variable_synthesizes_its_context_type()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let produced = synth_value(&mut arena, vec![unit, integer], variable)
            .expect("an in-scope variable synthesizes");
        assert_eq!(
            integer,
            produced.value_type().expect("a value type"),
            "index zero names the innermost slot"
        );
        let escaping = arena.value_variable(DeBruijnIndex::from(2_u32));
        assert_eq!(
            Err(KernelError::UnboundVariable {
                index: DeBruijnIndex::from(2_u32)
            }),
            synth_value(&mut arena, vec![unit, integer], escaping),
            "and an index past the context escapes"
        );
    }

    #[test]
    fn an_injection_is_not_inferable()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let injection = arena.value_injection(Side::Left, unit);
        assert_eq!(
            Err(KernelError::NotInferable {
                form: NonInferableForm::Injection
            }),
            synth_value(&mut arena, Vec::new(), injection),
            "an injection carries no record of which sum it injects into"
        );
    }

    #[test]
    fn an_injection_checks_against_its_sum()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let sum = arena.value_type_sum(unit_type, integer);
        let left = arena.value_injection(Side::Left, unit);
        assert!(
            check_value(&mut arena, Vec::new(), left, sum).is_ok(),
            "the left injection checks against the left summand"
        );
        let right = arena.value_injection(Side::Right, unit);
        assert!(
            matches!(
                check_value(&mut arena, Vec::new(), right, sum),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "and the right injection is checked against the right summand, which unit is not"
        );
        let refused = check_value(&mut arena, Vec::new(), left, unit_type);
        assert!(
            matches!(
                refused,
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Sum,
                    ..
                })
            ),
            "and a non-sum expected type is a shape mismatch: {refused:?}"
        );
    }

    #[test]
    fn a_pair_propagates_into_a_checking_component()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let injection = arena.value_injection(Side::Left, unit);
        let sum = arena.value_type_sum(unit_type, integer);
        let pair = arena.value_pair(unit, injection);
        let product = arena.value_type_product(unit_type, sum);
        assert!(
            check_value(&mut arena, Vec::new(), pair, product).is_ok(),
            "the expected product flows into both components, so the checking-only injection \
             reaches its sum"
        );
        assert!(
            matches!(
                synth_value(&mut arena, Vec::new(), pair),
                Err(KernelError::NotInferable {
                    form: NonInferableForm::Injection
                })
            ),
            "and the same pair does not synthesize, since nothing tells the injection its sum"
        );
    }

    #[test]
    fn an_application_produces_the_codomain()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(unit_type, returner);
        let thunk_type = arena.value_type_thunk(arrow);
        let head_variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let head = arena.computation_force(head_variable);
        let unit = arena.value_unit();
        let application = arena.computation_application(head, unit);
        let produced = synth_comp(&mut arena, vec![thunk_type], application)
            .expect("an application of a forced thunk synthesizes");
        assert_eq!(
            returner,
            produced.comp_type().expect("a computation type"),
            "an application produces its head's codomain"
        );
    }

    #[test]
    fn a_force_unwraps_a_thunk()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit_type);
        let thunk_type = arena.value_type_thunk(returner);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let force = arena.computation_force(variable);
        let produced =
            synth_comp(&mut arena, vec![thunk_type], force).expect("forcing a thunk synthesizes");
        assert_eq!(
            returner,
            produced.comp_type().expect("a computation type"),
            "a force yields the thunked computation type"
        );
        let not_a_thunk = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bad_force = arena.computation_force(not_a_thunk);
        assert!(
            matches!(
                synth_comp(&mut arena, vec![unit_type], bad_force),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Thunk,
                    ..
                })
            ),
            "and forcing a non-thunk is a shape mismatch"
        );
    }

    #[test]
    fn a_bind_binds_the_returned_value()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let thunk_type = arena.value_type_thunk(returner);
        let held = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.computation_force(held);
        // The body reads the payload the bind introduced, at index zero.
        let payload = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(payload);
        let sequence = arena.computation_bind(bound, body);
        let produced = synth_comp(&mut arena, vec![thunk_type], sequence)
            .expect("a bind over a returner synthesizes");
        let produced_type = produced.comp_type().expect("a computation type");
        let read = arena.comp_type(produced_type).expect("the type resolves");
        assert!(
            matches!(*read, CompType::Returner(result) if result == integer),
            "the body sees the bound payload's type, so the bind returns it"
        );
    }

    #[test]
    fn a_case_requires_convergent_branches()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let sum = arena.value_type_sum(unit_type, unit_type);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let left = arena.computation_return(bound);
        let right = arena.computation_return(bound);
        let case = arena.computation_case(scrutinee, left, right);
        assert!(
            synth_comp(&mut arena, vec![sum], case).is_ok(),
            "two branches returning their own summand converge when the summands agree"
        );

        let mixed = arena.value_type_sum(unit_type, integer);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let case = arena.computation_case(scrutinee, left, right);
        assert!(
            matches!(
                synth_comp(&mut arena, vec![mixed], case),
                Err(KernelError::CaseBranchMismatch(_))
            ),
            "and they diverge when the summands do"
        );
    }

    #[test]
    fn a_case_propagates_the_expected_type()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let mixed = arena.value_type_sum(unit_type, integer);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit = arena.value_unit();
        let left = arena.computation_return(unit);
        let right = arena.computation_return(unit);
        let case = arena.computation_case(scrutinee, left, right);
        let expected = arena.comp_type_returner(unit_type);
        let thunk = arena.value_thunk(case);
        let thunk_type = arena.value_type_thunk(expected);
        assert!(
            check_value(&mut arena, vec![mixed], thunk, thunk_type).is_ok(),
            "checking pushes one expected type into both branches, where synthesis would have \
             required them to agree on their own"
        );
    }

    #[test]
    fn a_universe_forms_one_level_up()
    {
        let mut arena = TermArena::new();
        let universe = arena.value_type_universe(level(LevelConstant::from(3)));
        assert_eq!(
            Ok(level(LevelConstant::from(4))),
            value_level(&arena, universe),
            "the universe at l forms at l + 1"
        );
        let unit = arena.value_type_unit();
        assert_eq!(
            Ok(level(LevelConstant::from(0))),
            value_level(&arena, unit),
            "and a small type forms at zero"
        );
    }

    #[test]
    fn a_lift_requires_a_strictly_higher_target()
    {
        let mut arena = TermArena::new();
        let universe = arena.value_type_universe(level(LevelConstant::from(1)));
        let raised = arena.value_type_lift(universe, level(LevelConstant::from(5)));
        assert_eq!(
            Ok(level(LevelConstant::from(5))),
            value_level(&arena, raised),
            "a lift forms at its target"
        );
        // `Universe(1)` itself forms at level 2, so 3 is the first admissible
        // target and 2 is the boundary that does not strictly raise.
        let boundary = arena.value_type_lift(universe, level(LevelConstant::from(3)));
        assert_eq!(
            Ok(level(LevelConstant::from(3))),
            value_level(&arena, boundary),
            "one above the inner type's own level is admissible"
        );
        let sunk = arena.value_type_lift(universe, level(LevelConstant::from(2)));
        assert!(
            matches!(
                value_level(&arena, sunk),
                Err(KernelError::UniverseViolation(_))
            ),
            "and a target at the inner type's own level does not strictly raise"
        );
    }

    #[test]
    fn an_arrow_forms_at_the_join_of_its_children()
    {
        let mut arena = TermArena::new();
        let low = arena.value_type_universe(level(LevelConstant::from(1)));
        let high = arena.value_type_universe(level(LevelConstant::from(4)));
        let returner = arena.comp_type_returner(high);
        let arrow = arena.comp_type_arrow(low, returner);
        let thunk = arena.value_type_thunk(arrow);
        assert_eq!(
            Ok(level(LevelConstant::from(5))),
            value_level(&arena, thunk),
            "the arrow takes the maximum of its domain's and codomain's levels"
        );
    }

    /// The dependent arrow forms like the arrow, checks a lambda like the
    /// arrow, and eliminates like the arrow. Three assertions in one case
    /// because they are one claim: at a type vocabulary with no former indexed
    /// by a value term, the binder the dependent arrow scopes its codomain
    /// under is the context slot a lambda's check already pushes, and
    /// instantiating the codomain at the argument moves nothing.
    #[test]
    fn a_dependent_arrow_forms_checks_and_eliminates_like_an_arrow()
    {
        let mut arena = TermArena::new();
        let low = arena.value_type_universe(level(LevelConstant::from(1)));
        let high = arena.value_type_universe(level(LevelConstant::from(4)));
        let returner = arena.comp_type_returner(high);
        let dependent = arena.comp_type_pi(low, returner);
        let thunk = arena.value_type_thunk(dependent);
        assert_eq!(
            Ok(level(LevelConstant::from(5))),
            value_level(&arena, thunk),
            "the dependent arrow forms at the join of its domain's and codomain's levels"
        );

        let unit_type = arena.value_type_unit();
        let unit_returner = arena.comp_type_returner(unit_type);
        let identity = arena.comp_type_pi(unit_type, unit_returner);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(bound);
        let lambda = arena.computation_lambda(body);
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        let checked = run(
            &mut arena,
            Judgement::new(&entries, &context_levels),
            Vec::new(),
            Goal::CheckComp(lambda, identity),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        );
        assert_eq!(
            Ok(Produced::Checked),
            checked,
            "a lambda checks against a dependent arrow through the domain it pushes"
        );

        let head_thunk = arena.value_type_thunk(identity);
        let head_variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let head = arena.computation_force(head_variable);
        let unit = arena.value_unit();
        let application = arena.computation_application(head, unit);
        let produced = synth_comp(&mut arena, vec![head_thunk], application)
            .expect("an application at a dependent head synthesizes");
        assert_eq!(
            unit_returner,
            produced.comp_type().expect("a computation type"),
            "and the elimination produces the codomain, which no term occurs in to substitute for"
        );
    }

    #[test]
    fn an_abstract_type_forms_at_its_declared_universe()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(level(LevelConstant::from(2)));
            staging.abstract_type(LevelSignature::monomorphic(), kind)
        };
        let _admitted = environment
            .add_decl(atom)
            .expect("an abstract type at a universe kind admits");
        let definition = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_universe(level(LevelConstant::from(9)));
            let _inner = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let _second = environment
            .add_decl(definition)
            .expect("an axiom at a universe admits");

        // The atom's own formation level is read off the kind its declaration
        // fixed, which is the whole rule.
        let referencing = {
            let mut staging = environment.stage();
            let atom_type = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let raised = staging
                .arena()
                .value_type_lift(atom_type, level(LevelConstant::from(3)));
            staging.axiom(LevelSignature::monomorphic(), raised)
        };
        assert!(
            environment.add_decl(referencing).is_ok(),
            "a lift of the atom to one level above its declared kind admits"
        );
        let too_low = {
            let mut staging = environment.stage();
            let atom_type = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let raised = staging
                .arena()
                .value_type_lift(atom_type, level(LevelConstant::from(2)));
            staging.axiom(LevelSignature::monomorphic(), raised)
        };
        assert!(
            matches!(
                environment.add_decl(too_low),
                Err(KernelError::UniverseViolation(_))
            ),
            "and a lift to the atom's own level does not, so the level came from the kind"
        );
    }

    #[test]
    fn an_atom_naming_a_definition_is_not_an_abstract_type()
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let _admitted = environment
            .add_decl(definition)
            .expect("a unit definition admits");
        let forged = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert_eq!(
            Err(KernelError::NotAnAbstractType {
                index: ConstantIndex::from(0_usize)
            }),
            environment.add_decl(forged).map(|_admitted| ()),
            "nothing in an artifact says 'I am an atom'; the kernel resolves the position"
        );
    }

    #[test]
    fn a_forward_atom_reference_is_not_an_abstract_type()
    {
        let mut environment = Environment::new();
        let forward = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(7_usize));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert_eq!(
            Err(KernelError::NotAnAbstractType {
                index: ConstantIndex::from(7_usize)
            }),
            environment.add_decl(forward).map(|_admitted| ()),
            "an out-of-range position resolves to nothing and is refused"
        );
    }

    #[test]
    fn an_identity_thunk_checks()
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let integer = staging.arena().value_type_base(BaseType::Integer);
            let returner = staging.arena().comp_type_returner(integer);
            let arrow = staging.arena().comp_type_arrow(integer, returner);
            let declared = staging.arena().value_type_thunk(arrow);
            let variable = staging.arena().value_variable(DeBruijnIndex::from(0_u32));
            let body = staging.arena().computation_return(variable);
            let lambda = staging.arena().computation_lambda(body);
            let thunk = staging.arena().value_thunk(lambda);
            staging.def(LevelSignature::monomorphic(), declared, thunk)
        };
        assert!(
            environment.add_decl(definition).is_ok(),
            "the identity on integers admits through the checked choke point"
        );
    }

    /// The polymorphic identity, admitted through the public choke point.
    ///
    /// `Π (A : U 0). Π (_ : El A). F (El A)` is the smallest declaration that
    /// makes every part of the dependent machinery load-bearing at once: the
    /// codomain mentions the binder through a code, so the context stops
    /// holding closed types and a variable synthesis has to shift its slot;
    /// the formation walk owes two code obligations and the driver drains
    /// both through the checking machine; and the mode switch at the
    /// returned variable converts two codes rather than two closed types.
    #[test]
    fn a_dependent_identity_checks_through_its_codes()
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let zero = level(LevelConstant::from(0));
            let mint = staging.arena();
            let universe = mint.value_type_universe(zero.clone());
            let outer_code = mint.value_variable(DeBruijnIndex::from(0_u32));
            let domain = mint.value_type_element(outer_code, zero.clone());
            let inner_code = mint.value_variable(DeBruijnIndex::from(1_u32));
            let result = mint.value_type_element(inner_code, zero);
            let returner = mint.comp_type_returner(result);
            let inner = mint.comp_type_pi(domain, returner);
            let outer = mint.comp_type_pi(universe, inner);
            let declared = mint.value_type_thunk(outer);

            let returned = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(returned);
            let inner_lambda = mint.computation_lambda(body);
            let outer_lambda = mint.computation_lambda(inner_lambda);
            let thunk = mint.value_thunk(outer_lambda);
            staging.def(LevelSignature::monomorphic(), declared, thunk)
        };
        assert_eq!(
            Ok(()),
            environment.add_decl(definition).map(|_admitted| ()),
            "the dependent identity admits through the checked choke point"
        );
    }

    /// A code whose type is not the universe its own node claimed is refused,
    /// and the refusal is the ordinary conversion mismatch rather than a
    /// special one — the carried level is checked exactly like every other
    /// obligation the kernel re-derives.
    #[test]
    fn a_code_that_is_not_of_its_declared_universe_refuses()
    {
        let mut environment = Environment::new();
        let axiom = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            // The unit *value* is not a code: its type is the unit type, not a
            // universe, so the type read off it does not form.
            let not_a_code = mint.value_unit();
            let declared = mint.value_type_element(not_a_code, level(LevelConstant::from(0)));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert!(
            matches!(
                environment.add_decl(axiom),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "a code that does not inhabit the universe its type named is refused"
        );
    }

    /// Instantiating a dependent codomain at an argument is observable now that
    /// a codomain can mention its binder: applying the polymorphic identity's
    /// type to a code produces the arrow over *that* code.
    #[test]
    fn an_application_instantiates_a_dependent_codomain()
    {
        let mut arena = TermArena::new();
        let zero = level(LevelConstant::from(0));
        let universe = arena.value_type_universe(zero.clone());
        let bound_code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound_element = arena.value_type_element(bound_code, zero.clone());
        let returner = arena.comp_type_returner(bound_element);
        let dependent = arena.comp_type_pi(universe, returner);
        let head_thunk = arena.value_type_thunk(dependent);

        // The argument is an outer variable naming a code, so the instantiated
        // codomain has to name *it* rather than the vanished binder.
        let argument = arena.value_variable(DeBruijnIndex::from(1_u32));
        let head_variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let head = arena.computation_force(head_variable);
        let application = arena.computation_application(head, argument);
        let outer_universe = arena.value_type_universe(zero);
        let produced = synth_comp(&mut arena, vec![outer_universe, head_thunk], application)
            .expect("the dependent application synthesizes");
        let synthesized = produced.comp_type().expect("a computation type");
        let Some(&CompType::Returner(result)) = arena.comp_type(synthesized)
        else {
            panic!("the instantiated codomain is a returner");
        };
        let Some(&ValueType::Element { code, .. }) = arena.value_type(result)
        else {
            panic!("over a type read off a code");
        };
        assert_eq!(
            Some(&Value::Variable(DeBruijnIndex::from(1_u32))),
            arena.value(code),
            "the codomain names the argument rather than the binder that vanished"
        );
    }

    #[test]
    fn an_axiom_checks_only_its_type()
    {
        let mut environment = Environment::new();
        let axiom = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert!(
            environment.add_decl(axiom).is_ok(),
            "an axiom claims an inhabitant and offers no body, so only its type is checked"
        );
    }

    #[test]
    fn a_sealed_atom_checks_only_its_kind()
    {
        let mut environment = Environment::new();
        let bad = {
            let mut staging = environment.stage();
            let kind = staging.arena().value_type_unit();
            staging.abstract_type(LevelSignature::monomorphic(), kind)
        };
        assert!(
            matches!(
                environment.add_decl(bad),
                Err(KernelError::AbstractTypeKindNotUniverse { .. })
            ),
            "an atom whose kind is not a universe would leave formation with a level to infer"
        );
    }

    #[test]
    fn sealing_provenance_must_occur_in_the_declared_type()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(level(LevelConstant::from(0)));
            staging.abstract_type(LevelSignature::monomorphic(), kind)
        };
        let _admitted = environment.add_decl(atom).expect("an atom admits");
        let claiming = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![
                ConstantIndex::from(0_usize),
            ])
        };
        assert_eq!(
            Err(KernelError::SealingProvenanceNotProjected {
                atom: ConstantIndex::from(0_usize)
            }),
            environment.add_decl(claiming).map(|_admitted| ()),
            "a provenance entry with no occurrence is an unfalsifiable claim"
        );
    }

    #[test]
    fn sealing_provenance_must_be_strictly_ascending()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(level(LevelConstant::from(0)));
            staging.abstract_type(LevelSignature::monomorphic(), kind)
        };
        let _admitted = environment.add_decl(atom).expect("an atom admits");
        let repeated = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let body = staging.arena().value_unit();
            staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![
                ConstantIndex::from(0_usize),
                ConstantIndex::from(0_usize),
            ])
        };
        assert_eq!(
            Err(KernelError::SealingProvenanceNotCanonical {
                atom: ConstantIndex::from(0_usize)
            }),
            environment.add_decl(repeated).map(|_admitted| ()),
            "canonical order is what makes the slot a set with one spelling"
        );
    }

    #[test]
    fn register_polarity_faults_fail_closed()
    {
        assert_eq!(
            Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedValueType
            )),
            Produced::Checked.value_type(),
            "a wiring defect refuses rather than fabricating a type"
        );
        assert_eq!(
            Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedCompType
            )),
            Produced::Checked.comp_type(),
            "on both polarities"
        );
    }
}
