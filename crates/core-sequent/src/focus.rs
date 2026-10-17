//! Focusing: the translation `𝓕⟦M⟧c` of a core computation under a
//! continuation into a command, and `𝓥⟦v⟧` of a core value into a producer.
//!
//! ```text
//! 𝓥⟦x⟧            = x                       𝓥⟦thunk M⟧ = {force(α) ⇒ 𝓕⟦M⟧α}
//! 𝓥⟦()⟧, 𝓥⟦(v, w)⟧, 𝓥⟦inj v⟧, 𝓥⟦lift v⟧    = the constructor over the images
//! 𝓥⟦c_i(v̄)⟧        = ctor[i](𝓥⟦v̄⟧)            the datatype erased
//! 𝓥⟦{l̄ = v̄}⟧       = record{l̄}(𝓥⟦v̄⟧)          the labels in canonical order
//!
//! 𝓕⟦return v⟧c    = ⟨𝓥⟦v⟧ |+ c⟩
//! 𝓕⟦force v⟧c     = ⟨𝓥⟦v⟧ |+ force(c)⟩
//! 𝓕⟦M v⟧c         = 𝓕⟦M⟧(apply(𝓥⟦v⟧; c))
//! 𝓕⟦λ. M⟧c        = ⟨cocase {apply(x; α) ⇒ 𝓕⟦M⟧α} |− c⟩
//! 𝓕⟦fix x. M⟧c    = ⟨fix{x; force(α) ⇒ 𝓕⟦M⟧α} |+ force(c)⟩
//! 𝓕⟦x ← M; N⟧c    = 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧c)                       c a tail
//!                 = ⟨μα. 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧α) |ε c⟩              otherwise
//! 𝓕⟦case v {l, r}⟧c = ⟨𝓥⟦v⟧ |+ case {inl(x) ⇒ 𝓕⟦l⟧c, inr(x) ⇒ 𝓕⟦r⟧c}⟩   c a tail
//!                 = ⟨μα. ⟨𝓥⟦v⟧ |+ case {… 𝓕⟦·⟧α …}⟩ |ε c⟩     otherwise
//! 𝓕⟦case v [C] of {b̄}⟧c = ⟨𝓥⟦v⟧ |+ datacase(𝓥⟦thunk b̄⟧; c)⟩   the motive erased
//! 𝓕⟦v.i⟧c, 𝓕⟦v.l⟧c = ⟨𝓥⟦v⟧ |+ select[i](c)⟩, ⟨𝓥⟦v⟧ |+ select[.l](c)⟩
//! ```
//!
//! A tail is a covariable or `★`. A continuation that is not a tail is never
//! placed under a binder: a bind or a case names it with a `μ`, at the
//! polarity of what it observes. Every continuation passed under a binder is
//! therefore a tail, every focused covariable is index `0`, and producer
//! indices are the core's own, so the translation shifts nothing and mints no
//! name. A core value is never a `μ`, so every argument of a focused frame
//! and every field of a focused constructor is a value.
//!
//! Every walk here is a loop over an explicit task stack, so no term's depth
//! reaches the call stack. A refused translation truncates the arena and the
//! provenance table to the marks taken on entry.
//!
//! # Focusing names only what is not a tail
//!
//! Focusing translates a computation `M` under a continuation `c` into a
//! command, `𝓕⟦M⟧c`, and a value `v` into a producer, `𝓥⟦v⟧`:
//!
//! ```text
//! 𝓥⟦x⟧ = x        𝓥⟦thunk M⟧ = {force(α) ⇒ 𝓕⟦M⟧α}        𝓥⟦(v̄)⟧, 𝓥⟦inj_i v⟧, 𝓥⟦lift v⟧ = the constructor
//! 𝓥⟦c_i(v̄)⟧ = ctor[i](𝓥⟦v̄⟧)        𝓥⟦{l̄ = v̄}⟧ = record{l̄}(𝓥⟦v̄⟧)
//!
//! 𝓕⟦return v⟧c        = ⟨𝓥⟦v⟧ |+ c⟩
//! 𝓕⟦force v⟧c         = ⟨𝓥⟦v⟧ |+ force(c)⟩
//! 𝓕⟦M v⟧c             = 𝓕⟦M⟧(apply(𝓥⟦v⟧; c))
//! 𝓕⟦λ. M⟧c            = ⟨cocase {apply(x; α) ⇒ 𝓕⟦M⟧α} |− c⟩
//! 𝓕⟦x ← M; N⟧c        = 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧c)                         c a tail
//!                     = ⟨μα. 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧α) |ε c⟩                otherwise
//! 𝓕⟦case v {b̄}⟧c     = ⟨𝓥⟦v⟧ |+ case {inj_i(x) ⇒ 𝓕⟦b_i⟧c, …}⟩       c a tail
//!                     = ⟨μα. ⟨𝓥⟦v⟧ |+ case {… 𝓕⟦·⟧α …}⟩ |ε c⟩        otherwise
//! 𝓕⟦case_D v {b̄}⟧c   = ⟨𝓥⟦v⟧ |+ datacase({force(α) ⇒ 𝓕⟦b_i⟧α}, …; c)⟩
//! 𝓕⟦v.i⟧c             = ⟨𝓥⟦v⟧ |+ select[i](c)⟩
//! 𝓕⟦v.l⟧c             = ⟨𝓥⟦v⟧ |+ select[.l](c)⟩
//! 𝓕⟦fix x. M⟧c        = ⟨fix{x; force(α) ⇒ 𝓕⟦M⟧α} |+ force(c)⟩
//! ```
//!
//! A tail is a covariable or `★`. A bind and a case open a producer binder, and
//! a continuation that is not a tail — a frame, a `μ̃` — carries producers
//! whose indices would have to shift under it; so such a continuation is named
//! once with a `μ`, at the polarity of what it observes, and the binder sees
//! only the tail `α0`. A nominal match opens no binder of its own: each branch
//! is a thunk of the function over the fields the core writes, and the match's
//! continuation `c` is carried once, beside the branches, so it is neither
//! shifted nor named; a selection carries its continuation the same way.
//! Every continuation that crosses a binder is then a tail, nothing is shifted
//! or copied, every focused covariable is index `0`, and two focusings of one
//! term build identical arenas. A core value is never a `μ`, so every frame
//! argument and constructor field of an image is a value. `Provenance`
//! records, for each command focusing creates, the core former it was created
//! for. A refused translation truncates the arena and the provenance table to
//! the marks it took on entry.
//!
//! Passing a continuation unchanged under a binder is sound for named
//! covariables but not for indexed producer operands. Shifting its producers
//! under every binder would copy a frame subtree at each crossing. Naming it
//! once instead costs one extra cut and one bound mark for a non-tail bind or
//! case. Revisit if measurement shows that cut costs more than a shift memoized
//! per frame.
//!
//! Tuples, injections and sum cases are n-ary, as in the core: a tuple is one
//! `Tuple(n)` head with `n` fields, so the empty tuple is the unit; an
//! injection is `Injection(i)` for the summand `i`; and a case carries one arm
//! per summand, in summand order, so a case of no arms is the empty sum's
//! eliminator. The alternative was a binary IL with nested pairs and
//! injections, which focusing could reach by re-associating the core's n-ary
//! formers, at the cost of a readback that cannot tell `(a, (b, c))` from `(a,
//! b, c)`. The pretty printer spells the binary heads `unit`, `pair`, `inl` and
//! `inr`, and the others `tuple` and `inj[i]`. Revisit if a consumer of the IL
//! needs a fixed set of heads.
//!
//! # Records carry their labels
//!
//! A record focuses to one `Record(labels)` head over its fields, the labels in
//! the core's canonical order and each field under its own label. A tuple
//! projection and a record projection focus to the positive cut of their
//! subject against a selection, `select[i](c)` or `select[.l](c)`, which names
//! the field and carries the projection's continuation beside it. The machine
//! reads the field's place from the head the selection meets: component `i` of
//! a `Tuple(n)`, or the field under `l` among a record's labels. A selection
//! that meets a value without its field is stuck as an unmatched match is.
//!
//! The core record has width and depth subtyping: a record of more labels
//! checks where one of fewer is expected, so a projection's static type fixes
//! neither the width of the value it meets nor the place of its label. The
//! alternatives each fixed a place at focusing time: elaborating a projection
//! to a `split` of the arity and at the position its type states, which
//! mis-splits a wider record that width subtyping admitted; a positional
//! selection alone, which has no place to read for a label; and a destructor
//! per label, which puts a string into the copyable destructor tag every frame
//! carries. The record of no labels stays a record rather than the unit, so
//! readback returns the record the core wrote.
//!
//! Revisit when the core record becomes an ordered telescope without width
//! subtyping: its fields then have a static place, so a record focuses as
//! `Tuple(n)` in its written order and a projection as the split at its place,
//! and the labels leave the IL.
//!
//! # A code has no producer
//!
//! A quote is a runtime value of a universe, but the IL has no producer for
//! that value. Its owned annotation arena carries types for List folds and
//! effect interfaces, not executable code values. Focusing therefore refuses
//! quotes and static code operators with `FocusRefusal::Code` and restores its
//! marks. Keeping a foreign core-arena reference would tie the runtime to that
//! arena; erasing a code to unit would corrupt readback. Revisit only when code
//! values have a runtime representation that preserves their meaning.
//!
//! # Native universe paths
//!
//! Native path values and `Transport` have no image in the command IL. Focusing
//! answers `FocusRefusal::UniverseTransport` and restores the command arena and
//! provenance to their entry marks. `Path_U` transport is computed by
//! `core-nbe` and checked by kernel replay; accepting a native certificate does
//! not authorize this machine to erase its evidence or invent a producer.
//!
//! **Choice.** An explicit refusal, rather than lowering a path to a pair of
//! functions without the obligations that certify it. **Reversal.** A
//! command-level image must specify its types, eliminations and certified
//! readback before focusing admits it. The in-memory bridge mode, higher
//! fields, funext and guarded List observations likewise remain outside this
//! IL. A flow is the exception: it carries no evidence the machine needs, and
//! runs as its translator ([`crate::flow`]).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::NodeCount;
use crate::boundary::ProducerArity;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CopatternArm;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::Introduces;
use crate::il::MintRefusal;
use crate::il::PatternArm;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::Route;
use crate::il::Selector;

/// The source construct a focused command was created for: the un-sugaring
/// view of a focused term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FocusOrigin
{
    /// An operation request with its inline interface.
    Perform,
    /// A deep handler with explicit return and operation clauses.
    Handle,
    /// An operation exercised through a capability.
    Exercise,
    /// A deep handler introducing the capability its subject exercises.
    Scope,
    /// A first-class stack resumption.
    Resume,
    /// A delimited answer context.
    Reset,
    /// A delimited continuation capture.
    Shift,
    /// A lazy pair of computations.
    With,
    /// `return v`: the cut of the value against the continuation.
    Return,
    /// A pure native List fold.
    ListFold,
    /// `force v`: the cut of the thunk against a force frame.
    Force,
    /// `fix x. M`: the cut of the recursive thunk against a force frame.
    Fixpoint,
    /// `λ. M`: the cut of the copattern object against the continuation.
    Lambda,
    /// `case v {…}`: the cut of the scrutinee against the match, or the cut
    /// naming the continuation the match's arms share.
    Case,
    /// `v.f`: the cut of a tuple or a record against the selection of one of
    /// its fields.
    Projection,
    /// `x ← M; N`: the cut naming the continuation a bind passes under its
    /// binder.
    Bind,
    /// A declaration's value, cut against `★`.
    TopValue,
    /// A memory form: a hold, an access or one of a view's eliminators.
    Memory,
}

/// The provenance table: the [`FocusOrigin`] of every command focusing
/// created, in creation order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Provenance
{
    /// Each created command with its origin, in increasing command address.
    origins: Vec<(CommandId, FocusOrigin)>,
}

impl Provenance
{
    /// An empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The origin recorded for a command, or `None` when focusing did not
    /// create it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(origin)` exactly when a translation recorded the
    ///   command.
    /// - provides: the per-command un-sugaring lookup.
    /// - fails: `None` for a command no translation created.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and sparse increasing command tables, exact
    ///   hits, an interior gap, the end and a truncated suffix distinguish
    ///   wrong-key searches, wrong origins and stale entries. The predicate
    ///   reads the one entry the increasing order places `command` at, found by
    ///   a lower-bound partition rather than the body's equality search.
    /// - witness: `focus::tests::provenance_lookup_distinguishes_unrecorded_commands`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.origins
        .get(self.origins.partition_point(|&(recorded, _)| recorded < command))
        .filter(|&&(recorded, _)| recorded == command).map(|&(_, origin)| origin)
    )]
    pub fn origin(
        &self,
        command: CommandId,
    ) -> Option<FocusOrigin>
    {
        self.origins
            .binary_search_by_key(&command, |&(recorded, _)| recorded)
            .ok()
            .and_then(|offset| self.origins.get(offset))
            .map(|&(_, origin)| origin)
    }

    /// Every recorded command with its origin, in creation order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn entries(&self) -> impl Iterator<Item = (CommandId, FocusOrigin)>
    {
        self.origins.iter().copied()
    }

    /// The number of recorded commands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> NodeCount
    {
        NodeCount::from(self.origins.len())
    }

    /// Record a command's origin.
    ///
    /// # Specification
    /// - requires: `command` is above every command already recorded, which
    ///   minting order guarantees.
    /// - ensures: the table answers `origin` for `command`.
    /// - provides: the one write of the table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two increasing records with different origins are
    ///   read independently; gap and truncation probes distinguish a skipped
    ///   append, wrong key or overwritten origin.
    /// - witness: `focus::tests::provenance_lookup_distinguishes_unrecorded_commands`
    #[spec(
        requires: self.origins.last().is_none_or(|&(previous, _)| previous < command),
        ensures: self.origin(command) == Some(origin),
    )]
    fn record(
        &mut self,
        command: CommandId,
        origin: FocusOrigin,
    )
    {
        self.origins.push((command, origin));
    }

    /// Truncate the table to an earlier length.
    ///
    /// # Specification
    /// trivial.
    fn truncate_to(
        &mut self,
        length: NodeCount,
    )
    {
        self.origins.truncate(usize::from(length));
    }
}

/// Why a translation was refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FocusRefusal
{
    /// Native universe transport has no command-IL destructor.
    UniverseTransport(ComputationId),
    /// Element transport has no command-IL destructor.
    ElementTransport(ComputationId),
    /// A path introduction — reflexivity, an extensionality or equivalence
    /// statement, a session equivalence — or a compound endpoint: the command
    /// IL carries no paths, so none has a producer to become. A flow is not
    /// refused: it runs as its translator.
    ElementPath(ValueId),
    /// A core value id names no node of the core arena.
    DanglingValue(ValueId),
    /// A core computation id names no node of the core arena.
    DanglingComputation(ComputationId),
    /// The command arena refused a node.
    Mint(MintRefusal),
    /// A code or universe-path certificate: the command IL carries no types, so
    /// a quoted type, a type operator or a static application has no
    /// producer to become.
    Code(ValueId),
    /// A hole or a mark in value position: an unfinished or ill-typed program
    /// has no command-IL image, as it has no kernel one.
    IncompleteValue(ValueId),
    /// A hole or a mark in computation position.
    IncompleteComputation(ComputationId),
    /// A session action: the command IL carries no channels, so a send, a
    /// receive, a choice, a close or a fork has no image in it.
    Session(ComputationId),
    /// A world form: the command IL runs at one world, so a hold, an open or
    /// a migration has no image in it.
    World(ComputationId),
    /// A computation standing where a value is read, before the checker's
    /// elaboration replaced it: only an elaborated body has a command-IL
    /// image, as only one has a kernel image.
    Unelaborated(ValueId),
    /// An internal invariant broke: a finishing task found no result where
    /// its own children should have left one. Unreachable while the
    /// translation's own pushes are the only source of tasks; reported rather
    /// than asserted.
    TranslationInvariant,
}

impl fmt::Display for FocusRefusal
{
    /// Names the refused input.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::UniverseTransport(_) => {
                f.write_str("universe transport has no command-IL destructor")
            },
            Self::ElementTransport(_) => {
                f.write_str("element transport has no command-IL destructor")
            },
            Self::ElementPath(_) => f.write_str(
                "an identity introduction or a compound endpoint has no command-IL producer",
            ),
            Self::DanglingValue(_) => f.write_str("a core value id names no node"),
            Self::DanglingComputation(_) => f.write_str("a core computation id names no node"),
            Self::Mint(refusal) => write!(f, "the command arena refused a node: {refusal}"),
            Self::TranslationInvariant => f.write_str("the translation lost a result it pushed"),
            Self::Code(_) => f.write_str("a code has no producer in the command IL"),
            Self::IncompleteValue(_) | Self::IncompleteComputation(_) => {
                f.write_str("a hole or a mark has no image in the command IL")
            },
            Self::Unelaborated(_) => f.write_str(
                "a computation standing as a value before elaboration has no command-IL producer",
            ),
            Self::Session(_) => f.write_str("a session action has no image in the command IL"),
            Self::World(_) => f.write_str("a world form has no image in the command IL"),
        }
    }
}

impl core::error::Error for FocusRefusal
{
}

impl From<MintRefusal> for FocusRefusal
{
    /// Carries the arena's refusal in its own vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MintRefusal) -> Self
    {
        Self::Mint(refusal)
    }
}

/// Focus a core computation against the terminal continuation `★`.
///
/// # Specification
/// - requires: `computation` is a closed term of `core`, or one whose free
///   variables the caller binds.
/// - ensures: on success the command `𝓕⟦computation⟧★`, every command it
///   created recorded in `provenance`; equal inputs mint identical nodes.
/// - provides: the entry of a computation into the IL.
/// - fails: [`FocusRefusal`] at the first dangling core id, code or refused
///   mint; `arena` and `provenance` are then exactly as they were on entry.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — an independent decoder compares generated closed
///   computations with their input, detecting wrong formers, child order and
///   binder shifts within the bounded generator. L3 — hand-built former cases
///   and exact refusal/rollback observations cover the directed residue;
///   equal-input arena comparison observes deterministic minting only.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
/// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
/// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
/// - witness: `focus::tests::a_refused_focusing_leaves_the_arena_at_its_mark`
/// - witness: `focus::tests::a_code_is_refused_by_name`
/// - witness: `focus::tests::focusing_mints_no_name`
/// - witness: `focus::tests::each_focus_entry_rolls_back_dangling_inputs`
#[inline]
#[spec(
    captures: [mark = arena.watermark(), recorded = provenance.len()],
    ensures: |ret| match ret {
        | Ok(id) => arena.command(id).is_some() && provenance.origin(id).is_some(),
        | Err(_) => arena.watermark() == mark && provenance.len() == recorded,
    },
)]
pub fn focus_computation(
    core: &CoreArena,
    computation: ComputationId,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
) -> Result<CommandId, FocusRefusal>
{
    transactional(arena, provenance, |arena, provenance| {
        with_combinators(
            core,
            arena,
            provenance,
            (
                |run: &mut Focusing<'_>| {
                    let top = run.arena.mint_consumer(ConsumerNode::Top)?;
                    run.tasks.push(Task::Computation {
                        computation,
                        continuation: top,
                    });
                    Ok(())
                },
                |run: Focusing<'_>| run.single_command(),
            ),
        )
    })
}

/// Focus a core value into a producer.
///
/// # Specification
/// - requires: as [`focus_computation`].
/// - ensures: on success the producer `𝓥⟦value⟧`, which is never a `μ`.
/// - provides: the entry of a value into the IL.
/// - fails: as [`focus_computation`], with the same rollback.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — the independent decoder compares generated values with
///   their source, exposing wrong constructors and child order within the
///   bounded generator. L3 — exact dangling-root rollback covers refusal.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
/// - witness: `focus::tests::each_focus_entry_rolls_back_dangling_inputs`
#[inline]
#[spec(
    captures: [mark = arena.watermark(), recorded = provenance.len()],
    ensures: |ret| match ret {
        | Ok(id) => arena.producer(id).is_some_and(|node| !matches!(node, &ProducerNode::Mu { .. })),
        | Err(_) => arena.watermark() == mark && provenance.len() == recorded,
    },
)]
pub fn focus_value(
    core: &CoreArena,
    value: ValueId,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
) -> Result<ProducerId, FocusRefusal>
{
    transactional(arena, provenance, |arena, provenance| {
        with_combinators(
            core,
            arena,
            provenance,
            (
                |run: &mut Focusing<'_>| {
                    run.tasks.push(Task::Value(value));
                    Ok(())
                },
                |run: Focusing<'_>| run.single_producer(),
            ),
        )
    })
}

/// Focus a declaration's value against `★`: the command `⟨𝓥⟦value⟧ |+ ★⟩`.
///
/// # Specification
/// - requires: as [`focus_computation`].
/// - ensures: on success the cut of `𝓥⟦value⟧` against `★`, recorded as
///   [`FocusOrigin::TopValue`].
/// - provides: the entry a declaration is run from.
/// - fails: as [`focus_computation`], with the same rollback.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a literal declaration focuses to one positive cut against
///   `★`, checked and recorded as a top value.
/// - witness: `tests::focus_properties::top_level_value_focuses_against_top`
/// - witness: `focus::tests::each_focus_entry_rolls_back_dangling_inputs`
#[inline]
#[spec(
    captures: [mark = arena.watermark(), recorded = provenance.len()],
    ensures: |ret| match ret {
        | Ok(id) => provenance.origin(id) == Some(FocusOrigin::TopValue)
            && arena.command(id).is_some_and(|node| matches!(node,
                &crate::il::CommandNode::Cut { polarity: Polarity::Positive, consumer, .. }
                    if arena.consumer(consumer) == Some(&ConsumerNode::Top))),
        | Err(_) => arena.watermark() == mark && provenance.len() == recorded,
    },
)]
pub fn focus_top_value(
    core: &CoreArena,
    value: ValueId,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
) -> Result<CommandId, FocusRefusal>
{
    transactional(arena, provenance, |arena, provenance| {
        with_combinators(
            core,
            arena,
            provenance,
            (
                |run: &mut Focusing<'_>| {
                    let top = run.arena.mint_consumer(ConsumerNode::Top)?;
                    run.tasks.push(Task::Cut {
                        origin: FocusOrigin::TopValue,
                        polarity: Polarity::Positive,
                        consumer: top,
                    });
                    run.tasks.push(Task::Value(value));
                    Ok(())
                },
                |run: Focusing<'_>| run.single_command(),
            ),
        )
    })
}

/// Run a translation, truncating the arena and the provenance table to their
/// entry marks if it is refused.
///
/// # Specification
/// - requires: `build` only appends nodes and origins; earlier entries are
///   neither removed nor rewritten.
/// - ensures: `build`'s answer; on refusal, `arena` and `provenance` are
///   exactly as on entry.
/// - provides: the one rollback every entry point shares.
/// - fails: `build`'s refusal, unchanged.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — partial builds and dangling roots through every entry
///   point observe exact refusal payloads and retained earlier translations. A
///   missing rollback or a rollback of one region only changes the
///   arena/provenance observations.
/// - witness: `focus::tests::a_refused_focusing_leaves_the_arena_at_its_mark`
/// - witness: `focus::tests::each_focus_entry_rolls_back_dangling_inputs`
#[spec(
    captures: [mark = arena.watermark(), recorded = provenance.len()],
    ensures: |ref ret| ret.is_ok() || (arena.watermark() == mark && provenance.len() == recorded),
)]
fn transactional<Answer, Build>(
    arena: &mut CommandArena,
    provenance: &mut Provenance,
    build: Build,
) -> Result<Answer, FocusRefusal>
where
    Build: FnOnce(&mut CommandArena, &mut Provenance) -> Result<Answer, FocusRefusal>,
{
    let arena_mark = arena.watermark();
    let provenance_mark = provenance.len();
    let answer = build(arena, provenance);
    if answer.is_err() {
        arena.truncate_to(arena_mark);
        provenance.truncate_to(provenance_mark);
    }
    answer
}

/// Focus the work `seed` sets up, every flow combinator it meets focused once
/// beforehand.
///
/// # Specification
/// - requires: `seed` only mints and pushes tasks; `finish` reads the run's one
///   result.
/// - ensures: a first run over `core` records the combinators its flows and
///   rides apply; when it met none its result is the answer. Otherwise the
///   arena and provenance return to their marks, each wanted combinator is
///   built closed in a scratch arena and focused by a run of its own, and a
///   second run with those producers prepared gives the answer.
/// - provides: closed combinators without a run nested in a run, and with no
///   cost to a term that holds no flow.
/// - fails: `seed`'s, a run's or `finish`'s refusal;
///   [`FocusRefusal::TranslationInvariant`] when the second run still wants a
///   combinator.
/// - panics: none.
/// - executable: none — the answer's type is the caller's, and what the runs
///   minted is observed by the entry points' own specifications.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — rides and a function flow run to the kernel rows' values,
///   which the first run's placeholders would not compute.
/// - witness: `tests::run::rides_run_by_the_motives_action`
/// - witness: `tests::run::a_function_flow_runs_in_variance_order`
fn with_combinators<Answer, Seed, Finish>(
    core: &CoreArena,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
    (seed, finish): (Seed, Finish),
) -> Result<Answer, FocusRefusal>
where
    Seed: Fn(&mut Focusing<'_>) -> Result<(), FocusRefusal>,
    Finish: Fn(Focusing<'_>) -> Result<Answer, FocusRefusal>,
{
    let arena_mark = arena.watermark();
    let provenance_mark = provenance.len();
    let wanted = {
        let mut run = Focusing::new(core, arena, provenance);
        seed(&mut run)?;
        run.drive()?;
        if run.wanted.is_empty() {
            return finish(run);
        }
        core::mem::take(&mut run.wanted)
    };
    arena.truncate_to(arena_mark);
    provenance.truncate_to(provenance_mark);
    let mut prepared = BTreeMap::new();
    for combinator in wanted {
        let mut scratch = CoreArena::new();
        let root = crate::flow::build(core, combinator, &mut scratch)?;
        let mut closed = Focusing::new(&scratch, arena, provenance);
        closed.tasks.push(Task::Value(root));
        closed.drive()?;
        if !closed.wanted.is_empty() {
            return Err(FocusRefusal::TranslationInvariant);
        }
        let _replaced = prepared.insert(combinator, closed.single_producer()?);
    }
    let mut run = Focusing::new(core, arena, provenance);
    run.prepared = prepared;
    seed(&mut run)?;
    run.drive()?;
    if !run.wanted.is_empty() {
        return Err(FocusRefusal::TranslationInvariant);
    }
    finish(run)
}

/// One unit of pending translation work.
#[derive(Clone, Debug)]
enum Task
{
    /// Assemble a literal stack after translating its operands and bind bodies.
    Reify(ValueId),
    /// Assemble an effect or control instruction after its children.
    Control
    {
        /// The source node carrying interface and clause metadata.
        source: ComputationId,
        /// The caller's return point.
        continuation: ConsumerId,
    },
    /// Assemble a native fold after its list and two branches.
    ListFold
    {
        /// Portable element annotation.
        element: gandr_core_term::ValueTypeId,
        /// Portable result annotation.
        result: gandr_core_term::ValueTypeId,
        /// The caller's return point.
        continuation: ConsumerId,
    },
    /// Complete a saturated native operation after translating its operands.
    Primitive
    {
        /// The table's operation.
        primitive: gandr_core_term::primitive::Primitive,
        /// The source operand shape.
        arguments: gandr_core_term::primitive::Arguments,
        /// The caller's return point.
        continuation: ConsumerId,
    },
    /// Translate a value; leaves one producer.
    Value(ValueId),
    /// Translate a computation under a continuation; leaves one command.
    Computation
    {
        /// The computation.
        computation: ComputationId,
        /// The continuation it returns to.
        continuation: ConsumerId,
    },
    /// Pop this many producers and mint their tuple.
    Tuple(ProducerArity),
    /// Pop one producer per label and mint the record of those labels.
    Record(alloc::sync::Arc<[gandr_core_term::FieldLabel]>),
    /// Pop one producer per payload move and mint the recorded run of these
    /// moves.
    Recorded(alloc::sync::Arc<[gandr_core_term::session::RecordedMove<()>]>),
    /// Pop head and tail producers and mint their native cell.
    ListCons,
    /// Pop one producer and mint its injection into this summand.
    Injection(Summand),
    /// Pop one producer and mint its lift.
    Lift(Level),
    /// Pop a datatype constructor's fields and mint it.
    Native
    {
        /// The constructor's ordinal.
        tag: gandr_kernel_term::ConstructorTag,
        /// Its field count.
        arity: ProducerArity,
        /// The declaration of its family, when the core's classifier names
        /// one.
        family: Option<gandr_kernel_term::ConstantIndex>,
    },
    /// Pop one command and mint the thunk suspending it.
    Thunk,
    /// Pop one command and mint the recursive thunk suspending it.
    Fixpoint(gandr_kernel_term::FixpointEvidence),
    /// Pop one producer and mint its cut against `consumer`.
    Cut
    {
        /// The construct the cut is created for.
        origin: FocusOrigin,
        /// The cut's polarity.
        polarity: Polarity,
        /// The consumer.
        consumer: ConsumerId,
    },
    /// Pop the argument's producer, mint `apply(argument; continuation)`, and
    /// translate `head` under it.
    Apply
    {
        /// The applied computation.
        head: ComputationId,
        /// The continuation the application returns to.
        continuation: ConsumerId,
    },
    /// Pop the body's command and mint `⟨cocase {apply ⇒ body} |− c⟩`.
    Lambda
    {
        /// The continuation the function is sent to.
        continuation: ConsumerId,
    },
    /// Pop the bind's body, mint `μ̃x. body`, and translate `head` under it.
    Bind
    {
        /// The bound computation.
        head: ComputationId,
    },
    /// Pop the scrutinee's producer and the arms' commands, one per summand,
    /// and mint the cut of the scrutinee against the match.
    Case
    {
        /// The number of arms.
        branches: NodeCount,
    },
    /// Pop the scrutinee's producer and the body's command, and mint the cut
    /// of the scrutinee against the match of one tuple pattern of this arity.
    Split(ProducerArity),
    /// Pop the branches' thunks and the scrutinee's producer, and mint the
    /// cut of the scrutinee against the nominal match.
    DataCase
    {
        /// The number of branches.
        branches: NodeCount,
        /// The continuation every branch returns to.
        continuation: ConsumerId,
    },
    /// Pop one command and mint `⟨μα. command |polarity continuation⟩`.
    Name
    {
        /// The construct the naming cut is created for.
        origin: FocusOrigin,
        /// The polarity of what the continuation observes.
        polarity: Polarity,
        /// The named continuation.
        continuation: ConsumerId,
    },
    /// Pop the second, then the first producer, and mint `⟨combinator |+
    /// force(apply(first; apply(second; continuation)))⟩` over the closed
    /// combinator's producer.
    Combinator
    {
        /// The closed program applied.
        combinator: crate::flow::Combinator,
        /// The continuation its answer is sent to.
        continuation: ConsumerId,
    },
}

/// The state of one translation.
struct Focusing<'run>
{
    /// The core arena read from.
    core: &'run CoreArena,
    /// The command arena minted into.
    arena: &'run mut CommandArena,
    /// The provenance table recorded into.
    provenance: &'run mut Provenance,
    /// The pending work, the next task last.
    tasks: Vec<Task>,
    /// Translated producers awaiting their parent.
    producers: Vec<ProducerId>,
    /// Translated commands awaiting their parent.
    commands: Vec<CommandId>,
    /// The flow combinators focused before this run, by combinator.
    prepared: BTreeMap<crate::flow::Combinator, ProducerId>,
    /// The flow combinators this run met that were not prepared.
    wanted: BTreeSet<crate::flow::Combinator>,
}

impl<'run> Focusing<'run>
{
    /// A translation with no work.
    ///
    /// # Specification
    /// trivial.
    fn new(
        core: &'run CoreArena,
        arena: &'run mut CommandArena,
        provenance: &'run mut Provenance,
    ) -> Self
    {
        Self {
            core,
            arena,
            provenance,
            tasks: Vec::new(),
            producers: Vec::new(),
            commands: Vec::new(),
            prepared: BTreeMap::new(),
            wanted: BTreeSet::new(),
        }
    }

    /// Run every pending task.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the task stack is empty and each translated root
    ///   left its one result.
    /// - provides: the loop every translation drives; no task recurses.
    /// - fails: the first refusal a task raises.
    /// - panics: none.
    /// - intension: one iteration per task; a value or computation node is
    ///   translated by a constant number of tasks.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent decoding of bounded generated terms
    ///   observes former choice, child order and binder shifts. L3 — one case
    ///   per former and exact refusal/rollback probes cover directed
    ///   boundaries.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    #[spec(ensures: |ret| ret.is_err() || self.tasks.is_empty())]
    fn drive(&mut self) -> Result<(), FocusRefusal>
    {
        while let Some(task) = self.tasks.pop() {
            self.step(task)?;
        }
        Ok(())
    }

    /// Run one task.
    ///
    /// # Specification
    /// - requires: a finishing task's children have left their results.
    /// - ensures: the task's result, or its follow-up tasks, are pushed.
    /// - provides: the translation table of the module documentation, one arm
    ///   per row.
    /// - fails: a dangling core id, a refused mint, or a missing result.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent decoding of bounded generated terms
    ///   observes former choice, child order and binder shifts. L3 — one case
    ///   per former and exact refusal/rollback probes cover directed
    ///   boundaries.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    #[spec(
        requires: match &task {
            | &Task::Reify(source) => self.core.value(source).is_none_or(|node| match *node {
                Value::Reify(ref frames) => self.producers.len() >= frames.iter().filter(|frame| matches!(frame, gandr_core_term::control::StackFrame::Apply(_))).count()
                    && self.commands.len() >= frames.iter().filter(|frame| matches!(frame, gandr_core_term::control::StackFrame::Bind(_))).count(),
                Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Tuple(_) | Value::Injection(..) | Value::ListNil | Value::ListCons(..) | Value::Thunk(_) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..) | Value::Constructor { .. } | Value::Record(_) | Value::Hole(_) | Value::Mark { .. } => true,
            }),
            | &Task::Control { source, .. } => self.core.computation(source).is_none_or(|node| match *node {
                Computation::Perform { .. } => !self.producers.is_empty(),
                Computation::Exercise { .. } => self.producers.len() >= 2,
                Computation::Handle { ref clauses, .. } | Computation::Scope { ref clauses, .. } => self.commands.len() >= clauses.len().saturating_add(2),
                Computation::Resume(..) => !self.producers.is_empty() && !self.commands.is_empty(),
                Computation::Reset(_) | Computation::Shift(_) => !self.commands.is_empty(),
                Computation::With(..) => self.commands.len() >= 2,
                Computation::Primitive { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Application(..) | Computation::Return(_) | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::Force(_) | Computation::Case { .. } | Computation::Split { .. } | Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Hole(_) | Computation::Mark { .. } | Computation::ListFold { .. } | Computation::Project(..) | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => true,
            }),
            | &Task::Primitive { arguments, .. } => self.producers.len() >= arguments.len(),
            | &Task::ListCons | &Task::Combinator { .. } => self.producers.len() >= 2,
            | &Task::Injection(_) | &Task::Lift(_) | &Task::Cut { .. } | &Task::Apply { .. } => !self.producers.is_empty(),
            | &Task::Thunk | &Task::Fixpoint(_) | &Task::Lambda { .. } | &Task::Bind { .. } | &Task::Name { .. } => !self.commands.is_empty(),
            | &Task::ListFold { .. } => !self.producers.is_empty() && self.commands.len() >= 2,
            | &Task::Case { branches } => !self.producers.is_empty() && self.commands.len() >= usize::from(branches),
            | &Task::Split(_) => !self.producers.is_empty() && !self.commands.is_empty(),
            | &Task::Tuple(arity) | &Task::Native { arity, .. } => self.producers.len() >= usize::from(arity),
            | &Task::Record(ref labels) => self.producers.len() >= labels.len(),
            | &Task::Recorded(ref moves) => self.producers.len() >= usize::from(ConstructorTag::Recorded(alloc::sync::Arc::clone(moves)).producer_arity()),
            | &Task::DataCase { branches, .. } => self.producers.len() > usize::from(branches),
            | &Task::Value(_) | &Task::Computation { .. } => true,
        },
        ensures: |ret| ret.is_err() || (self.producers.last().is_none_or(|id| self.arena.producer(*id).is_some())
            && self.commands.last().is_none_or(|id| self.arena.command(*id).is_some())),
    )]
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), FocusRefusal>
    {
        match task {
            Task::Reify(source) => self.complete_reify(source),
            Task::Control {
                source,
                continuation,
            } => self.complete_control(source, continuation),
            Task::Primitive {
                primitive,
                arguments,
                continuation,
            } => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    Arguments::Unary(_) => Arguments::Unary(self.pop_producer()?),
                    Arguments::Binary(_) => {
                        let second = self.pop_producer()?;
                        Arguments::Binary([self.pop_producer()?, second])
                    },
                };
                let producer = self.arena.mint_producer(ProducerNode::Primitive {
                    primitive,
                    arguments,
                })?;
                self.cut(
                    FocusOrigin::Return,
                    Polarity::Positive,
                    producer,
                    continuation,
                )
            },
            Task::Value(value) => self.value(value),
            Task::Computation {
                computation,
                continuation,
            } => self.computation(computation, continuation),
            Task::Tuple(arity) => {
                let start = self
                    .producers
                    .len()
                    .checked_sub(usize::from(arity))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let components: alloc::vec::Vec<ProducerId> =
                    self.producers.drain(start ..).collect();
                self.constructor(ConstructorTag::Tuple(arity), &components)
            },
            Task::Record(labels) => {
                let start = self
                    .producers
                    .len()
                    .checked_sub(labels.len())
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let fields: Vec<ProducerId> = self.producers.drain(start ..).collect();
                self.constructor(ConstructorTag::Record(labels), &fields)
            },
            Task::Recorded(moves) => {
                let tag = ConstructorTag::Recorded(moves);
                let start = self
                    .producers
                    .len()
                    .checked_sub(usize::from(tag.producer_arity()))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let payloads: Vec<ProducerId> = self.producers.drain(start ..).collect();
                self.constructor(tag, &payloads)
            },
            Task::ListCons => {
                let tail = self.pop_producer()?;
                let head = self.pop_producer()?;
                self.constructor(ConstructorTag::ListCons, &[head, tail])
            },
            Task::Injection(summand) => {
                let body = self.pop_producer()?;
                self.constructor(ConstructorTag::Injection(summand), &[body])
            },
            Task::Lift(level) => {
                let body = self.pop_producer()?;
                self.constructor(ConstructorTag::Lift(level), &[body])
            },
            Task::Native { tag, arity, family } => {
                let start = self
                    .producers
                    .len()
                    .checked_sub(usize::from(arity))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let fields: Vec<ProducerId> = self.producers.drain(start ..).collect();
                self.constructor(ConstructorTag::Data { tag, arity, family }, &fields)
            },
            Task::Thunk => {
                let body = self.pop_command()?;
                let thunk = self.arena.mint_producer(ProducerNode::Thunk { body })?;
                self.producers.push(thunk);
                Ok(())
            },
            Task::Fixpoint(evidence) => {
                let body = self.pop_command()?;
                let thunk = self
                    .arena
                    .mint_producer(ProducerNode::Fixpoint { body, evidence })?;
                self.producers.push(thunk);
                Ok(())
            },
            Task::Cut {
                origin,
                polarity,
                consumer,
            } => {
                let producer = self.pop_producer()?;
                self.cut(origin, polarity, producer, consumer)
            },
            Task::ListFold {
                element,
                result,
                continuation,
            } => {
                let list = self.pop_producer()?;
                let on_cons = self.pop_command()?;
                let on_nil = self.pop_command()?;
                let consumer = self.arena.mint_consumer(ConsumerNode::ListFold {
                    element,
                    result,
                    on_nil,
                    on_cons,
                    continuation,
                })?;
                self.cut(FocusOrigin::ListFold, Polarity::Positive, list, consumer)
            },
            Task::Apply { head, continuation } => {
                let argument = self.pop_producer()?;
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    producers: alloc::boxed::Box::from([argument]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                self.tasks.push(Task::Computation {
                    computation: head,
                    continuation: frame,
                });
                Ok(())
            },
            Task::Combinator {
                combinator,
                continuation,
            } => {
                let second = self.pop_producer()?;
                let first = self.pop_producer()?;
                let inner = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    producers: alloc::boxed::Box::from([second]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                let outer = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    producers: alloc::boxed::Box::from([first]),
                    consumers: alloc::boxed::Box::from([inner]),
                })?;
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    producers: alloc::boxed::Box::from([]),
                    consumers: alloc::boxed::Box::from([outer]),
                })?;
                let closed = self.combinator(combinator)?;
                self.cut(FocusOrigin::Force, Polarity::Positive, closed, frame)
            },
            Task::Lambda { continuation } => {
                let body = self.pop_command()?;
                let object = self.arena.mint_producer(ProducerNode::Cocase {
                    arms: alloc::boxed::Box::from([CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    }]),
                })?;
                self.cut(
                    FocusOrigin::Lambda,
                    Polarity::Negative,
                    object,
                    continuation,
                )
            },
            Task::Bind { head } => {
                let body = self.pop_command()?;
                let binder = self.arena.mint_consumer(ConsumerNode::MuTilde { body })?;
                self.tasks.push(Task::Computation {
                    computation: head,
                    continuation: binder,
                });
                Ok(())
            },
            Task::Case { branches } => {
                let scrutinee = self.pop_producer()?;
                let start = self
                    .commands
                    .len()
                    .checked_sub(usize::from(branches))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let arms = self
                    .commands
                    .drain(start ..)
                    .enumerate()
                    .map(|(summand, body)| PatternArm {
                        constructor: ConstructorTag::Injection(Summand::from(summand)),
                        body,
                    })
                    .collect();
                let matcher = self.arena.mint_consumer(ConsumerNode::Case { arms })?;
                self.cut(FocusOrigin::Case, Polarity::Positive, scrutinee, matcher)
            },
            Task::Split(arity) => {
                let body = self.pop_command()?;
                let scrutinee = self.pop_producer()?;
                let arms = alloc::boxed::Box::from([PatternArm {
                    constructor: ConstructorTag::Tuple(arity),
                    body,
                }]);
                let matcher = self.arena.mint_consumer(ConsumerNode::Case { arms })?;
                self.cut(FocusOrigin::Case, Polarity::Positive, scrutinee, matcher)
            },
            Task::DataCase {
                branches,
                continuation,
            } => {
                let scrutinee = self.pop_producer()?;
                let start = self
                    .producers
                    .len()
                    .checked_sub(usize::from(branches))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let thunks: alloc::boxed::Box<[ProducerId]> =
                    self.producers.drain(start ..).collect();
                let matcher = self.arena.mint_consumer(ConsumerNode::DataCase {
                    branches: thunks,
                    then: continuation,
                })?;
                self.cut(FocusOrigin::Case, Polarity::Positive, scrutinee, matcher)
            },
            Task::Name {
                origin,
                polarity,
                continuation,
            } => {
                let body = self.pop_command()?;
                let capture = self.arena.mint_producer(ProducerNode::Mu { body })?;
                self.cut(origin, polarity, capture, continuation)
            },
        }
    }

    /// Assemble a flat literal stack; each bind body owns its own return
    /// binder.
    ///
    /// # Specification
    /// - ensures: frame order and names are preserved, with no later frame
    ///   entering an earlier bind frame's value scope.
    /// - fails: missing child results, malformed source, or refused allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed apply, bind and projection frames distinguish
    ///   order and accidental scope nesting.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(ensures: |ret| ret.is_err() || self.producers.last().is_some_and(|id|
        matches!((self.core.value(source), self.arena.producer(*id)), (Some(Value::Reify(source)), Some(ProducerNode::Reify(frames))) if source.len() == frames.len())))]
    fn complete_reify(
        &mut self,
        source: ValueId,
    ) -> Result<(), FocusRefusal>
    {
        let core = self.core;
        let node = core
            .value(source)
            .ok_or(FocusRefusal::TranslationInvariant)?;
        let Value::Reify(ref source) = *node
        else {
            return Err(FocusRefusal::TranslationInvariant);
        };
        let mut frames = Vec::with_capacity(source.len());
        for frame in source.iter().rev() {
            frames.push(match *frame {
                gandr_core_term::control::StackFrame::Apply(_) => {
                    gandr_core_term::control::StackFrame::Apply(self.pop_producer()?)
                },
                gandr_core_term::control::StackFrame::Bind(_) => {
                    gandr_core_term::control::StackFrame::Bind(self.pop_command()?)
                },
                gandr_core_term::control::StackFrame::Project(side) => {
                    gandr_core_term::control::StackFrame::Project(side)
                },
            });
        }
        frames.reverse();
        let producer = self
            .arena
            .mint_producer(ProducerNode::Reify(frames.into()))?;
        self.producers.push(producer);
        Ok(())
    }

    /// Relocate an inline interface into the focused arena's annotation graph.
    ///
    /// # Specification
    /// - ensures: operation names survive and every type edge belongs to the
    ///   focused annotation arena, even when source handles contain free codes.
    /// - fails: a dangling source annotation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — displaced target arenas and dependent payload types
    ///   expose copied foreign handles and omitted signature edges.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|found|
        found.name() == signature.name() && found.types().all(|id| self.arena.annotations().value_type(id).is_some())))]
    fn signature(
        &mut self,
        signature: &gandr_core_term::effect::EffectSig,
    ) -> Result<gandr_core_term::effect::EffectSig, FocusRefusal>
    {
        let mut annotations =
            gandr_core_term::TypeImporter::new(self.core, self.arena.annotations_mut());
        Ok(
            signature.try_map_types(gandr_core_term::effect::TypeOrder::Forward, |id| {
                annotations
                    .value_type(id)
                    .map_err(|gandr_core_term::ImportFault| MintRefusal::DanglingAnnotation(id))
            })?,
        )
    }

    /// Assemble control children and record the instruction's source origin.
    ///
    /// # Specification
    /// - ensures: bodies retain their fresh return binder; operation clauses
    ///   retain source order and bind payload then resumption.
    /// - fails: missing child results, malformed source or refused allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent unfocusing distinguishes missing
    ///   children, swapped clauses, lost annotations and the two lazy
    ///   projections.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(ensures: |ret| ret.is_err()
        || self.commands.last().is_some_and(|id| self.arena.command(*id).is_some() && self.provenance.origin(*id).is_some()))]
    fn complete_control(
        &mut self,
        source: ComputationId,
        continuation: ConsumerId,
    ) -> Result<(), FocusRefusal>
    {
        let core = self.core;
        let node = core
            .computation(source)
            .ok_or(FocusRefusal::DanglingComputation(source))?;
        let (node, origin) = match *node {
            Computation::Perform {
                ref signature,
                ref operation,
                ..
            } => {
                let signature = self.signature(signature)?;
                let payload = self.pop_producer()?;
                (
                    crate::il::CommandNode::Perform {
                        signature,
                        operation: operation.clone(),
                        route: Route::Nearest,
                        payload,
                        continuation,
                    },
                    FocusOrigin::Perform,
                )
            },
            Computation::Exercise {
                ref signature,
                ref operation,
                ..
            } => {
                let signature = self.signature(signature)?;
                let payload = self.pop_producer()?;
                let capability = self.pop_producer()?;
                (
                    crate::il::CommandNode::Perform {
                        signature,
                        operation: operation.clone(),
                        route: Route::Capability(capability),
                        payload,
                        continuation,
                    },
                    FocusOrigin::Exercise,
                )
            },
            Computation::Handle {
                ref signature,
                ref clauses,
                ..
            }
            | Computation::Scope {
                ref signature,
                ref clauses,
                ..
            } => {
                let (introduces, origin) = match *node {
                    Computation::Scope { .. } => (Introduces::Capability, FocusOrigin::Scope),
                    Computation::Primitive { .. }
                    | Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::Ride { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Lambda(_)
                    | Computation::Fixpoint { .. }
                    | Computation::Application(..)
                    | Computation::Return(_)
                    | Computation::Bind(..)
                    | Computation::Ascribe { .. }
                    | Computation::Force(_)
                    | Computation::Case { .. }
                    | Computation::Split { .. }
                    | Computation::DataCase { .. }
                    | Computation::RecordProjection(..)
                    | Computation::TupleProjection(..)
                    | Computation::Hole(_)
                    | Computation::Mark { .. }
                    | Computation::ListFold { .. }
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Exercise { .. }
                    | Computation::Resume(..)
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..)
                    | Computation::Session(_)
                    | Computation::Memory(_)
                    | Computation::World(_) => (Introduces::Nothing, FocusOrigin::Handle),
                };
                let signature = self.signature(signature)?;
                let mut translated = Vec::with_capacity(clauses.len());
                for clause in clauses.iter().rev() {
                    translated.push(gandr_core_term::control::EffectClause {
                        operation: clause.operation.clone(),
                        body: self.pop_command()?,
                    });
                }
                translated.reverse();
                let on_return = self.pop_command()?;
                let subject = self.pop_command()?;
                (
                    crate::il::CommandNode::Handle {
                        signature,
                        introduces,
                        subject,
                        on_return,
                        clauses: translated.into(),
                        continuation,
                    },
                    origin,
                )
            },
            Computation::Resume(..) => {
                let body = self.pop_command()?;
                let stack = self.pop_producer()?;
                (
                    crate::il::CommandNode::Resume {
                        stack,
                        body,
                        continuation,
                    },
                    FocusOrigin::Resume,
                )
            },
            Computation::Reset(_) => (
                crate::il::CommandNode::Reset {
                    body: self.pop_command()?,
                    continuation,
                },
                FocusOrigin::Reset,
            ),
            Computation::Shift(_) => (
                crate::il::CommandNode::Shift {
                    body: self.pop_command()?,
                    continuation,
                },
                FocusOrigin::Shift,
            ),
            Computation::Memory(ref form) => (
                crate::il::CommandNode::Memory {
                    form: form.try_map(
                        gandr_core_term::session::ChildOrder::Reverse,
                        self,
                        |focus, _| focus.pop_producer(),
                        |focus, _| focus.pop_command(),
                    )?,
                    continuation,
                },
                FocusOrigin::Memory,
            ),
            Computation::With(..) => {
                let right = self.pop_command()?;
                let left = self.pop_command()?;
                let producer = self.arena.mint_producer(ProducerNode::Cocase {
                    arms: alloc::boxed::Box::from([
                        CopatternArm {
                            destructor: DestructorTag::Project(Side::Left),
                            body: left,
                        },
                        CopatternArm {
                            destructor: DestructorTag::Project(Side::Right),
                            body: right,
                        },
                    ]),
                })?;
                return self.cut(
                    FocusOrigin::With,
                    Polarity::Negative,
                    producer,
                    continuation,
                );
            },
            Computation::Primitive { .. }
            | Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Lambda(_)
            | Computation::Fixpoint { .. }
            | Computation::Application(..)
            | Computation::Return(_)
            | Computation::Bind(..)
            | Computation::Ascribe { .. }
            | Computation::Force(_)
            | Computation::Case { .. }
            | Computation::Split { .. }
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..)
            | Computation::Hole(_)
            | Computation::Mark { .. }
            | Computation::ListFold { .. }
            | Computation::Project(..)
            | Computation::Session(_)
            | Computation::World(_) => return Err(FocusRefusal::TranslationInvariant),
        };
        let command = self.arena.mint_command(node)?;
        self.provenance.record(command, origin);
        self.commands.push(command);
        Ok(())
    }

    /// Translate one value node, or schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a leaf's producer is pushed; a composite's finishing task and
    ///   its children's tasks are scheduled, children left to right.
    /// - provides: the `𝓥` rows.
    /// - fails: [`FocusRefusal::DanglingValue`], [`FocusRefusal::Code`] for a
    ///   quote of either sort, a static lambda or a static application,
    ///   [`FocusRefusal::IncompleteValue`] for a hole or a mark,
    ///   [`FocusRefusal::Unelaborated`] for an unelaborated computation in
    ///   value position, or a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent decoding of bounded generated terms
    ///   observes former choice, child order and binder shifts. L3 — one case
    ///   per former and exact refusal/rollback probes cover directed
    ///   boundaries.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    /// - witness: `focus::tests::a_record_focuses_to_its_labels_in_canonical_order`
    /// - witness: `focus::tests::a_code_is_refused_by_name`
    /// - witness: `focus::tests::each_focus_entry_rolls_back_dangling_inputs`
    /// - witness: `focus::tests::a_hole_or_a_mark_is_refused_by_name`
    #[spec(
        captures: [work = self.tasks.len(), results = self.producers.len()],
        ensures: |ret| match self.core.value(id) {
            | None => ret == Err(FocusRefusal::DanglingValue(id)),
            | Some(&Value::Quote(_) | &Value::QuoteComputation(_)) => ret == Err(FocusRefusal::Code(id)),
            | Some(&Value::Hole(_) | &Value::Mark { .. }) => ret == Err(FocusRefusal::IncompleteValue(id)),
            | Some(&Value::Nested(_) | &Value::Run(_)) => ret == Err(FocusRefusal::Unelaborated(id)),
            | Some(_) => ret.is_err() || self.tasks.len() > work || self.producers.len() > results,
        },
    )]
    fn value(
        &mut self,
        id: ValueId,
    ) -> Result<(), FocusRefusal>
    {
        let node = self.core.value(id).ok_or(FocusRefusal::DanglingValue(id))?;
        let leaf = match *node {
            Value::Record(ref fields) => {
                self.tasks
                    .push(Task::Record(fields.keys().cloned().collect()));
                for &field in fields.values().rev() {
                    self.tasks.push(Task::Value(field));
                }
                return Ok(());
            },
            Value::Constructor {
                datatype,
                tag,
                ref fields,
            } => {
                self.tasks.push(Task::Native {
                    tag,
                    arity: ProducerArity::from(fields.len()),
                    family: match self.core.value_type(datatype) {
                        Some(&gandr_core_term::ValueType::Data { declaration, .. }) => {
                            Some(declaration)
                        },
                        Some(_) | None => None,
                    },
                });
                for &field in fields.iter().rev() {
                    self.tasks.push(Task::Value(field));
                }
                return Ok(());
            },
            Value::Reify(ref frames) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Reify(id));
                for frame in frames.iter().rev() {
                    match *frame {
                        gandr_core_term::control::StackFrame::Apply(value) => {
                            self.tasks.push(Task::Value(value));
                        },
                        gandr_core_term::control::StackFrame::Bind(body) => {
                            self.tasks.push(Task::Computation {
                                computation: body,
                                continuation: return_point,
                            });
                        },
                        gandr_core_term::control::StackFrame::Project(_) => {},
                    }
                }
                return Ok(());
            },
            Value::ListNil => ProducerNode::Constructor {
                tag: ConstructorTag::ListNil,
                producers: alloc::boxed::Box::from([]),
                consumers: alloc::boxed::Box::from([]),
            },
            Value::ListCons(head, tail) => {
                self.tasks.push(Task::ListCons);
                self.tasks.push(Task::Value(tail));
                self.tasks.push(Task::Value(head));
                return Ok(());
            },
            Value::Variable { zone, index } => ProducerNode::Variable { zone, index },
            Value::Constant(constant) => ProducerNode::Constant(constant),
            Value::Literal(ref literal) => ProducerNode::Literal(literal.clone()),
            Value::Tuple(ref components) if components.is_empty() => ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                producers: alloc::boxed::Box::from([]),
                consumers: alloc::boxed::Box::from([]),
            },
            Value::Tuple(ref components) => {
                self.tasks
                    .push(Task::Tuple(ProducerArity::from(components.len())));
                for &component in components.iter().rev() {
                    self.tasks.push(Task::Value(component));
                }
                return Ok(());
            },
            Value::Recorded(ref moves) => {
                self.tasks.push(Task::Recorded(
                    moves.iter().map(|movement| movement.carrying(())).collect(),
                ));
                for movement in moves.iter().rev() {
                    if let gandr_core_term::session::RecordedMove::Sent(payload)
                    | gandr_core_term::session::RecordedMove::Received(payload) = *movement
                    {
                        self.tasks.push(Task::Value(payload));
                    }
                }
                return Ok(());
            },
            Value::Injection(summand, body) => {
                self.tasks.push(Task::Injection(summand));
                self.tasks.push(Task::Value(body));
                return Ok(());
            },
            Value::Lift { ref target, body } => {
                self.tasks.push(Task::Lift(target.clone()));
                self.tasks.push(Task::Value(body));
                return Ok(());
            },
            Value::Thunk(body) | Value::Primitive { body, .. } => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Thunk);
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
                return Ok(());
            },
            Value::PathRefl(_)
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticLambda(_)
            | Value::StaticApplication(..) => return Err(FocusRefusal::Code(id)),
            // A flow runs as its translator.
            Value::Forward(translator) => {
                self.tasks.push(Task::Value(translator));
                return Ok(());
            },
            Value::Stay(_)
            | Value::SessionRelated {
                relation: gandr_core_term::session::SessionRelation::Subtyping,
                ..
            } => {
                let identity = self.combinator(crate::flow::Combinator::Identity)?;
                self.producers.push(identity);
                return Ok(());
            },
            Value::Then(first, second)
            | Value::FunctionFlow(first, second)
            | Value::FlowProduct(first, second) => {
                let combinator = match *node {
                    Value::Then(..) => crate::flow::Combinator::Compose,
                    Value::FlowProduct(..) => crate::flow::Combinator::Pair,
                    Value::Primitive { .. }
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Ua { .. }
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_)
                    | Value::Returned(_)
                    | Value::Nested(_)
                    | Value::Run(_)
                    | Value::Variable { .. }
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::Tuple(_)
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Thunk(_)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)
                    | Value::Constructor { .. }
                    | Value::Record(_)
                    | Value::Hole(_)
                    | Value::Mark { .. }
                    | Value::Reify(_) => crate::flow::Combinator::Wrap,
                };
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Thunk);
                self.tasks.push(Task::Combinator {
                    combinator,
                    continuation: return_point,
                });
                self.tasks.push(Task::Value(second));
                self.tasks.push(Task::Value(first));
                return Ok(());
            },
            Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Ua { .. }
            | Value::SessionRelated { .. }
            | Value::Returned(_) => {
                return Err(FocusRefusal::ElementPath(id));
            },
            Value::Hole(_) | Value::Mark { .. } => {
                return Err(FocusRefusal::IncompleteValue(id));
            },
            Value::Nested(_) | Value::Run(_) => return Err(FocusRefusal::Unelaborated(id)),
        };
        let producer = self.arena.mint_producer(leaf)?;
        self.producers.push(producer);
        Ok(())
    }

    /// Translate one computation node under a continuation, or schedule its
    /// children.
    ///
    /// # Specification
    /// - requires: `continuation` was minted for the binder depth `id` stands
    ///   at.
    /// - ensures: the `𝓕` row for the node's former is scheduled or minted; a
    ///   continuation that is not a tail is placed under no binder.
    /// - provides: the `𝓕` rows.
    /// - fails: [`FocusRefusal::DanglingComputation`],
    ///   [`FocusRefusal::IncompleteComputation`] for a hole or a mark,
    ///   [`FocusRefusal::Session`] for a session action,
    ///   [`FocusRefusal::UniverseTransport`] for a universe transport,
    ///   [`FocusRefusal::ElementTransport`] for an element transport, or a
    ///   refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent decoding of bounded generated terms
    ///   observes former choice, child order and binder shifts. L3 — one case
    ///   per former and exact refusal/rollback probes cover directed
    ///   boundaries.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    /// - witness: `focus::tests::a_projection_selects_by_position_or_label`
    /// - witness: `focus::tests::each_focus_entry_rolls_back_dangling_inputs`
    /// - witness: `focus::tests::a_hole_or_a_mark_is_refused_by_name`
    /// - witness: `focus::tests::a_session_action_is_refused_by_name`
    #[spec(
        captures: [work = self.tasks.len()],
        ensures: |ret| match self.core.computation(id) {
            | None => ret == Err(FocusRefusal::DanglingComputation(id)),
            | Some(&Computation::Hole(_) | &Computation::Mark { .. }) => ret == Err(FocusRefusal::IncompleteComputation(id)),
            | Some(&Computation::Session(_)) => ret == Err(FocusRefusal::Session(id)),
            | Some(&Computation::World(_)) => ret == Err(FocusRefusal::World(id)),
            | Some(_) => ret.is_err() || self.tasks.len() > work,
        },
    )]
    fn computation(
        &mut self,
        id: ComputationId,
        continuation: ConsumerId,
    ) -> Result<(), FocusRefusal>
    {
        let node = self
            .core
            .computation(id)
            .ok_or(FocusRefusal::DanglingComputation(id))?;
        match *node {
            Computation::RecordProjection(record, ref label) => {
                self.select(record, Selector::Label(label.clone()), continuation)?;
            },
            Computation::TupleProjection(tuple, component) => {
                self.select(tuple, Selector::Component(component), continuation)?;
            },
            Computation::Split {
                scrutinee,
                arity,
                body,
                ..
            } => {
                let inner = self.share_or_name(FocusOrigin::Case, continuation)?;
                self.tasks
                    .push(Task::Split(ProducerArity::from(usize::from(arity))));
                self.tasks.push(Task::Value(scrutinee));
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: inner,
                });
            },
            Computation::DataCase {
                scrutinee,
                ref branches,
                ..
            } => {
                self.tasks.push(Task::DataCase {
                    branches: NodeCount::from(branches.len()),
                    continuation,
                });
                self.tasks.push(Task::Value(scrutinee));
                for &branch in branches.iter().rev() {
                    let return_point = self.innermost_covariable()?;
                    self.tasks.push(Task::Thunk);
                    self.tasks.push(Task::Computation {
                        computation: branch,
                        continuation: return_point,
                    });
                }
            },
            Computation::Perform { payload, .. } => {
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                self.tasks.push(Task::Value(payload));
            },
            Computation::Exercise {
                capability,
                payload,
                ..
            } => {
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                self.tasks.push(Task::Value(payload));
                self.tasks.push(Task::Value(capability));
            },
            Computation::Handle {
                subject,
                on_return,
                ref clauses,
                ..
            }
            | Computation::Scope {
                subject,
                on_return,
                ref clauses,
                ..
            } => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                for clause in clauses.iter().rev() {
                    self.tasks.push(Task::Computation {
                        computation: clause.body,
                        continuation: return_point,
                    });
                }
                self.tasks.push(Task::Computation {
                    computation: on_return,
                    continuation: return_point,
                });
                self.tasks.push(Task::Computation {
                    computation: subject,
                    continuation: return_point,
                });
            },
            Computation::Resume(stack, body) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
                self.tasks.push(Task::Value(stack));
            },
            Computation::Reset(body) | Computation::Shift(body) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
            },
            Computation::Memory(ref form) => {
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                for body in form.computations().rev() {
                    let return_point = self.innermost_covariable()?;
                    self.tasks.push(Task::Computation {
                        computation: body,
                        continuation: return_point,
                    });
                }
                for value in form.values() {
                    self.tasks.push(Task::Value(value));
                }
            },
            Computation::With(left, right) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Control {
                    source: id,
                    continuation,
                });
                self.tasks.push(Task::Computation {
                    computation: right,
                    continuation: return_point,
                });
                self.tasks.push(Task::Computation {
                    computation: left,
                    continuation: return_point,
                });
            },
            Computation::Project(side, subject) => {
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Project(side),
                    producers: alloc::boxed::Box::from([]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                self.tasks.push(Task::Computation {
                    computation: subject,
                    continuation: frame,
                });
            },
            // An ascription is the checker's: the sequent runs its body
            // against the same continuation.
            Computation::Ascribe { body, .. } => {
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation,
                });
            },
            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => {
                let mut annotations =
                    gandr_core_term::TypeImporter::new(self.core, self.arena.annotations_mut());
                let element =
                    annotations
                        .value_type(element)
                        .map_err(|gandr_core_term::ImportFault| {
                            MintRefusal::DanglingAnnotation(element)
                        })?;
                let result =
                    annotations
                        .value_type(result)
                        .map_err(|gandr_core_term::ImportFault| {
                            MintRefusal::DanglingAnnotation(result)
                        })?;
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::ListFold {
                    element,
                    result,
                    continuation,
                });
                self.tasks.push(Task::Value(list));
                self.tasks.push(Task::Computation {
                    computation: on_cons,
                    continuation: return_point,
                });
                self.tasks.push(Task::Computation {
                    computation: on_nil,
                    continuation: return_point,
                });
            },
            Computation::Primitive {
                primitive,
                arguments,
            } => {
                self.tasks.push(Task::Primitive {
                    primitive,
                    arguments,
                    continuation,
                });
                for argument in arguments.iter().rev() {
                    self.tasks.push(Task::Value(*argument));
                }
            },
            Computation::Transport(..) => return Err(FocusRefusal::UniverseTransport(id)),
            Computation::PathTransport { .. } | Computation::TelescopeTransport { .. } => {
                return Err(FocusRefusal::ElementTransport(id));
            },
            Computation::Hole(_) | Computation::Mark { .. } => {
                return Err(FocusRefusal::IncompleteComputation(id));
            },
            Computation::Session(_) => return Err(FocusRefusal::Session(id)),
            Computation::World(_) => return Err(FocusRefusal::World(id)),
            Computation::Fixpoint { body, evidence } => {
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    producers: alloc::boxed::Box::from([]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                self.tasks.push(Task::Cut {
                    origin: FocusOrigin::Fixpoint,
                    polarity: Polarity::Positive,
                    consumer: frame,
                });
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Fixpoint(evidence));
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
            },
            // A ride runs as its motive's action applied to the flow's
            // translator and the ridden value.
            Computation::Ride {
                motive,
                flow,
                value,
            } => {
                self.tasks.push(Task::Combinator {
                    combinator: crate::flow::Combinator::Act(motive),
                    continuation,
                });
                self.tasks.push(Task::Value(value));
                self.tasks.push(Task::Value(flow));
            },
            Computation::Return(value) => {
                self.tasks.push(Task::Cut {
                    origin: FocusOrigin::Return,
                    polarity: Polarity::Positive,
                    consumer: continuation,
                });
                self.tasks.push(Task::Value(value));
            },
            Computation::Force(value) => {
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    producers: alloc::boxed::Box::from([]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                self.tasks.push(Task::Cut {
                    origin: FocusOrigin::Force,
                    polarity: Polarity::Positive,
                    consumer: frame,
                });
                self.tasks.push(Task::Value(value));
            },
            Computation::Application(head, argument) => {
                self.tasks.push(Task::Apply { head, continuation });
                self.tasks.push(Task::Value(argument));
            },
            Computation::Lambda(body) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Lambda { continuation });
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
            },
            Computation::Bind(head, body) => {
                let inner = self.share_or_name(FocusOrigin::Bind, continuation)?;
                self.tasks.push(Task::Bind { head });
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: inner,
                });
            },
            Computation::Case {
                scrutinee,
                ref branches,
            } => {
                let inner = self.share_or_name(FocusOrigin::Case, continuation)?;
                self.tasks.push(Task::Case {
                    branches: NodeCount::from(branches.len()),
                });
                self.tasks.push(Task::Value(scrutinee));
                for &branch in branches.iter().rev() {
                    self.tasks.push(Task::Computation {
                        computation: branch,
                        continuation: inner,
                    });
                }
            },
        }
        Ok(())
    }

    /// Schedule `𝓕⟦v.f⟧c = ⟨𝓥⟦v⟧ |+ select[f](c)⟩`: the selection carries `c`
    /// beside its field and opens no binder, so `c` is neither shifted nor
    /// named.
    ///
    /// # Specification
    /// - requires: `continuation` was minted for the projection's depth.
    /// - ensures: the selection of `selector` returning to `continuation` is
    ///   minted, and the positive cut of `subject`'s producer against it is
    ///   scheduled, recorded as [`FocusOrigin::Projection`].
    /// - provides: the image of a record projection and a tuple projection.
    /// - fails: a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a component and a label projection of a variable,
    ///   each under a non-tail continuation, are observed at their exact
    ///   selector, continuation, cut polarity and origin; a selection that
    ///   named or shifted its continuation changes the consumer it returns to.
    /// - witness: `focus::tests::a_projection_selects_by_position_or_label`
    #[spec(
        captures: [work = self.tasks.len()],
        ensures: |ret| ret.is_err() || (work.checked_add(2) == Some(self.tasks.len())
            && matches!(self.tasks.last(), Some(&Task::Value(scheduled)) if scheduled == subject)),
    )]
    fn select(
        &mut self,
        subject: ValueId,
        selector: Selector,
        continuation: ConsumerId,
    ) -> Result<(), FocusRefusal>
    {
        let select = self.arena.mint_consumer(ConsumerNode::Select {
            selector,
            then: continuation,
        })?;
        self.tasks.push(Task::Cut {
            origin: FocusOrigin::Projection,
            polarity: Polarity::Positive,
            consumer: select,
        });
        self.tasks.push(Task::Value(subject));
        Ok(())
    }

    /// The continuation a binder's body is translated under: `continuation`
    /// itself when it is a tail, otherwise the innermost covariable, with the
    /// naming cut scheduled to run once the body's command is built.
    ///
    /// # Specification
    /// - requires: `continuation` resolves.
    /// - ensures: a tail is returned unchanged and nothing is scheduled; any
    ///   other continuation is named by a [`Task::Name`] at the polarity of
    ///   what it observes, and covariable `0` is returned.
    /// - provides: the rule that keeps a continuation from being copied under a
    ///   binder.
    /// - fails: a dangling continuation, as
    ///   [`FocusRefusal::TranslationInvariant`], or a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independently decoded bind/case contexts distinguish
    ///   copied continuations and shifted binders. L3 — named and tail
    ///   continuations are observed at their exact consumer and scheduled cut.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `focus::tests::focusing_mints_no_name`
    #[spec(
        captures: [work = self.tasks.len()],
        ensures: |ret| ret.is_err() || ret.is_ok_and(|id|
            if matches!(self.arena.consumer(continuation), Some(&ConsumerNode::Top | &ConsumerNode::Covariable(_))) {
                id == continuation && self.tasks.len() == work
            } else {
                self.arena.consumer(id) == Some(&ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
                    && work.checked_add(1) == Some(self.tasks.len())
                    && matches!(self.tasks.last(), Some(&Task::Name { origin: recorded, continuation: target, .. })
                        if recorded == origin && target == continuation)
            }),
    )]
    fn share_or_name(
        &mut self,
        origin: FocusOrigin,
        continuation: ConsumerId,
    ) -> Result<ConsumerId, FocusRefusal>
    {
        let polarity = match *self
            .arena
            .consumer(continuation)
            .ok_or(FocusRefusal::TranslationInvariant)?
        {
            ConsumerNode::Covariable(_) | ConsumerNode::Top => return Ok(continuation),
            ConsumerNode::Destructor { tag, .. } => tag.polarity(),
            ConsumerNode::MuTilde { .. }
            | ConsumerNode::Case { .. }
            | ConsumerNode::DataCase { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::ListFold { .. } => Polarity::Positive,
        };
        self.tasks.push(Task::Name {
            origin,
            polarity,
            continuation,
        });
        self.innermost_covariable()
    }

    /// Mint the covariable `0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success a new consumer names covariable `0`.
    /// - provides: the return point of a newly opened covariable binder.
    /// - fails: a refused consumer mint at the address ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// A consumer-family allocation refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every focused covariable is read at its exact index,
    ///   exposing shifted binders. The shared address helper witnesses the
    ///   ceiling; no full-sized consumer arena is allocated.
    /// - witness: `focus::tests::focusing_mints_no_name`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|id|
        self.arena.consumer(id) == Some(&ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
    ))]
    fn innermost_covariable(&mut self) -> Result<ConsumerId, FocusRefusal>
    {
        Ok(self
            .arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))?)
    }

    /// The producer of a closed flow combinator this run applies.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the producer [`with_combinators`] focused for `combinator`
    ///   before this run; for one it did not, `combinator` is recorded as
    ///   wanted and a placeholder stands in, which the rerun replaces.
    /// - provides: the closed programs a flow's image applies to its parts,
    ///   without a nested run.
    /// - fails: a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a composite and a ride focused and run reach the
    ///   values the kernel's rows compute, which a placeholder left in place
    ///   would not.
    /// - witness: `tests::run::rides_run_by_the_motives_action`
    #[spec(ensures: |ret| ret.is_err() || self.prepared.contains_key(&combinator) || self.wanted.contains(&combinator))]
    fn combinator(
        &mut self,
        combinator: crate::flow::Combinator,
    ) -> Result<ProducerId, FocusRefusal>
    {
        if let Some(&producer) = self.prepared.get(&combinator) {
            return Ok(producer);
        }
        let _first = self.wanted.insert(combinator);
        Ok(self.arena.mint_producer(ProducerNode::Constant(
            gandr_kernel_term::ConstantIndex::from(0_usize),
        ))?)
    }

    /// Mint a constructor over producer fields and push it.
    ///
    /// # Specification
    /// - requires: `fields` has the head's arity.
    /// - ensures: the constructor is pushed.
    /// - provides: the one constructor mint of `𝓥`.
    /// - fails: a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — decoded generated values and one case per former
    ///   observe constructor identity and ordered fields. Wrong tags, missing
    ///   children and reversed pairs change the recovered source.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    #[spec(
        requires: fields.len() == usize::from(tag.producer_arity()),
        ensures: |ret| ret.is_err() || self.producers.last()
            .and_then(|id| self.arena.producer(*id)).is_some_and(|node| matches!(*node,
                ProducerNode::Constructor { ref producers, ref consumers, .. }
                    if producers.as_ref() == fields && consumers.is_empty())),
    )]
    fn constructor(
        &mut self,
        tag: ConstructorTag,
        fields: &[ProducerId],
    ) -> Result<(), FocusRefusal>
    {
        let producer = self.arena.mint_producer(ProducerNode::Constructor {
            tag,
            producers: alloc::boxed::Box::from(fields),
            consumers: alloc::boxed::Box::from([]),
        })?;
        self.producers.push(producer);
        Ok(())
    }

    /// Mint a cut, record its origin, and push it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cut is pushed and recorded with `origin`.
    /// - provides: the one cut mint of `𝓕`, so every created command has an
    ///   origin.
    /// - fails: a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independently decoded terms expose changed cut
    ///   endpoints and polarity. L3 — the top-value entry observes its exact
    ///   terminal continuation and origin.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::top_level_value_focuses_against_top`
    #[spec(
        captures: [results = self.commands.len()],
        ensures: |ret| ret.is_err() || (results.checked_add(1) == Some(self.commands.len())
            && self.commands.last().is_some_and(|id| self.provenance.origin(*id) == Some(origin)
                && self.arena.command(*id) == Some(&crate::il::CommandNode::Cut { polarity, producer, consumer }))),
    )]
    fn cut(
        &mut self,
        origin: FocusOrigin,
        polarity: Polarity,
        producer: ProducerId,
        consumer: ConsumerId,
    ) -> Result<(), FocusRefusal>
    {
        let command = self.arena.mint_cut(polarity, producer, consumer)?;
        self.provenance.record(command, origin);
        self.commands.push(command);
        Ok(())
    }

    /// Pop a translated producer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the last producer is removed and returned; an empty stack is
    ///   unchanged and refused.
    /// - provides: the checked result pop used by finishing tasks.
    /// - fails: [`FocusRefusal::TranslationInvariant`] on an empty stack.
    /// - panics: none.
    ///
    /// # Errors
    /// The missing-result invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two distinct results are popped in reverse order,
    ///   then exact underflow is observed. Wrong-end removal, stale results and
    ///   silent underflow change the answer.
    /// - witness: `focus::tests::result_stacks_enforce_singletons_and_lifo`
    #[spec(
        captures: [last = self.producers.last().copied(), length = self.producers.len()],
        ensures: |ret| ret == last.ok_or(FocusRefusal::TranslationInvariant)
            && self.producers.len() == length.saturating_sub(1),
    )]
    fn pop_producer(&mut self) -> Result<ProducerId, FocusRefusal>
    {
        self.producers
            .pop()
            .ok_or(FocusRefusal::TranslationInvariant)
    }

    /// Pop a translated command.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the last command is removed and returned; an empty stack is
    ///   unchanged and refused.
    /// - provides: the checked result pop used by finishing tasks.
    /// - fails: [`FocusRefusal::TranslationInvariant`] on an empty stack.
    /// - panics: none.
    ///
    /// # Errors
    /// The missing-result invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two distinct results are popped in reverse order,
    ///   then exact underflow is observed. Wrong-end removal, stale results and
    ///   silent underflow change the answer.
    /// - witness: `focus::tests::result_stacks_enforce_singletons_and_lifo`
    #[spec(
        captures: [last = self.commands.last().copied(), length = self.commands.len()],
        ensures: |ret| ret == last.ok_or(FocusRefusal::TranslationInvariant)
            && self.commands.len() == length.saturating_sub(1),
    )]
    fn pop_command(&mut self) -> Result<CommandId, FocusRefusal>
    {
        self.commands
            .pop()
            .ok_or(FocusRefusal::TranslationInvariant)
    }

    /// The one command a computation's translation leaves.
    ///
    /// # Specification
    /// - requires: the translation has been driven.
    /// - ensures: the single command, with no producer left over.
    /// - provides: the result of a computation entry point.
    /// - fails: [`FocusRefusal::TranslationInvariant`] for any other shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite product of zero, one and two results on
    ///   each stack distinguishes missing, surplus and wrong-kind results. The
    ///   observer is the exact singleton or invariant refusal.
    /// - witness: `focus::tests::result_stacks_enforce_singletons_and_lifo`
    #[spec(
        requires: self.tasks.is_empty(),
        captures: [single = self.commands.len() == 1 && self.producers.is_empty(), last = self.commands.last().copied()],
        ensures: |ret| ret == if single { last.ok_or(FocusRefusal::TranslationInvariant) }
            else { Err(FocusRefusal::TranslationInvariant) },
    )]
    fn single_command(mut self) -> Result<CommandId, FocusRefusal>
    {
        let command = self.pop_command()?;
        if self.commands.is_empty() && self.producers.is_empty() {
            Ok(command)
        }
        else {
            Err(FocusRefusal::TranslationInvariant)
        }
    }

    /// The one producer a value's translation leaves.
    ///
    /// # Specification
    /// - requires: the translation has been driven.
    /// - ensures: the single producer, with no command left over.
    /// - provides: the result of a value entry point.
    /// - fails: [`FocusRefusal::TranslationInvariant`] for any other shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite product of zero, one and two results on
    ///   each stack distinguishes missing, surplus and wrong-kind results. The
    ///   observer is the exact singleton or invariant refusal.
    /// - witness: `focus::tests::result_stacks_enforce_singletons_and_lifo`
    #[spec(
        requires: self.tasks.is_empty(),
        captures: [single = self.producers.len() == 1 && self.commands.is_empty(), last = self.producers.last().copied()],
        ensures: |ret| ret == if single { last.ok_or(FocusRefusal::TranslationInvariant) }
            else { Err(FocusRefusal::TranslationInvariant) },
    )]
    fn single_producer(mut self) -> Result<ProducerId, FocusRefusal>
    {
        let producer = self.pop_producer()?;
        if self.commands.is_empty() && self.producers.is_empty() {
            Ok(producer)
        }
        else {
            Err(FocusRefusal::TranslationInvariant)
        }
    }
}

#[cfg(test)]
mod tests;
