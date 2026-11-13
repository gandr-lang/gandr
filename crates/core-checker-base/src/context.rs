//! The checking context: the core context the judgement goes under binders in,
//! wrapped with what the core context does not hold.
//!
//! # A wrapper, not an extension of the core context
//!
//! `gandr-core-term`'s [`Context`] is the flat, de Bruijn, name-free binder
//! stack, and it stays that. What checking adds sits here beside it: the
//! signature table from admission positions to the types declarations
//! supplied, the highest admission position so far, the atoms the literal and
//! unit rules hand out, the definitions a code may unfold to, the sealed
//! abstract types with the sites that minted them, the lifts the judgement
//! decided, and the step allowance. A later synthesised context lands in this
//! wrapper too, so no checking concern widens the core crate.
//!
//! The binder stack is empty between judgements and restored to where it stood
//! whenever a run is refused. The alternative was adding the signature table to
//! the core crate; the wrapper moves down when a second consumer needs the same
//! one.
//!
//! # The context mints
//!
//! A dependent type is rewritten as it is read — a binder's type shifted to
//! the depth it is read at, a codomain instantiated at its argument, a quote's
//! universe minted at its type's level — so the context holds the arena
//! mutably and the judgement mints into it. A shift mints nothing until it is
//! settled: a variable's slot type reaches the value bridge as a relocated id
//! the conversion reads through, and every other rule settles it where it
//! reads it. Every node minted is a type the judgement reads; no term the
//! producer built is changed.
//!
//! # Resolution by admission position
//!
//! A declaration's type enters the signature table only after its own body
//! was judged, and a declaration is admitted only above every position already
//! admitted. A body therefore sees exactly the declarations strictly before
//! it: self-reference and mutual reference find no type, whatever the producer
//! resolved.
//!
//! A declared type is the contract and enters the table whether or not the body
//! met it, so one wrong body does not turn every later reference into an
//! unknown constant; an unsigned body supplies a type only when it synthesised
//! one. The alternative was withholding a signed declaration whose body was
//! refused, which cascades a single mistake into every later reference.
//!
//! Recursion keeps this order. A fixpoint binds its own thunk as a variable,
//! `fix x. M` with `x : U C`, so a recursive body refers to that binder, never
//! to its own admission position, and erases to the kernel's former without a
//! self-referential constant. One resolution rule then serves the checker, the
//! bridge and the kernel's admission prefix, and a `rec { … }` form that admits
//! a body referring to its own declaration is not needed. A data declaration's
//! self occurrence is the one exception, read through the declaration's own
//! signature while that declaration forms.
//!
//! # Adopted answers
//!
//! A caller that holds a declaration's earlier verdict and has shown it still
//! answers — an incremental checker comparing the verdict's support pointwise
//! — may admit the declaration with the type it supplied before, through
//! [`CheckingContext::adopt`], instead of judging it again. Admission order
//! binds an adopted declaration exactly as a judged one.
//!
//! # A sealed atom is manifest inside its seal
//!
//! An abstract type admitted at position `a` with extent `n` stands for its
//! representation while the judgement reads a declaration at a position in
//! `a + 1 ..= a + n` — the sealing module's own members and the witnesses that
//! check them at the signature — and for itself everywhere else. The weak head
//! reads it through, so a member checks at the representation inside the
//! module and an export read from outside meets the atom, which relates to
//! nothing but itself. The kernel decides manifestness by the same rule over
//! the same positions, so the two sides agree on every reading.
//!
//! The alternatives were substituting the representation into the members'
//! types before checking them, which leaves no single place that knows where
//! the seal ends, and a scope pushed and popped around the module, which a
//! checker judging one declaration at a time — the incremental one — cannot
//! reconstruct. The choice reverses with nested sealing that reaches back over
//! an enclosing seal, which needs a stack of extents rather than one per atom.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
#[cfg(feature = "unfolding-probe")]
use gandr_core_nbe::UnfoldingProbe;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Context;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerWidth;
use quenchant_shape::shape::Maybe;

use crate::code::CodeDefinitions;
use crate::code::Lift;
use crate::code::Unfolded;
use crate::code::unfolding;
use crate::declaration::AbstractType;
use crate::formation::FormedValueType;
use crate::formation::level_of;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::seal::SealId;
use crate::seal::SealTable;
use crate::support::Consulted;
use crate::support::Support;
use crate::support::SupportLog;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

quenchant_shape::reason_enum! {
    /// Why the signature table holds no type for a position.
    pub mod signature_table {
        /// The reason no type is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No declaration at that position supplied a type: none was
            /// admitted there yet, its body synthesised nothing, or the
            /// producer withheld it.
            Untyped,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no admission position has been admitted.
    mod admission {
        /// The reason nothing is admitted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The context has admitted no declaration yet.
            Fresh,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no mutual block is open.
    mod mutual {
        /// The reason no block is open.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Each declaration judged is admitted alone.
            Lone,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no fixpoint of the declaration under way is its own.
    pub mod own {
        /// The reason none is.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration under way opened no fixpoint.
            Unopened,
            /// The fixpoint it opened has closed.
            Closed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no nominal signature is in scope at a position.
    pub mod data_scope {
        /// The reason no signature is in scope.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No admitted declaration and no forming block names the
            /// position.
            Unknown,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a hole stands in no pattern's place.
    pub mod pattern_hole {
        /// The reason it does not.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The hole was written in a term, not in place of a pattern.
            Term,
        }
    }
}

/// The work one judgement may spend before it refuses.
///
/// One step is charged per machine transition. A goal the run's memo answers
/// is one transition, so a subterm met again at a goal already judged costs one
/// step. The allowance therefore bounds the shared work of a run, and not the
/// size of the tree a shared term unfolds to.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CheckBudget(usize);

impl CheckBudget
{
    /// The allowance a caller with no reason to bound the judgement takes.
    pub const DEFAULT: Self = Self(1_000_000_usize);
}

impl From<usize> for CheckBudget
{
    /// The allowance of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: usize) -> Self
    {
        Self(steps)
    }
}

impl From<CheckBudget> for usize
{
    /// The number of steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: CheckBudget) -> Self
    {
        budget.0
    }
}

impl fmt::Display for CheckBudget
{
    /// Writes the number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// The value types the literal and unit rules synthesise.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Atoms
{
    /// The unit type.
    unit: FormedValueType,
    /// The integer atom.
    integer: FormedValueType,
    /// The string atom.
    string: FormedValueType,
    /// The character atom.
    character: FormedValueType,
    /// The 64-bit floating-point atom.
    float64: FormedValueType,
    /// The `u32` width atom.
    u32: FormedValueType,
    /// The `u64` width atom.
    u64: FormedValueType,
    /// The `i32` width atom.
    i32: FormedValueType,
    /// The `i64` width atom.
    i64: FormedValueType,
}

/// Which atom a leaf rule synthesises.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Atom
{
    /// The unit type, for the unit value.
    Unit,
    /// The integer atom, for an integer literal.
    Integer,
    /// The string atom, for a string literal.
    String,
    /// The character atom, for a character literal.
    Character,
    /// The 64-bit floating-point atom, for a floating-point literal.
    Float64,
    /// An integer width atom, for a literal of that width.
    Fixed(IntegerWidth),
}

/// An abstract type the context admitted, with the level of the universe it
/// inhabits.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Sealed
{
    /// The declaration, as offered.
    declared: AbstractType,
    /// The level of its kind.
    level: Level,
}

/// How many definitions the open foresights had foreseen when one opened:
/// what [`CheckingContext::forget_foresight`] returns the signature table to.
///
/// A foresight opens and closes on the judgement machine's frame stack, so
/// a case's branch forms its identified telescope without the machine calling
/// back into itself.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Foresight(usize);

/// The core context wrapped with the signature table, the admission position,
/// the atoms, the code definitions, the sealed abstract types, the lifts and
/// the step allowance.
///
/// The context derives nothing: it borrows the whole arena, and an equality
/// or a debug rendering of it would read every node.
pub struct CheckingContext<'arena>
{
    /// The arena every id the judgement reads resolves in, and the types it
    /// rewrites are minted into.
    arena: &'arena mut CoreArena,
    /// The binders the judgement is under; empty between judgements.
    binders: Context,
    /// The types declarations supplied, ascending by admission position.
    signatures: Vec<(ConstantIndex, FormedValueType)>,
    /// Successfully formed nominal signatures, without a value unfolding.
    data_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::DataSignature>>,
    /// Successfully formed codata signatures, by position.
    codata_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::CodataSignature>>,
    /// What each data declaration's occurrence walk decided, kept once its
    /// signature forms.
    accessibility: BTreeMap<ConstantIndex, crate::occurrence::Accessibility>,
    /// The highest admission position admitted, or why there is none.
    admitted: Maybe<ConstantIndex, admission::Absent>,
    /// The atoms the leaf rules hand out.
    atoms: Atoms,
    /// The bodies a code constant unfolds to.
    definitions: CodeDefinitions,
    /// The codes checked at a universe above their own, by node.
    lifts: BTreeMap<ValueId, Lift>,
    /// The function extensionalities the judgement decided, by node, with
    /// the evaluations each component replays.
    funexts: BTreeMap<ValueId, crate::funext::Funext>,
    /// The values the value bridge coerced in to a patched type, by node, each
    /// with the fixed fields it compared.
    coercions: BTreeMap<ValueId, crate::conversion::Coercion>,
    /// The universe equivalences the judgement decided, by node, with the
    /// evidence each round trip replays.
    equivalences: BTreeMap<ValueId, crate::equiv::Equivalence>,
    /// The session statements the judgement decided, by node, with the
    /// engine's pairs the kernel replays.
    flows: BTreeMap<ValueId, crate::flow::Statement>,
    /// The forward and function flows the judgement decided, by node, with
    /// the images and dialogues the kernel replays.
    directed: BTreeMap<ValueId, crate::forward::Directed>,
    /// The family each transport or ride along a path or a flow above level
    /// zero formed its motive as, by node: its written motive with the
    /// binder's decodes read at the carrier's level.
    motives: BTreeMap<ComputationId, ValueTypeId>,
    /// The payload type each send and each receive the judgement checked
    /// moves, by node: the type a send's value was checked at, and the type a
    /// receive opened its slot at — a value's payload type, or the session or
    /// buffer at the payload's weak head.
    payloads: BTreeMap<ComputationId, ValueTypeId>,
    /// The types each handler and capability scope the judgement checked was
    /// judged at, by node: its subject's result and its answer.
    handled: BTreeMap<ComputationId, crate::handler::Handled>,
    /// The computations the judgement checked or synthesised at a returner
    /// over a row of operations, and the levels of those returners.
    rows: crate::program::Rows,
    /// The records [`Self::rows`] gained since the first run of the body
    /// under way began: what its second run forgets.
    gained_rows: Vec<crate::program::Gained>,
    /// The reflexivities the judgement checked, by node, with the dialogues
    /// relating each point to its endpoints.
    reflexivities: BTreeMap<ValueId, crate::code::Reflexivity>,
    /// How the judgement decided each computation written where a value is
    /// read, by node, since the declaration under way began.
    nesting: BTreeMap<ValueId, crate::nested::Nesting>,
    /// The crossing each value the value bridge carried from a model of a
    /// theory to a model of one it includes, or from a model with manifest
    /// sorts to its theory's models, crossed by, by node, since the
    /// declaration under way began.
    crossings: BTreeMap<ValueId, gandr_core_term::Crossing>,
    /// The labels each record update keeps of its base, by node, since the
    /// declaration under way began.
    updates: BTreeMap<ValueId, Vec<gandr_kernel_term::FieldLabel>>,
    /// The path endpoint pairs the judgement's type conversions related since
    /// the declaration under way began, by pair, with each derivation.
    relating: BTreeMap<(ValueId, ValueId), crate::code::EndpointRelation>,
    /// The path endpoint pairs each accepted declaration's type conversions
    /// related, by position.
    relations: BTreeMap<ConstantIndex, Vec<crate::code::EndpointRelation>>,
    /// The nodes the judgement checked in another form than written since the
    /// declaration under way began, each beside the node checked in its place:
    /// an arm or a case refined by a solved variable, and a constructor
    /// restated at its stated application.
    restating: BTreeMap<TermNode, TermNode>,
    /// What reads each refinement since the last take back as written.
    readings: crate::solution::Written,
    /// The restated nodes of each accepted declaration, by position, each
    /// beside the node the kernel reads in its place, ascending by the restated
    /// node.
    restatements: BTreeMap<ConstantIndex, Vec<(TermNode, TermNode)>>,
    /// The laws each lawful declaration's folds rest on, by position, in its
    /// folded type's rule order.
    laws: BTreeMap<ConstantIndex, Vec<ConstantIndex>>,
    /// The rules of the operation each ruled declaration lowered from, by
    /// position; the judgement carries them to the kernel unread.
    operation_rules: BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>,
    /// The matches of each declaration's body with their derivations, by
    /// position; the judgement carries them to the kernel unread.
    covers: BTreeMap<ConstantIndex, Vec<(ComputationId, gandr_kernel_term::cover::Cover)>>,
    /// The stage signature of each definition quantified over stages, by
    /// position: its binders' bounds and the occurrences its plain declared
    /// type holds each binder's stage at.
    stage_signatures: BTreeMap<ConstantIndex, gandr_kernel_term::StageSignature>,
    /// The native universe path each univalence statement the judgement
    /// decided derives, each path product it judged elaborates to, and the
    /// value each fill's induction returns, by node.
    natives: BTreeMap<ValueId, ValueId>,
    /// The abstract types admitted, by position.
    sealed: BTreeMap<ConstantIndex, Sealed>,
    /// The sites that minted them, in minting order.
    seals: SealTable,
    /// The declaration that holds each built-in role.
    builtins: BTreeMap<gandr_kernel_term::Builtin, ConstantIndex>,
    /// The allowance each judgement starts with.
    budget: CheckBudget,
    /// The answers the running supported judgement consulted, when one runs.
    support: SupportLog,
    /// Residual equations recorded only inside the elaboration entry point.
    deferrals: crate::elaboration::Deferrals,
    /// The data declarations whose signatures are forming, each naming
    /// itself and the others: one alone, or the families of a mutual block.
    forming: Vec<(
        ConstantIndex,
        alloc::sync::Arc<gandr_core_term::DataSignature>,
    )>,
    /// The codata declaration whose observations are forming: it names
    /// itself only at an observation's result.
    codata_forming: Vec<(
        ConstantIndex,
        alloc::sync::Arc<gandr_core_term::CodataSignature>,
    )>,
    /// The mutual block being admitted, while one is.
    mutual: Maybe<crate::occurrence::Block, mutual::Absent>,
    /// The bodies of the open mutual block's definitions, by position: the
    /// occurrence walk reads a field naming one through its body.
    defining: Vec<(ConstantIndex, ValueId)>,
    /// Every mutual block of several families opened so far: its families
    /// share one stage.
    kin: Vec<crate::occurrence::Block>,
    /// The declared types the open mutual block foresaw for its definitions
    /// not yet admitted, ascending: a family's field read inside a definition
    /// names them, as the family did.
    hindsight: Vec<(ConstantIndex, FormedValueType)>,
    /// The definitions the open foresights foresaw from hindsight, in the
    /// order they were foreseen: what each closes again.
    foreseen: Vec<ConstantIndex>,
    /// The authority the host grants the module's held capabilities.
    grants: crate::capability::Grants,
    /// The term judgements and type formations a typed run finished, in the
    /// order finished, when one is recording.
    typings: Option<crate::record::Kept>,
    /// The types whose formations a recording keeps, and which of them it
    /// has kept.
    formations: Wanted,
    /// The stages the recursion typing minted since the declaration under way
    /// began.
    stages: gandr_kernel_core::stage_order::StageOrder,
    /// The stages the declaration under way's calls supply their callees'
    /// binders at, each at the value its call forces.
    supplies: Vec<gandr_core_term::staged::Supply>,
    /// The fixpoint the definition under way thunks as its body — its own —
    /// and, while that fixpoint is open, the depth below its self binder and
    /// that binder's type.
    own: (
        Maybe<ComputationId, own::Absent>,
        Maybe<(BinderDepth, ValueTypeId), own::Absent>,
    ),
    /// How the definition under way's own fixpoint reads its result: as
    /// declared, or at the stage of the parameter it recurses on.
    result_stage: crate::recursion::ResultStage,
    /// The definitions admitted whose result stands at the stage of the
    /// parameter their recursion is staged on, with that parameter's position.
    following: BTreeMap<ConstantIndex, gandr_kernel_term::StagedPosition>,
    /// The worlds declared, each declaration's home, the entries, the host's
    /// entry and the entry under way.
    worlds: crate::worlds::Worlds,
    /// The holes the module's matches were written with in place of a
    /// pattern: a tree leaf that is one of them leaves an arm undecided.
    pattern_holes: BTreeSet<HoleId>,
    /// The reducts the module mints, each restricting the models of a theory
    /// to the models of one it includes: the value bridge crosses by one where
    /// a model of the first stands at a model of the second.
    reducts: Vec<gandr_kernel_term::ConstantIndex>,
    /// The literal readers the module lends, each a model's `fromNat` or
    /// `fromNeg`: the value bridge crosses an integer literal by the one of
    /// its kind whose carrier is the type the literal is checked at.
    readers: Vec<gandr_core_term::LiteralReader>,
    /// The tier an endpoint pair is offered before the machine, when the run
    /// handed one. A checkpoint does not keep it: a resumed context takes its
    /// own.
    tier: Option<alloc::boxed::Box<dyn crate::tier::EndpointTier>>,
    /// Whether a closed pair the tier meets crosses as an admitted result the
    /// kernel takes, or as an evaluation it derives. A checkpoint does not
    /// keep it, as it does not keep the tier.
    admitting: gandr_kernel_core::AdmissionPolicy,
    /// The catalogues and strata the context holds for its life, and the
    /// store it recalls them from and keeps them to. A checkpoint does not
    /// keep them: a resumed context takes the store it is handed.
    strata: crate::ua::Strata,
    /// Whether each run of the machine keeps a goal memo. A checkpoint does
    /// not keep it: a resumed context keeps one.
    memo: MemoActivity,
    /// The goal memo's hits and misses over every run in this context, which
    /// the counts layer reads before and after each item. A checkpoint does
    /// not keep it: a resumed context counts from zero.
    #[cfg(feature = "instrument")]
    tally: crate::tally::MemoTally,
    /// The buffer each run of the machine writes its steps into, while a
    /// tracer lends one. A checkpoint does not keep it: a resumed context
    /// holds none until a tracer lends it one.
    #[cfg(feature = "instrument")]
    trace: Option<crate::trace::StepBuffer>,
    /// The step [`Self::unfold`] certified at each code: the reduct and what
    /// the step unfolded. The definitions only grow, and a certified step
    /// reads only them and the arena. So a second unfold of a code reads the
    /// held step and certifies nothing. A checkpoint does not keep it: a
    /// resumed context certifies again.
    unfolded: BTreeMap<ValueId, (ValueId, Unfolded)>,
}

/// Whether a typed run is recording the judgements it holds as they finish.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Recording
{
    /// No typed run is under way: nothing is kept.
    Off,
    /// A typed run is under way: every judgement keeps what it finished.
    On,
}

/// The types whose formations a typed run keeps with their levels.
///
/// A formation's level is read under the binders it was formed under, so it
/// is read when the formation finishes; reading it for every formation a run
/// makes is the larger part of what recording costs, and a caller answering
/// written types needs only the first formation of each. Reversal: a caller
/// that answers every formed type, or every formation of one.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum Formations
{
    /// Every formation.
    #[default]
    All,
    /// Only the first formation of each of these types, ascending and
    /// unique.
    Firsts(Vec<crate::refusal::TypeNode>),
}

/// [`Formations`] as a recording consumes it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Wanted
{
    /// Every formation.
    All,
    /// The first formation of each type, with whether it was kept.
    Firsts(Vec<(crate::refusal::TypeNode, First)>),
}

/// Whether a wanted type's first formation was kept.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum First
{
    /// Not formed yet.
    Pending,
    /// Formed and kept.
    Kept,
}

/// Whether a value selects a variable in either zone.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Closure
{
    /// It selects none.
    Closed,
    /// It selects one, or the arena records no support for it.
    Open,
}

/// A checking context's state between two judgements, its arena released.
///
/// A later run continues from it over the arena the state was reached in, or
/// over a copy of it that more nodes were minted into after.
///
/// # Specification
/// - requires: taken between two judgements, no supported judgement logging and
///   no term-producing run recording ([`CheckingContext::checkpoint`]).
/// - ensures: [`CheckingContext::resume`] over such an arena, handed the tier
///   and the admission policy the context held
///   ([`CheckingContext::decide_endpoints_on`]), judges what the context it was
///   taken from would have judged next.
/// - executable: none — a data type; the witness judges a module in two runs
///   with a checkpoint between and compares the report with one run's.
///
/// # Adequacy
/// - hypothesis: L3 — a module whose mutual block ends where the checkpoint is
///   taken, resumed over a copy of the arena, reports what one run over the
///   whole module reports and mints the same arena.
/// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
#[derive(Clone, Debug)]
pub struct Checkpoint
{
    /// [`CheckingContext::binders`].
    binders: Context,
    /// [`CheckingContext::signatures`].
    signatures: Vec<(ConstantIndex, FormedValueType)>,
    /// [`CheckingContext::data_signatures`].
    data_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::DataSignature>>,
    /// [`CheckingContext::codata_signatures`].
    codata_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::CodataSignature>>,
    /// [`CheckingContext::accessibility`].
    accessibility: BTreeMap<ConstantIndex, crate::occurrence::Accessibility>,
    /// [`CheckingContext::admitted`].
    admitted: Maybe<ConstantIndex, admission::Absent>,
    /// [`CheckingContext::atoms`].
    atoms: Atoms,
    /// [`CheckingContext::definitions`].
    definitions: CodeDefinitions,
    /// [`CheckingContext::lifts`].
    lifts: BTreeMap<ValueId, Lift>,
    /// [`CheckingContext::funexts`].
    funexts: BTreeMap<ValueId, crate::funext::Funext>,
    /// [`CheckingContext::coercions`].
    coercions: BTreeMap<ValueId, crate::conversion::Coercion>,
    /// [`CheckingContext::equivalences`].
    equivalences: BTreeMap<ValueId, crate::equiv::Equivalence>,
    /// [`CheckingContext::flows`].
    flows: BTreeMap<ValueId, crate::flow::Statement>,
    /// [`CheckingContext::directed`].
    directed: BTreeMap<ValueId, crate::forward::Directed>,
    /// [`CheckingContext::motives`].
    motives: BTreeMap<ComputationId, ValueTypeId>,
    /// [`CheckingContext::payloads`].
    payloads: BTreeMap<ComputationId, ValueTypeId>,
    /// [`CheckingContext::handled`].
    handled: BTreeMap<ComputationId, crate::handler::Handled>,
    /// [`CheckingContext::rows`].
    rows: crate::program::Rows,
    /// [`CheckingContext::reflexivities`].
    reflexivities: BTreeMap<ValueId, crate::code::Reflexivity>,
    /// [`CheckingContext::nesting`].
    nesting: BTreeMap<ValueId, crate::nested::Nesting>,
    /// [`CheckingContext::crossings`].
    crossings: BTreeMap<ValueId, gandr_core_term::Crossing>,
    /// [`CheckingContext::updates`].
    updates: BTreeMap<ValueId, Vec<gandr_kernel_term::FieldLabel>>,
    /// [`CheckingContext::relating`].
    relating: BTreeMap<(ValueId, ValueId), crate::code::EndpointRelation>,
    /// [`CheckingContext::relations`].
    relations: BTreeMap<ConstantIndex, Vec<crate::code::EndpointRelation>>,
    /// The restatements the context records since its last take.
    restating: BTreeMap<TermNode, TermNode>,
    /// What reads each refinement since the last take back as written.
    readings: crate::solution::Written,
    /// [`CheckingContext::restatements`].
    restatements: BTreeMap<ConstantIndex, Vec<(TermNode, TermNode)>>,
    /// [`CheckingContext::laws`].
    laws: BTreeMap<ConstantIndex, Vec<ConstantIndex>>,
    /// [`CheckingContext::operation_rules`].
    operation_rules: BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>,
    /// [`CheckingContext::covers`].
    covers: BTreeMap<ConstantIndex, Vec<(ComputationId, gandr_kernel_term::cover::Cover)>>,
    /// [`CheckingContext::stage_signatures`].
    stage_signatures: BTreeMap<ConstantIndex, gandr_kernel_term::StageSignature>,
    /// [`CheckingContext::natives`].
    natives: BTreeMap<ValueId, ValueId>,
    /// [`CheckingContext::sealed`].
    sealed: BTreeMap<ConstantIndex, Sealed>,
    /// [`CheckingContext::builtins`].
    builtins: BTreeMap<gandr_kernel_term::Builtin, ConstantIndex>,
    /// [`CheckingContext::seals`].
    seals: SealTable,
    /// [`CheckingContext::budget`].
    budget: CheckBudget,
    /// The holes judged owed: the deferrals' set every later comparison
    /// reads.
    owed: BTreeSet<ConstantIndex>,
    /// The declarations judged suspended: the deferrals' other lasting set.
    suspended: BTreeSet<ConstantIndex>,
    /// [`CheckingContext::forming`].
    forming: Vec<(
        ConstantIndex,
        alloc::sync::Arc<gandr_core_term::DataSignature>,
    )>,
    /// [`CheckingContext::codata_forming`].
    codata_forming: Vec<(
        ConstantIndex,
        alloc::sync::Arc<gandr_core_term::CodataSignature>,
    )>,
    /// [`CheckingContext::mutual`].
    mutual: Maybe<crate::occurrence::Block, mutual::Absent>,
    /// [`CheckingContext::defining`].
    defining: Vec<(ConstantIndex, ValueId)>,
    /// [`CheckingContext::kin`].
    kin: Vec<crate::occurrence::Block>,
    /// [`CheckingContext::hindsight`].
    hindsight: Vec<(ConstantIndex, FormedValueType)>,
    /// [`CheckingContext::foreseen`].
    foreseen: Vec<ConstantIndex>,
    /// [`CheckingContext::grants`].
    grants: crate::capability::Grants,
    /// [`CheckingContext::typings`].
    typings: Option<crate::record::Kept>,
    /// [`CheckingContext::formations`].
    formations: Wanted,
    /// [`CheckingContext::stages`].
    stages: gandr_kernel_core::stage_order::StageOrder,
    /// [`CheckingContext::supplies`].
    supplies: Vec<gandr_core_term::staged::Supply>,
    /// [`CheckingContext::own`].
    own: (
        Maybe<ComputationId, own::Absent>,
        Maybe<(BinderDepth, ValueTypeId), own::Absent>,
    ),
    /// [`CheckingContext::result_stage`].
    result_stage: crate::recursion::ResultStage,
    /// [`CheckingContext::following`].
    following: BTreeMap<ConstantIndex, gandr_kernel_term::StagedPosition>,
    /// [`CheckingContext::worlds`].
    worlds: crate::worlds::Worlds,
    /// [`CheckingContext::pattern_holes`].
    pattern_holes: BTreeSet<HoleId>,
    /// [`CheckingContext::reducts`].
    reducts: Vec<gandr_kernel_term::ConstantIndex>,
    /// [`CheckingContext::readers`].
    readers: Vec<gandr_core_term::LiteralReader>,
}

impl<'arena> CheckingContext<'arena>
{
    /// A context over `arena` with no declaration admitted, judging under
    /// `budget`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the context holds no binder, no signature, no definition and
    ///   no lift, has admitted nothing, sealed nothing, forms no block and
    ///   bounds no held capability by a grant.
    /// - provides: the context every face and the declaration check run in.
    /// - panics: none.
    /// - intension: mints eight value-type nodes into `arena` — the unit type,
    ///   the integer atom, the string atom, the character atom and the four
    ///   integer width atoms — which every literal and unit rule then hands
    ///   out; the judgement mints the types it rewrites — a codomain shifted
    ///   under a binder, instantiated at an argument, or decoded from a quote —
    ///   into the same arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh context synthesises the three rigid atoms and
    ///   rejects a first undeclared constant; admission and budget cases
    ///   separate leaked prior state and a lost allowance. These cases do not
    ///   quantify over allocation limits.
    /// - witness: `context::tests::the_producer_declares_the_rigid_base_atoms`
    /// - witness: `context::tests::an_undeclared_type_name_is_refused_by_name`
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `gandr-core-checker::tests::elaboration::owed_conversion_suspends`
    #[spec(ensures: |ret| ret.budget.0 == budget.0
        && ret.signatures.is_empty() && ret.definitions.definitions().next().is_none()
        && ret.lifts.is_empty() && matches!(ret.admitted, Maybe::Absent(admission::Absent::Fresh))
        && matches!(ret.support, SupportLog::Off)
        && ret.deferrals.owed.is_empty() && ret.deferrals.suspended.is_empty()
        && ret.deferrals.residue == crate::elaboration::Residue::default()
        && ret.deferrals.collecting == crate::elaboration::Collecting::Off
        && matches!(ret.deferrals.emission, crate::elaboration::Emission::Off)
        && ret.grants == crate::capability::Grants::Unbounded
        && ret.depth(Zone::Intuitionistic) == BinderDepth::default()
        && ret.depth(Zone::Linear) == BinderDepth::default())]
    #[inline]
    #[must_use]
    pub fn new(
        arena: &'arena mut CoreArena,
        budget: CheckBudget,
    ) -> Self
    {
        let atoms = Atoms {
            unit: FormedValueType::derived(arena.value_type_unit()),
            integer: FormedValueType::derived(arena.value_type_base(BaseType::Integer)),
            string: FormedValueType::derived(arena.value_type_base(BaseType::String)),
            character: FormedValueType::derived(arena.value_type_base(BaseType::Character)),
            float64: FormedValueType::derived(arena.value_type_base(BaseType::Float64)),
            u32: FormedValueType::derived(
                arena.value_type_base(BaseType::Fixed(IntegerWidth::U32)),
            ),
            u64: FormedValueType::derived(
                arena.value_type_base(BaseType::Fixed(IntegerWidth::U64)),
            ),
            i32: FormedValueType::derived(
                arena.value_type_base(BaseType::Fixed(IntegerWidth::I32)),
            ),
            i64: FormedValueType::derived(
                arena.value_type_base(BaseType::Fixed(IntegerWidth::I64)),
            ),
        };
        Self {
            arena,
            binders: Context::new(),
            signatures: Vec::new(),
            data_signatures: BTreeMap::new(),
            codata_signatures: BTreeMap::new(),
            accessibility: BTreeMap::new(),
            admitted: Maybe::Absent(admission::Absent::Fresh),
            atoms,
            definitions: CodeDefinitions::new(),
            lifts: BTreeMap::new(),
            funexts: BTreeMap::new(),
            coercions: BTreeMap::new(),
            equivalences: BTreeMap::new(),
            flows: BTreeMap::new(),
            directed: BTreeMap::new(),
            motives: BTreeMap::new(),
            payloads: BTreeMap::new(),
            handled: BTreeMap::new(),
            rows: crate::program::Rows::default(),
            gained_rows: Vec::new(),
            reflexivities: BTreeMap::new(),
            natives: BTreeMap::new(),
            nesting: BTreeMap::new(),
            crossings: BTreeMap::new(),
            updates: BTreeMap::new(),
            relating: BTreeMap::new(),
            relations: BTreeMap::new(),
            restating: BTreeMap::new(),
            readings: crate::solution::Written::default(),
            restatements: BTreeMap::new(),
            laws: BTreeMap::new(),
            operation_rules: BTreeMap::new(),
            covers: BTreeMap::new(),
            stage_signatures: BTreeMap::new(),
            sealed: BTreeMap::new(),
            builtins: BTreeMap::new(),
            seals: SealTable::new(),
            budget,
            support: SupportLog::Off,
            deferrals: crate::elaboration::Deferrals::default(),
            forming: Vec::new(),
            codata_forming: Vec::new(),
            mutual: Maybe::Absent(mutual::Absent::Lone),
            defining: Vec::new(),
            kin: Vec::new(),
            hindsight: Vec::new(),
            foreseen: Vec::new(),
            grants: crate::capability::Grants::Unbounded,
            typings: None,
            formations: Wanted::All,
            stages: gandr_kernel_core::stage_order::StageOrder::default(),
            supplies: Vec::new(),
            own: (
                Maybe::Absent(own::Absent::Unopened),
                Maybe::Absent(own::Absent::Unopened),
            ),
            result_stage: crate::recursion::ResultStage::Declared,
            following: BTreeMap::new(),
            worlds: crate::worlds::Worlds::default(),
            pattern_holes: BTreeSet::new(),
            reducts: Vec::new(),
            readers: Vec::new(),
            tier: None,
            admitting: gandr_kernel_core::AdmissionPolicy::Derive,
            strata: crate::ua::Strata::default(),
            memo: MemoActivity::Active,
            #[cfg(feature = "instrument")]
            tally: crate::tally::MemoTally::default(),
            unfolded: BTreeMap::new(),
            #[cfg(feature = "instrument")]
            trace: None,
        }
    }

    /// The context's state, its arena released: what [`Self::resume`]
    /// continues from.
    ///
    /// # Specification
    /// - requires: no judgement is under way, no supported judgement is logging
    ///   and no term-producing run is recording: between two declarations of a
    ///   module run.
    /// - ensures: every table the context holds, copied; the owed and suspended
    ///   sets among its deferrals.
    /// - panics: none.
    /// - executable: none — the copy is the statement; the witness resumes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Checkpoint`].
    /// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
    #[inline]
    #[must_use]
    pub fn checkpoint(&self) -> Checkpoint
    {
        let Self {
            arena: _,
            ref binders,
            ref signatures,
            ref data_signatures,
            ref codata_signatures,
            ref accessibility,
            admitted,
            atoms,
            ref definitions,
            ref lifts,
            ref funexts,
            ref coercions,
            ref equivalences,
            ref flows,
            ref directed,
            ref motives,
            ref payloads,
            ref handled,
            ref rows,
            gained_rows: _,
            ref reflexivities,
            ref nesting,
            ref crossings,
            ref updates,
            ref relating,
            ref relations,
            ref restating,
            ref readings,
            ref restatements,
            ref laws,
            ref operation_rules,
            ref covers,
            ref stage_signatures,
            ref natives,
            ref sealed,
            ref builtins,
            ref seals,
            budget,
            support: _,
            ref deferrals,
            ref forming,
            ref codata_forming,
            mutual,
            ref defining,
            ref kin,
            ref hindsight,
            ref foreseen,
            ref grants,
            ref typings,
            ref formations,
            ref stages,
            ref supplies,
            own,
            result_stage,
            ref following,
            ref worlds,
            ref pattern_holes,
            ref reducts,
            ref readers,
            tier: _,
            admitting: _,
            strata: _,
            memo: _,
            #[cfg(feature = "instrument")]
                tally: _,
            unfolded: _,
            #[cfg(feature = "instrument")]
                trace: _,
        } = *self;
        Checkpoint {
            binders: binders.clone(),
            signatures: signatures.clone(),
            data_signatures: data_signatures.clone(),
            codata_signatures: codata_signatures.clone(),
            accessibility: accessibility.clone(),
            admitted,
            atoms,
            definitions: definitions.clone(),
            lifts: lifts.clone(),
            funexts: funexts.clone(),
            coercions: coercions.clone(),
            equivalences: equivalences.clone(),
            flows: flows.clone(),
            directed: directed.clone(),
            motives: motives.clone(),
            payloads: payloads.clone(),
            handled: handled.clone(),
            rows: rows.clone(),
            reflexivities: reflexivities.clone(),
            nesting: nesting.clone(),
            crossings: crossings.clone(),
            updates: updates.clone(),
            relating: relating.clone(),
            relations: relations.clone(),
            restating: restating.clone(),
            readings: readings.clone(),
            restatements: restatements.clone(),
            laws: laws.clone(),
            operation_rules: operation_rules.clone(),
            covers: covers.clone(),
            stage_signatures: stage_signatures.clone(),
            natives: natives.clone(),
            sealed: sealed.clone(),
            builtins: builtins.clone(),
            seals: seals.clone(),
            budget,
            owed: deferrals.owed.clone(),
            suspended: deferrals.suspended.clone(),
            forming: forming.clone(),
            codata_forming: codata_forming.clone(),
            mutual,
            defining: defining.clone(),
            kin: kin.clone(),
            hindsight: hindsight.clone(),
            foreseen: foreseen.clone(),
            grants: grants.clone(),
            typings: typings.clone(),
            formations: formations.clone(),
            stages: stages.clone(),
            supplies: supplies.clone(),
            own,
            result_stage,
            following: following.clone(),
            worlds: worlds.clone(),
            pattern_holes: pattern_holes.clone(),
            reducts: reducts.clone(),
            readers: readers.clone(),
        }
    }

    /// The context `checkpoint` was taken from, over `arena`.
    ///
    /// # Specification
    /// - requires: `arena` is the arena the checkpoint was taken over, or a
    ///   copy of it that more nodes were minted into after.
    /// - ensures: the context holds every table `checkpoint` holds, its
    ///   supported judgement idle and its term-producing run off, so it judges
    ///   what the context the checkpoint was taken from would have judged next.
    /// - panics: none.
    /// - executable: none — the clauses compare two contexts over one arena;
    ///   the witness compares the reports two runs make.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Checkpoint`].
    /// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
    #[inline]
    #[must_use]
    pub fn resume(
        arena: &'arena mut CoreArena,
        checkpoint: Checkpoint,
    ) -> Self
    {
        let Checkpoint {
            binders,
            signatures,
            data_signatures,
            codata_signatures,
            accessibility,
            admitted,
            atoms,
            definitions,
            lifts,
            funexts,
            coercions,
            equivalences,
            flows,
            directed,
            motives,
            payloads,
            handled,
            rows,
            reflexivities,
            nesting,
            crossings,
            updates,
            relating,
            relations,
            restating,
            readings,
            restatements,
            laws,
            operation_rules,
            covers,
            stage_signatures,
            natives,
            sealed,
            builtins,
            seals,
            budget,
            owed,
            suspended,
            forming,
            codata_forming,
            mutual,
            defining,
            kin,
            hindsight,
            foreseen,
            grants,
            typings,
            formations,
            stages,
            supplies,
            own,
            result_stage,
            following,
            worlds,
            pattern_holes,
            reducts,
            readers,
        } = checkpoint;
        Self {
            arena,
            binders,
            signatures,
            data_signatures,
            codata_signatures,
            accessibility,
            admitted,
            atoms,
            definitions,
            lifts,
            funexts,
            coercions,
            equivalences,
            flows,
            directed,
            motives,
            payloads,
            handled,
            rows,
            gained_rows: Vec::new(),
            reflexivities,
            nesting,
            crossings,
            updates,
            relating,
            relations,
            restating,
            readings,
            restatements,
            laws,
            operation_rules,
            covers,
            stage_signatures,
            natives,
            sealed,
            builtins,
            seals,
            budget,
            support: SupportLog::Off,
            deferrals: crate::elaboration::Deferrals {
                owed,
                suspended,
                ..crate::elaboration::Deferrals::default()
            },
            forming,
            codata_forming,
            mutual,
            defining,
            kin,
            hindsight,
            foreseen,
            grants,
            typings,
            formations,
            stages,
            supplies,
            own,
            result_stage,
            following,
            worlds,
            pattern_holes,
            reducts,
            readers,
            tier: None,
            admitting: gandr_kernel_core::AdmissionPolicy::Derive,
            strata: crate::ua::Strata::default(),
            memo: MemoActivity::Active,
            #[cfg(feature = "instrument")]
            tally: crate::tally::MemoTally::default(),
            unfolded: BTreeMap::new(),
            #[cfg(feature = "instrument")]
            trace: None,
        }
    }

    /// Decide each endpoint pair the `here` rule meets on `tier` before the
    /// machine, a closed pair it meets crossing as `policy` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later endpoint pair is offered to `tier` first; a
    ///   context holds one tier and one policy, the last handed.
    /// - provides: the driver's hand-in of its tier, as a staging check is
    ///   handed its [`gandr_core_fork::Fork`].
    /// - panics: none.
    /// - executable: none — the tier is a trait object no predicate compares.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a context handed a tier that meets every pair records
    ///   `Evaluate` for a closed pair and for an open one; a context handed
    ///   none records the machine's dialogue for both. Under the native
    ///   conversion policy the closed pair records `Admitted` and the open one
    ///   `Evaluate`.
    /// - witness: `judgement::tests::a_pair_the_tier_meets_carries_its_evaluation_3557`
    /// - witness: `judgement::tests::a_closed_pair_the_tier_meets_is_admitted_under_the_policy_3558`
    #[inline]
    pub fn decide_endpoints_on(
        &mut self,
        tier: alloc::boxed::Box<dyn crate::tier::EndpointTier>,
        policy: gandr_kernel_core::AdmissionPolicy,
    )
    {
        self.tier = Some(tier);
        self.admitting = policy;
    }

    /// The policy a closed pair the tier meets crosses under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admitting(&self) -> gandr_kernel_core::AdmissionPolicy
    {
        self.admitting
    }

    /// Keep a goal memo in each later run of the machine as `activity` says:
    /// [`MemoActivity::Active`] unless a caller asks for runs without one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each run of the machine started later answers its repeated
    ///   goals from a memo exactly when `activity` is [`MemoActivity::Active`].
    /// - panics: none.
    /// - executable: none — the activity is read where each run starts, which
    ///   no predicate over this call observes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run without the memo spends the unshared work of a
    ///   shared pair, and the same run with it spends the shared work.
    /// - witness: `judgement::memo::tests::a_shared_pair_spends_a_step_for_each_distinct_goal`
    #[inline]
    pub const fn memoise_goals(
        &mut self,
        activity: MemoActivity,
    )
    {
        self.memo = activity;
    }

    /// Whether each run of the machine keeps a goal memo.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn goal_memo(&self) -> MemoActivity
    {
        self.memo
    }

    /// The goal memo's hits and misses over every run in this context so far.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    #[must_use]
    pub const fn tally(&self) -> crate::tally::MemoTally
    {
        self.tally
    }

    /// The tally each run of the machine counts its memo's consults into.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    pub(crate) const fn tally_mut(&mut self) -> &mut crate::tally::MemoTally
    {
        &mut self.tally
    }

    /// Write each step of the machine's runs into `buffer`, until the buffer
    /// is taken back.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    pub fn trace_into(
        &mut self,
        buffer: crate::trace::StepBuffer,
    )
    {
        self.trace = Some(buffer);
    }

    /// The buffer the machine's runs write their steps into, or why the
    /// context holds none.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    pub const fn trace(
        &self
    ) -> quenchant_shape::shape::Maybe<&crate::trace::StepBuffer, crate::trace::untraced::Absent>
    {
        match self.trace {
            Some(ref buffer) => quenchant_shape::shape::Maybe::Present(buffer),
            None => quenchant_shape::shape::Maybe::Absent(crate::trace::untraced::Absent::Unlent),
        }
    }

    /// Forget the steps the buffer holds, and keep the buffer.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    pub fn retrace(&mut self)
    {
        if let Some(ref mut buffer) = self.trace {
            buffer.clear();
        }
    }

    /// Take the buffer back: the machine's runs then write no step.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    pub fn take_trace(
        &mut self
    ) -> quenchant_shape::shape::Maybe<crate::trace::StepBuffer, crate::trace::untraced::Absent>
    {
        self.trace.take().map_or(
            quenchant_shape::shape::Maybe::Absent(crate::trace::untraced::Absent::Unlent),
            quenchant_shape::shape::Maybe::Present,
        )
    }

    /// Write the step that `step` makes of the clock's reading, when a
    /// tracer lent a buffer.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    pub(crate) fn traced<Make>(
        &mut self,
        step: Make,
    ) where
        Make: FnOnce(gandr_core_fork::activity::Nanos) -> crate::trace::Step,
    {
        if let Some(ref mut buffer) = self.trace {
            buffer.write(step);
        }
    }

    /// Recall the strata `ua` statements name from `store`, and keep there
    /// what this context certifies.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later stratum the context does not hold is asked of
    ///   `store` first; a context holds one store, the last handed.
    /// - provides: the driver's hand-in of its store, as it hands its tier.
    /// - panics: none.
    /// - executable: none — the store is a trait object no predicate compares.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a context handed a store holding a stratum's image
    ///   replays it and certifies nothing, and one holding a damaged image
    ///   refuses it by name and certifies afresh.
    /// - witness: `tests::ua::a_stored_stratum_replays_and_a_damaged_one_is_certified_afresh_4034`
    #[inline]
    pub fn keep_strata_in(
        &mut self,
        store: alloc::sync::Arc<dyn crate::ua::StratumStore>,
    )
    {
        self.strata.keep_in(store);
    }

    /// Level two at `at` over the wreath of the chains over themselves, from
    /// the strata this context holds: recalled from its store and replayed,
    /// or certified and kept.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`crate::ua::Strata::level_two`].
    /// - fails: as [`crate::ua::Strata::level_two`].
    /// - panics: none.
    /// - executable: none — the stratum source's own contract.
    ///
    /// # Errors
    /// [`crate::ua::StratumDefect`] as [`crate::ua::Strata::level_two`]
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a context handed a store holding level two's image
    ///   replays it and certifies nothing, and one holding a damaged image
    ///   refuses it by name and certifies afresh.
    /// - witness: `ua::tests::level_two_is_kept_recalled_and_refused_by_the_store_4123`
    #[inline]
    pub fn level_two(
        &mut self,
        at: crate::ua::StratumAt,
    ) -> Result<alloc::sync::Arc<gandr_theory_sites::WreathStratum>, crate::ua::StratumDefect>
    {
        self.strata.level_two(at)
    }

    /// The catalogues and strata the context holds, and its store.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn strata_mut(&mut self) -> &mut crate::ua::Strata
    {
        &mut self.strata
    }

    /// Offer `point` and `endpoint` to the context's tier.
    ///
    /// # Specification
    /// - requires: both values live in the context's arena.
    /// - ensures: [`crate::tier::Meeting::Met`] exactly when the context holds
    ///   a tier and the tier meets the pair over the definitions admitted so
    ///   far; [`crate::tier::Meeting::Unmet`] otherwise.
    /// - panics: none.
    /// - executable: none — the tier's answer is its implementation's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide_endpoints_on`].
    /// - witness: `judgement::tests::a_pair_the_tier_meets_carries_its_evaluation_3557`
    pub(crate) fn meet_endpoints(
        &mut self,
        point: ValueId,
        endpoint: ValueId,
    ) -> crate::tier::Meeting
    {
        let Some(tier) = self.tier.as_deref_mut()
        else {
            return crate::tier::Meeting::Unmet;
        };
        let arena: &CoreArena = self.arena;
        tier.meet(arena, &self.definitions, (point, endpoint))
    }

    /// The one decision a pair the tier met crosses with: `Admitted` under
    /// the native conversion policy when both sides are closed, and
    /// `Evaluate` otherwise.
    ///
    /// # Specification
    /// - requires: both values live in the context's arena.
    /// - ensures: `Admitted` exactly when the policy is
    ///   [`gandr_kernel_core::AdmissionPolicy::NativeConversion`] and neither
    ///   value selects a variable in either zone; `Evaluate` otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide_endpoints_on`].
    /// - witness: `judgement::tests::a_closed_pair_the_tier_meets_is_admitted_under_the_policy_3558`
    #[spec(ensures: |ret| (ret == gandr_kernel_conversion_trace::ConversionDecision::Admitted)
        == (self.admitting == gandr_kernel_core::AdmissionPolicy::NativeConversion
            && [point, endpoint].into_iter().all(|side| self.closure(side) == Closure::Closed)))]
    pub(crate) fn met_decision(
        &self,
        point: ValueId,
        endpoint: ValueId,
    ) -> gandr_kernel_conversion_trace::ConversionDecision<gandr_core_nbe::TraceNode>
    {
        let taken = self.admitting == gandr_kernel_core::AdmissionPolicy::NativeConversion
            && [point, endpoint]
                .into_iter()
                .all(|side| self.closure(side) == Closure::Closed);
        if taken {
            gandr_kernel_conversion_trace::ConversionDecision::Admitted
        }
        else {
            gandr_kernel_conversion_trace::ConversionDecision::Evaluate
        }
    }

    /// The pair the tier met, with what the machine reads to answer it should
    /// the kernel's own evaluation leave it undecided. An open pair reads the
    /// binders whose calls return, `known` once read. A closed pair reads none.
    ///
    /// # Specification
    /// - requires: `point` and `endpoint` stand under the context's binders.
    /// - ensures: the pair of `point` and `endpoint`; with no binder when both
    ///   are closed, and otherwise with [`crate::divergence::returning`]'s
    ///   answer, which `known` keeps, or with no binder when that read fails.
    /// - provides: the second certificate's input, recorded at the cost of the
    ///   binders' read alone and only for an open pair.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::code::MetPair::certified`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_undecided_pair_crosses_with_its_second_certificate_3557`
    #[spec(ensures: |ret| ret.point() == point)]
    pub(crate) fn met_pair(
        &mut self,
        point: ValueId,
        endpoint: ValueId,
        known: &mut Option<Vec<gandr_kernel_term::DeBruijnIndex>>,
    ) -> crate::code::MetPair
    {
        let closed = [point, endpoint]
            .into_iter()
            .all(|side| self.closure(side) == Closure::Closed);
        if closed {
            return crate::code::MetPair::new(point, endpoint, Vec::new());
        }
        let returning = match *known {
            Some(ref read) => read.clone(),
            None => crate::divergence::returning(self).map_or_else(
                |_unread| Vec::new(),
                |read| {
                    *known = Some(read.clone());
                    read
                },
            ),
        };
        crate::code::MetPair::new(point, endpoint, returning)
    }

    /// Whether `value` selects no variable in either zone.
    ///
    /// # Specification
    /// trivial.
    fn closure(
        &self,
        value: ValueId,
    ) -> Closure
    {
        let closed = self.arena.value_support(value).is_some_and(|support| {
            [Zone::Intuitionistic, Zone::Linear]
                .into_iter()
                .all(|zone| support.indices(zone).next().is_none())
        });
        if closed {
            Closure::Closed
        }
        else {
            Closure::Open
        }
    }

    /// Keep `typing`, when a typed run is recording: the one point every
    /// finished term judgement passes, whatever former judged it and in
    /// whichever run, so a former that judges its sub-terms records them
    /// without knowing the record exists. A typing inside a refined term is
    /// kept as its written term's, read in the written context
    /// ([`crate::solution::Written::read_back`]).
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a recording log's typings grow by `typing` read back at their
    ///   end; nothing changes otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed run's term and a strict judgement nested in a
    ///   typed run separate recording from not. A refined arm's written terms
    ///   read at the arm's own depth.
    /// - witness: `judgement::elaboration::tests::a_typed_run_keeps_the_type_of_every_term_it_judged`
    /// - witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.typings.len()),
        ensures: self.typings.as_ref().map(|log| log.typings.len()) == before.map(|count| count.saturating_add(1)),
    )]
    pub(crate) fn keep_typing(
        &mut self,
        typing: crate::record::Typing,
    )
    {
        if let Some(ref mut log) = self.typings {
            log.typings
                .push(self.readings.read_back(self.arena, typing));
        }
    }

    /// Keep the session type an action's endpoint stood at, when a typed run
    /// is recording: `standing`'s term is the action, its type the endpoint's
    /// session type read where the action stands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a recording log's endpoints grow by `standing` at their end;
    ///   nothing changes otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each action of the seat exchange keeps its endpoint's
    ///   state, which advances along the protocol.
    /// - witness: `tests::judgement::session::a_typed_run_keeps_each_endpoint_s_state`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.endpoints.len()),
        ensures: self.typings.as_ref().map(|log| log.endpoints.len()) == before.map(|count| count.saturating_add(1)),
    )]
    pub(crate) fn keep_endpoint(
        &mut self,
        standing: crate::record::Typing,
    )
    {
        if let Some(ref mut log) = self.typings {
            log.endpoints.push(standing);
        }
    }

    /// Keep a move of the world register, when a typed run is recording: a
    /// migration's spent capability and its return.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a recording log's moves grow by `moved` at their end; nothing
    ///   changes otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed run of a migration keeps its push, with the
    ///   capability available before and spent after, and its return.
    /// - witness: `worlds::tests::a_migration_consumes_its_capability_visibly`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.moves.len()),
        ensures: self.typings.as_ref().map(|log| log.moves.len()) == before.map(|count| count.saturating_add(1)),
    )]
    pub(crate) fn keep_move(
        &mut self,
        moved: crate::worlds::WorldMove,
    )
    {
        if let Some(ref mut log) = self.typings {
            log.moves.push(moved);
        }
    }

    /// `relocated` settled to plain nodes. While a typed run records, each
    /// node the settling mints is kept beside the node it copies, so a reader
    /// of the record names the copy as its source.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `relocated` settled, as [`Relocated::settle`] settles it; a
    ///   recording log's copies grow at their end only.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a variable whose type is read past binders keeps each
    ///   node its type was copied to beside the node it copies.
    /// - witness: `module::tests::a_variable_s_type_keeps_the_copies_its_reading_mints`
    ///
    /// [`Relocated::settle`]: gandr_core_term::Relocated::settle
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.copies.len()),
        ensures: self.typings.as_ref().map(|log| log.copies.len()) >= before,
    )]
    pub(crate) fn settle_value_type(
        &mut self,
        relocated: gandr_core_term::Relocated<ValueTypeId>,
    ) -> ValueTypeId
    {
        match self.typings {
            Some(ref mut log) => relocated.settle_traced(self.arena, &mut log.copies),
            None => relocated.settle(self.arena),
        }
    }

    /// `relocated` settled to plain nodes, each node it mints kept as
    /// [`Self::settle_value_type`] keeps it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `relocated` settled, as [`Relocated::settle`] settles it; a
    ///   recording log's copies grow at their end only.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda checked against a non-dependent arrow reads
    ///   the arrow's codomain past its binder, a copy kept beside it.
    /// - witness: `module::tests::a_variable_s_type_keeps_the_copies_its_reading_mints`
    ///
    /// [`Relocated::settle`]: gandr_core_term::Relocated::settle
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.copies.len()),
        ensures: self.typings.as_ref().map(|log| log.copies.len()) >= before,
    )]
    pub(crate) fn settle_comp_type(
        &mut self,
        relocated: gandr_core_term::Relocated<CompTypeId>,
    ) -> CompTypeId
    {
        match self.typings {
            Some(ref mut log) => relocated.settle_traced(self.arena, &mut log.copies),
            None => relocated.settle(self.arena),
        }
    }

    /// `ty` read `amount` binders deeper, each node the shift mints kept as
    /// [`Self::settle_value_type`] keeps it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`gandr_core_term::shift_value_type`], settled; a
    ///   recording log's copies grow at their end only.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the components of a pair a split opens, each read
    ///   past the components before it, keep their labels in the copies.
    /// - witness: `module::tests::a_variable_s_type_keeps_the_copies_its_reading_mints`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.copies.len()),
        ensures: self.typings.as_ref().map(|log| log.copies.len()) >= before,
    )]
    pub(crate) fn shift_value_type(
        &mut self,
        ty: ValueTypeId,
        amount: gandr_core_term::Binders,
    ) -> ValueTypeId
    {
        let relocated = gandr_core_term::shift_value_type(self.arena, ty, amount);
        self.settle_value_type(relocated)
    }

    /// `ty` read `amount` binders deeper, each node the shift mints kept as
    /// [`Self::settle_value_type`] keeps it: the type a body is checked
    /// against past the binders its form opens.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`gandr_core_term::shift_comp_type`], settled; a recording
    ///   log's copies grow at their end only.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match arm checked against a dependent record read
    ///   past the arm's fields keeps the record's labels in the copy.
    /// - witness: `module::tests::a_variable_s_type_keeps_the_copies_its_reading_mints`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.copies.len()),
        ensures: self.typings.as_ref().map(|log| log.copies.len()) >= before,
    )]
    pub(crate) fn shift_comp_type(
        &mut self,
        ty: CompTypeId,
        amount: gandr_core_term::Binders,
    ) -> CompTypeId
    {
        let relocated = gandr_core_term::shift_comp_type(self.arena, ty, amount);
        self.settle_comp_type(relocated)
    }

    /// The binder of the type `subject` instantiated at `argument`, each node
    /// it rewrites kept as [`Self::settle_value_type`] keeps it.
    ///
    /// # Specification
    /// - requires: `subject` is scoped beneath one binder of the context
    ///   `argument` stands in.
    /// - ensures: as [`gandr_core_term::instantiate_value_type`]; a recording
    ///   log's copies grow at their end only.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent record's second component, projected,
    ///   reads its type at the first, a copy kept beside it.
    /// - witness: `module::tests::a_variable_s_type_keeps_the_copies_its_reading_mints`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.copies.len()),
        ensures: self.typings.as_ref().map(|log| log.copies.len()) >= before,
    )]
    pub(crate) fn instantiate_value_type(
        &mut self,
        subject: ValueTypeId,
        argument: gandr_core_term::ValueId,
    ) -> ValueTypeId
    {
        match self.typings {
            Some(ref mut log) => gandr_core_term::instantiate_value_type_traced(
                self.arena,
                subject,
                argument,
                &mut log.copies,
            ),
            None => gandr_core_term::instantiate_value_type(self.arena, subject, argument),
        }
    }

    /// Keep the formation of `ty`, when a typed run is recording, at the
    /// level it forms at under the binders it was formed under: the one point
    /// every finished formation passes, as [`Self::keep_typing`] is for
    /// terms.
    ///
    /// # Specification
    /// - requires: `ty` was formed under the context's binders.
    /// - ensures: a recording log's formations grow by `ty` at its level when
    ///   the context keeps `ty`'s formations ([`Self::keep_formations`]) and
    ///   the level reads, and the context marks a wanted type's first formation
    ///   kept; nothing changes otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a transport's motive, formed under its binder, and a
    ///   written signature separate an open type's level from a closed one's.
    /// - witness: `module::tests::a_typed_module_keeps_the_terms_its_signature_judges`
    #[spec(
        captures: before = self.typings.as_ref().map(|log| log.formed.len()),
        ensures: self.typings.as_ref().map(|log| log.formed.len()).is_none_or(|count|
            before.is_some_and(|prior| count == prior || count == prior.saturating_add(1))),
    )]
    pub(crate) fn keep_formed(
        &mut self,
        ty: crate::refusal::TypeNode,
    )
    {
        if self.typings.is_none() {
            return;
        }
        let wanted = match self.formations {
            Wanted::All => None,
            Wanted::Firsts(ref types) => match types.binary_search_by_key(&ty, |&(held, _)| held) {
                Ok(at)
                    if types
                        .get(at)
                        .is_some_and(|&(_, first)| first == First::Pending) =>
                {
                    Some(at)
                },
                Ok(_) | Err(_) => return,
            },
        };
        let Ok(level) = crate::formation::level_of(self, ty)
        else {
            return;
        };
        if let Wanted::Firsts(ref mut types) = self.formations
            && let Some(&mut (_, ref mut first)) = wanted.and_then(|at| types.get_mut(at))
        {
            *first = First::Kept;
        }
        if let Some(ref mut log) = self.typings {
            log.formed.push(crate::record::Formed { ty, level });
        }
    }

    /// Keep only `formations` from here on: a typed run's log keeps a
    /// formation, with its level, only where `formations` asks for it.
    ///
    /// # Specification
    /// - requires: a [`Formations::Firsts`] list is ascending and unique.
    /// - ensures: the context keeps every formation for [`Formations::All`],
    ///   and for [`Formations::Firsts`] the first formation of each listed
    ///   type, none kept yet.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed module asked for its signature's type alone
    ///   keeps that formation once and none of the others it formed, though a
    ///   second run forms it again.
    /// - witness: `module::tests::a_typed_module_keeps_the_terms_its_signature_judges`
    #[spec(
        requires: match formations { Formations::All => true, Formations::Firsts(ref types) => types.is_sorted_by(|left, right| left < right) },
        captures: expected = formations.clone(),
        ensures: match (&self.formations, &expected) {
            | (&Wanted::All, &Formations::All) => true,
            | (&Wanted::Firsts(ref held), &Formations::Firsts(ref types)) => held.len() == types.len()
                && held.iter().zip(types).all(|(&(ty, first), &listed)| ty == listed && first == First::Pending),
            | (&Wanted::All, &Formations::Firsts(_)) | (&Wanted::Firsts(_), &Formations::All) => false,
        },
    )]
    #[inline]
    pub fn keep_formations(
        &mut self,
        formations: Formations,
    )
    {
        self.formations = match formations {
            Formations::All => Wanted::All,
            Formations::Firsts(types) => {
                Wanted::Firsts(types.into_iter().map(|ty| (ty, First::Pending)).collect())
            },
        };
    }

    /// Whether a typed run is recording.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn recording(&self) -> Recording
    {
        if self.typings.is_some() {
            Recording::On
        }
        else {
            Recording::Off
        }
    }

    /// Whether a typed run is recording a formation of `ty`: it records and
    /// keeps every formation, or `ty` is a wanted type not yet formed.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn forming(
        &self,
        ty: crate::refusal::TypeNode,
    ) -> Recording
    {
        let forming = self.typings.is_some()
            && match self.formations {
                Wanted::All => true,
                Wanted::Firsts(ref types) => types
                    .binary_search_by_key(&ty, |&(held, _)| held)
                    .ok()
                    .and_then(|at| types.get(at))
                    .is_some_and(|&(_, first)| first == First::Pending),
            };
        if forming {
            Recording::On
        }
        else {
            Recording::Off
        }
    }

    /// Record every term judgement and type formation from here on, until
    /// [`Self::finish_typings`]; the log a recording already under way kept is
    /// set aside and handed back.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the context records into an empty log; the result is the log
    ///   it recorded into before, or `None` when it recorded nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed run inside a declaration whose signature was
    ///   recorded keeps the two logs apart and joins them in order.
    /// - witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`
    #[spec(ensures: self.typings.as_ref().is_some_and(|log| log.typings.is_empty() && log.formed.is_empty()))]
    pub(crate) fn start_typings(&mut self) -> Option<crate::record::Kept>
    {
        self.typings.replace(crate::record::Kept::default())
    }

    /// Stop recording: the log kept since [`Self::start_typings`], the
    /// recording `outer` was restored to.
    ///
    /// # Specification
    /// - requires: `outer` is what the matching [`Self::start_typings`]
    ///   returned.
    /// - ensures: the context records into `outer` again; the result is
    ///   everything kept since the matching start, in the order kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::start_typings`].
    /// - witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`
    #[spec(
        captures: restored = outer.is_some(),
        ensures: self.typings.is_some() == restored,
    )]
    pub(crate) fn finish_typings(
        &mut self,
        outer: Option<crate::record::Kept>,
    ) -> crate::record::Kept
    {
        core::mem::replace(&mut self.typings, outer).unwrap_or_default()
    }

    /// Bound the module's held capabilities by `grants`: the authority the
    /// host grants at the checker's entry.
    ///
    /// # Specification
    /// - ensures: every later declaration of a held capability is judged
    ///   against `grants`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held capability within the grant is owed, one
    ///   beyond it is refused by name, and with no grant both are owed.
    /// - witness: `capability::tests::a_held_capability_enters_only_within_the_grant`
    #[spec(captures: expected = grants.clone(), ensures: self.grants == expected)]
    #[inline]
    pub fn grant(
        &mut self,
        grants: crate::capability::Grants,
    )
    {
        self.grants = grants;
    }

    /// Read `holes` as the holes the module's matches were written with in
    /// place of a pattern, so a match tree whose leaf is one of them is
    /// refused rather than checked.
    ///
    /// # Specification
    /// - ensures: every later judgement of a hole among `holes` is refused as
    ///   [`CheckRefusal::UndecidedCoverage`]; a hole outside them still checks
    ///   against any type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same hole node is refused once its id is a
    ///   pattern hole and checks while it is not.
    /// - witness: `judgement::tests::a_pattern_hole_at_a_leaf_leaves_the_match_undecided`
    #[spec(ensures: holes.iter().all(|hole| self.pattern_holes.contains(hole)))]
    #[inline]
    pub fn keep_pattern_holes(
        &mut self,
        holes: &[HoleId],
    )
    {
        self.pattern_holes.extend(holes.iter().copied());
    }

    /// Read `reducts` as maps between models the module mints, so the value
    /// bridge crosses by one where a model of a theory stands at a model of a
    /// theory it includes, or a model with manifest sorts at its theory's
    /// models.
    ///
    /// # Specification
    /// - ensures: every later value bridge between two types apart crosses by
    ///   the first of the kept maps, in position order, whose signature carries
    ///   the one to the other at the carriers it solves, and records it at the
    ///   value it crossed; each map is kept once, however often it is read.
    /// - panics: none.
    /// - executable: none — the kept reducts are the receiver's own, which a
    ///   predicate would search again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a monoid's model passed where a semigroup's is asked
    ///   checks once the reduct is kept and is refused while it is not.
    /// - witness: `tests::module::a_model_crosses_to_an_included_theory_s_by_its_reduct`
    #[inline]
    pub fn keep_reducts(
        &mut self,
        reducts: &[gandr_kernel_term::ConstantIndex],
    )
    {
        self.reducts.extend(reducts.iter().copied());
        self.reducts.sort_unstable();
        self.reducts.dedup();
    }

    /// The reducts the module mints, in position order, as
    /// [`CheckingContext::keep_reducts`] kept them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn reducts(&self) -> &[gandr_kernel_term::ConstantIndex]
    {
        &self.reducts
    }

    /// Read `readers` as the literal readers the module lends, so the value
    /// bridge crosses an integer literal checked at a type apart from
    /// `Integer` by the one of its kind whose carrier converts with that type.
    ///
    /// # Specification
    /// - ensures: every later value bridge from `Integer` at an integer literal
    ///   to a type apart from it crosses by the one kept reader of the
    ///   literal's kind whose result converts with that type, and records it at
    ///   the literal; each reader is kept once, in position order, however
    ///   often it is read.
    /// - panics: none.
    /// - executable: none — the kept readers are the receiver's own, which a
    ///   predicate would search again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a literal checked at a parity crosses by the parity's
    ///   reader once it is kept, and is refused while it is not.
    /// - witness: `tests::module::a_natural_literal_crosses_by_the_reader_of_its_type_4528`
    /// - witness: `tests::module::a_negative_literal_crosses_by_from_neg_at_its_magnitude_4732`
    #[inline]
    pub fn keep_readers(
        &mut self,
        readers: &[gandr_core_term::LiteralReader],
    )
    {
        self.readers.extend(readers.iter().copied());
        self.readers.sort_unstable();
        self.readers.dedup();
    }

    /// The literal readers the module lends, in position order, as
    /// [`CheckingContext::keep_readers`] kept them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn readers(&self) -> &[gandr_core_term::LiteralReader]
    {
        &self.readers
    }

    /// `hole` when it was written in place of a pattern.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn pattern_hole(
        &self,
        hole: HoleId,
    ) -> Maybe<HoleId, pattern_hole::Absent>
    {
        if self.pattern_holes.contains(&hole) {
            Maybe::Present(hole)
        }
        else {
            Maybe::Absent(pattern_hole::Absent::Term)
        }
    }

    /// The authority the host grants the module's held capabilities.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn grants(&self) -> &crate::capability::Grants
    {
        &self.grants
    }

    /// Native signatures already admitted in this context.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn data_signatures(
        &self
    ) -> &BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::DataSignature>>
    {
        &self.data_signatures
    }

    /// Retain a signature after its formation judgment has succeeded, and
    /// read the terms of a presented one by their normal forms from then on.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn record_data(
        &mut self,
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::DataSignature>,
    )
    {
        self.definitions.present(constant, &signature);
        let _previous = self.data_signatures.insert(constant, signature);
    }

    /// What the occurrence walk of every data declaration formed so far
    /// decided: the variance a nested occurrence is read through.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn accessibility(
        &self
    ) -> &BTreeMap<ConstantIndex, crate::occurrence::Accessibility>
    {
        &self.accessibility
    }

    /// Retain the accessibility the walk of the data declaration at
    /// `constant` decided, once its signature has formed.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn record_accessibility(
        &mut self,
        constant: ConstantIndex,
        accessibility: crate::occurrence::Accessibility,
    )
    {
        let _previous = self.accessibility.insert(constant, accessibility);
    }

    /// How the occurrences of the family at `constant` stand: stratified for
    /// a family whose walk is not held, the reading a case owes no less.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn stratification(
        &self,
        constant: ConstantIndex,
    ) -> crate::occurrence::Stratification
    {
        self.accessibility.get(&constant).map_or(
            crate::occurrence::Stratification::Stratified,
            crate::occurrence::Accessibility::stratification,
        )
    }

    /// Re-form and adopt a nominal signature without a value unfolding.
    ///
    /// # Specification
    /// - requires: identifiers are read in this context; no cached formation
    ///   claim is trusted across arenas.
    /// - ensures: the fresh position has a nominal signature, not a value body.
    /// - fails: signature formation or admission out of source order.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a formation refusal or the ordinary admission-order refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reusing a nominal signature must retain its full
    ///   field table so constructor checks remain identical to a fresh
    ///   judgment.
    /// - witness: `tests::native_formers::native_signature_support_and_adoption`
    #[spec(ensures: |ret| ret.is_err() || self.data_signatures.contains_key(&constant))]
    #[inline]
    pub fn adopt_data(
        &mut self,
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::DataSignature>,
    ) -> Result<(), CheckRefusal>
    {
        crate::former::form_signature(self, constant, &signature)?;
        self.admit(constant)?;
        self.record_data(constant, signature);
        Ok(())
    }

    /// Codata signatures already admitted in this context.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn codata_signatures(
        &self
    ) -> &BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::CodataSignature>>
    {
        &self.codata_signatures
    }

    /// Retain a codata signature after its formation has succeeded.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn record_codata(
        &mut self,
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::CodataSignature>,
    )
    {
        let _previous = self.codata_signatures.insert(constant, signature);
    }

    /// Re-form and adopt a codata signature.
    ///
    /// # Specification
    /// - requires: identifiers are read in this context.
    /// - ensures: the fresh position has a codata signature.
    /// - fails: signature formation or admission out of source order.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a formation refusal or the ordinary admission-order refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stream adopted into a fresh context reads through
    ///   its observations as it did where it was first admitted.
    /// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
    #[spec(ensures: |ret| ret.is_err() || self.codata_signatures.contains_key(&constant))]
    #[inline]
    pub fn adopt_codata(
        &mut self,
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::CodataSignature>,
    ) -> Result<(), CheckRefusal>
    {
        crate::codata::form_signature(self, constant, &signature)?;
        self.admit(constant)?;
        self.record_codata(constant, signature);
        Ok(())
    }

    /// Open the codata declaration at `position` for its observations'
    /// formation: until it closes, [`Self::codata_in_scope`] answers
    /// `signature` at `position`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn open_codata(
        &mut self,
        position: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::CodataSignature>,
    )
    {
        self.codata_forming.clear();
        self.codata_forming.push((position, signature));
    }

    /// Close the codata declaration whose observations were forming.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn close_codata(&mut self)
    {
        self.codata_forming.clear();
    }

    /// Whether `constant` is the codata declaration whose observations are
    /// forming.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn codata_forming_at(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<alloc::sync::Arc<gandr_core_term::CodataSignature>, data_scope::Absent>
    {
        self.codata_forming
            .iter()
            .find_map(|&(held, ref signature)| (held == constant).then_some(signature))
            .map_or(Maybe::Absent(data_scope::Absent::Unknown), |signature| {
                Maybe::Present(alloc::sync::Arc::clone(signature))
            })
    }

    /// The codata signature in scope at `constant`, without logging: the
    /// forming declaration's when it is that position's, else the admitted
    /// one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn codata_in_scope(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<alloc::sync::Arc<gandr_core_term::CodataSignature>, data_scope::Absent>
    {
        if let Maybe::Present(signature) = self.codata_forming_at(constant) {
            return Maybe::Present(signature);
        }
        self.codata_signatures
            .get(&constant)
            .map_or(Maybe::Absent(data_scope::Absent::Unknown), |signature| {
                Maybe::Present(alloc::sync::Arc::clone(signature))
            })
    }

    /// Read and log an admitted codata signature, including its absence.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the exact stored signature, and a supported judgment logs the
    ///   identity and the signature read.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a judgement reading a stream through its observations
    ///   logs the stream's signature once.
    /// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
    #[spec(ensures: |ret| match self.support {
SupportLog::Off => true,
SupportLog::Recording { ref codata, .. } => codata.last().is_some_and(|entry| entry.constant() == constant && entry.signature() == match ret { Maybe::Present(ref held) => Some(&**held), Maybe::Absent(_) => None }),
})]
    pub(crate) fn consult_codata(
        &mut self,
        constant: ConstantIndex,
    ) -> Maybe<alloc::sync::Arc<gandr_core_term::CodataSignature>, data_scope::Absent>
    {
        let answer = self
            .codata_signatures
            .get(&constant)
            .map_or(Maybe::Absent(data_scope::Absent::Unknown), |signature| {
                Maybe::Present(alloc::sync::Arc::clone(signature))
            });
        if let SupportLog::Recording { ref mut codata, .. } = self.support {
            codata.push(crate::support::CodataConsulted::new(
                constant,
                match answer {
                    Maybe::Present(ref signature) => Some(alloc::sync::Arc::clone(signature)),
                    Maybe::Absent(_) => None,
                },
            ));
        }
        answer
    }

    /// Open the block of the data declaration at `position` for its
    /// signature's formation: until the block closes, a nominal lookup of
    /// `position` answers `signature`. The other families of its mutual block
    /// stay in scope beside it.
    ///
    /// # Specification
    /// - requires: nothing; a block already open at `position` is replaced.
    /// - ensures: [`Self::data_in_scope`] answers `signature` at `position`.
    /// - provides: the one scope a data declaration's fields name it in.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field naming its own family forms inside the block
    ///   and a later reference to the same family, outside it, needs the
    ///   admitted signature.
    /// - witness: `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
    #[spec(ensures: matches!(self.data_in_scope(position), Maybe::Present(_)))]
    pub(crate) fn open_block(
        &mut self,
        position: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::DataSignature>,
    )
    {
        self.forming.retain(|&(held, _)| held != position);
        self.forming.push((position, signature));
    }

    /// Close the forming block at `position`; the other families of its
    /// mutual block stay in scope until their own close.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn close_block(
        &mut self,
        position: ConstantIndex,
    )
    {
        self.forming.retain(|&(held, _)| held != position);
    }

    /// Open the mutual block `block` over the signatures of its families and
    /// the bodies of its definitions: each family is in scope until its own
    /// formation closes it, and the block is what each family's occurrences
    /// are walked by, through its definitions' bodies.
    ///
    /// # Specification
    /// - requires: `families` are the block's data declarations, in order, and
    ///   `definitions` the bodies of its definitions that have one.
    /// - ensures: [`Self::data_in_scope`] answers each family's signature,
    ///   [`Self::block_of`] answers `block` for each of its members, and
    ///   [`Self::block_definitions`] answers `definitions`.
    /// - provides: the scope a mutual block's definitions' declared types form
    ///   in before any family's constructors do.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe and its decoder admitted as one block, and
    ///   a family naming itself through a definition of its block refused.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    /// - witness: `tests::recursive_data::a_definition_of_the_block_is_read_through_602`
    #[spec(ensures: self.mutual == Maybe::Present(block))]
    pub(crate) fn open_mutual(
        &mut self,
        block: crate::occurrence::Block,
        families: impl IntoIterator<
            Item = (
                ConstantIndex,
                alloc::sync::Arc<gandr_core_term::DataSignature>,
            ),
        >,
        definitions: Vec<(ConstantIndex, ValueId)>,
    )
    {
        self.mutual = Maybe::Present(block);
        if usize::from(block.families()).saturating_sub(usize::from(block.first())) >= 2 {
            self.kin.push(block);
        }
        self.forming.extend(families);
        self.defining = definitions;
    }

    /// The bodies of the open mutual block's definitions, by position; none
    /// outside a block.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn block_definitions(&self) -> &[(ConstantIndex, ValueId)]
    {
        &self.defining
    }

    /// Close the mutual block: every family left forming leaves scope.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn close_mutual(&mut self)
    {
        self.mutual = Maybe::Absent(mutual::Absent::Lone);
        self.forming.clear();
        self.defining.clear();
        self.hindsight.clear();
    }

    /// The mutual block of several families the family at `position` was
    /// opened in.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn kin_of(
        &self,
        position: ConstantIndex,
    ) -> Maybe<crate::occurrence::Block, mutual::Absent>
    {
        self.kin
            .iter()
            .rev()
            .find(|block| block.first() <= position && position < block.families())
            .map_or(Maybe::Absent(mutual::Absent::Lone), |&block| {
                Maybe::Present(block)
            })
    }

    /// The block the data declaration at `position` is admitted in: the open
    /// mutual block when it holds `position`, else `position` alone.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn block_of(
        &self,
        position: ConstantIndex,
    ) -> crate::occurrence::Block
    {
        match self.mutual {
            Maybe::Present(block)
                if block.holds(position) == crate::occurrence::Membership::Family =>
            {
                block
            },
            Maybe::Present(_) | Maybe::Absent(_) => crate::occurrence::Block::lone(position),
        }
    }

    /// The signature forming at `constant`, if one is.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: walks the families forming, one for a lone declaration and at
    ///   most its mutual block's family count otherwise.
    fn forming_at(
        &self,
        constant: ConstantIndex,
    ) -> Option<&alloc::sync::Arc<gandr_core_term::DataSignature>>
    {
        self.forming
            .iter()
            .find_map(|&(held, ref signature)| (held == constant).then_some(signature))
    }

    /// The nominal signature in scope at `constant`, without logging: the
    /// forming block's when it is that position's, else the admitted one.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: [`Self::forming_at`]'s walk, then one ordered-map lookup.
    #[inline]
    pub fn data_in_scope(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<alloc::sync::Arc<gandr_core_term::DataSignature>, data_scope::Absent>
    {
        if let Some(signature) = self.forming_at(constant) {
            return Maybe::Present(alloc::sync::Arc::clone(signature));
        }
        self.data_signatures
            .get(&constant)
            .map_or(Maybe::Absent(data_scope::Absent::Unknown), |signature| {
                Maybe::Present(alloc::sync::Arc::clone(signature))
            })
    }

    /// Read and log a complete nominal signature, including its absence.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a forming block's signature at its own position, unlogged;
    ///   otherwise the exact stored table, and a supported judgment logs its
    ///   identity and table, rather than only its universe.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — changing only a constructor table, or supplying a
    ///   declaration that was missing, changes a dependent judgment's answer; a
    ///   declaration's own fields read its forming signature, which no later
    ///   run can disagree with.
    /// - witness: `tests::native_formers::native_signature_support_and_adoption`
    /// - witness: `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
    #[spec(ensures: |ret| match self.forming_at(constant) {
Some(signature) => ret.as_ref() == Some(signature),
None => ret.as_ref() == self.data_signatures.get(&constant) && match self.support {
SupportLog::Off => true,
SupportLog::Recording { ref data,.. } => data.last().is_some_and(|entry| entry.constant() == constant && entry.signature() == ret.as_deref()),
},
})]
    pub(crate) fn consult_data(
        &mut self,
        constant: ConstantIndex,
    ) -> Option<alloc::sync::Arc<gandr_core_term::DataSignature>>
    {
        if let Some(signature) = self.forming_at(constant) {
            return Some(alloc::sync::Arc::clone(signature));
        }
        let answer = self
            .data_signatures
            .get(&constant)
            .map(alloc::sync::Arc::clone);
        if let SupportLog::Recording { ref mut data, .. } = self.support {
            data.push(crate::support::DataConsulted::new(constant, answer.clone()));
        }
        answer
    }

    /// Mint the atom for the abstract type at `constant`, formed at `level`,
    /// and retain it.
    ///
    /// # Specification
    /// - requires: the abstract type formed at `level`, as
    ///   [`crate::former::form_abstract`] gives it.
    /// - ensures: the atom [`SealTable::mint`] gives the declaration's site,
    ///   and the context answers `level` for `constant`; on refusal the table
    ///   and the retained abstract types are unchanged.
    /// - fails: [`CheckRefusal::SealSiteRepeated`] naming the site when it was
    ///   minted before.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::SealSiteRepeated`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two abstract types at one site, the second refused by
    ///   name with nothing minted for it.
    /// - witness: `module::tests::a_repeated_sealing_site_is_refused_and_mints_nothing`
    #[spec(
        captures: before = self.seals.sites().len(),
        ensures: |ret| match ret {
            | Ok(id) => id.site() == declared.site()
                && self.seals.sites().len() == before.saturating_add(1)
                && self.sealed.contains_key(&constant),
            | Err(refusal) => refusal == CheckRefusal::SealSiteRepeated(declared.site())
                && self.seals.sites().len() == before,
        },
    )]
    pub(crate) fn seal_abstract(
        &mut self,
        constant: ConstantIndex,
        declared: AbstractType,
        level: Level,
    ) -> Result<SealId, CheckRefusal>
    {
        let atom = self
            .seals
            .mint(declared.site())
            .map_err(|_minted| CheckRefusal::SealSiteRepeated(declared.site()))?;
        if let Maybe::Present(interface) = declared.interface()
            && let Maybe::Present(_) = interface.law()
        {
            self.definitions.identify(constant, interface.relation());
        }
        let _previous = self.sealed.insert(constant, Sealed { declared, level });
        Ok(atom)
    }

    /// Give the declaration at `constant` the built-in `role`, when the
    /// declaration's `content` is of the judgement that holds the role, answers
    /// the role's canonical form and no earlier declaration holds the role.
    ///
    /// # Specification
    /// - requires: `content` is the content of the declaration at `constant`.
    /// - ensures: the context answers `constant` for `role`; a second claim by
    ///   the same declaration is admitted unchanged. The holders of `E` and `F`
    ///   answer their canonical bodies once those are judged
    ///   ([`crate::canonical::answers`]), so this claim reads only their
    ///   judgement.
    /// - fails: [`CheckRefusal::BuiltinMisplaced`] when the content is of
    ///   another judgement than [`gandr_kernel_term::Builtin::holder`],
    ///   [`CheckRefusal::BuiltinNotCanonical`] naming the first departure when
    ///   the holder of the signature type or of the pair type departs from its
    ///   canonical form, and [`CheckRefusal::BuiltinRepeated`] naming the
    ///   holder when another declaration holds the role; the context is
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::BuiltinMisplaced`],
    /// [`CheckRefusal::BuiltinNotCanonical`]
    /// and [`CheckRefusal::BuiltinRepeated`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a role claimed by two declarations, a role on a
    ///   declaration of the wrong judgement, and a signature type or a pair
    ///   type in another shape are each refused by cause.
    /// - witness: `module::tests::a_builtin_role_is_held_once_by_a_declaration_of_its_judgement_3575`
    /// - witness: `module::tests::a_signature_type_in_another_shape_holds_no_role_5254`
    /// - witness: `module::tests::a_pair_type_in_another_shape_holds_no_role_5255`
    #[spec(
        captures: before = self.builtins.get(&role).copied(),
        ensures: |ret| match ret {
            | Ok(()) => matches!((role.holder(), content), (gandr_kernel_term::Holder::Data, crate::DeclarationContent::Data(_)) | (gandr_kernel_term::Holder::Value, crate::DeclarationContent::Value { .. }))
                && before.is_none_or(|holder| holder == constant)
                && self.builtins.get(&role) == Some(&constant),
            | Err(refusal) => self.builtins.get(&role).copied() == before
                && if !matches!((role.holder(), content), (gandr_kernel_term::Holder::Data, crate::DeclarationContent::Data(_)) | (gandr_kernel_term::Holder::Value, crate::DeclarationContent::Value { .. })) {
                    refusal == CheckRefusal::BuiltinMisplaced(role)
                }
                else if let CheckRefusal::BuiltinNotCanonical { role: refused, .. } = refusal {
                    refused == role && matches!(role, gandr_kernel_term::Builtin::IrSignature | gandr_kernel_term::Builtin::IrPair)
                }
                else {
                    before.is_some_and(|holder| refusal == CheckRefusal::BuiltinRepeated { role, holder })
                },
        },
    )]
    pub(crate) fn claim_builtin(
        &mut self,
        constant: ConstantIndex,
        role: gandr_kernel_term::Builtin,
        content: &crate::DeclarationContent,
    ) -> Result<(), CheckRefusal>
    {
        let fits = matches!(
            (role.holder(), content),
            (
                gandr_kernel_term::Holder::Data,
                crate::DeclarationContent::Data(_)
            ) | (
                gandr_kernel_term::Holder::Value,
                crate::DeclarationContent::Value { .. }
            )
        );
        if !fits {
            return Err(CheckRefusal::BuiltinMisplaced(role));
        }
        if let &crate::DeclarationContent::Data(ref signature) = content {
            let canonical = match role {
                gandr_kernel_term::Builtin::IrSignature => {
                    crate::canonical::signature(self.arena(), constant, signature)
                },
                gandr_kernel_term::Builtin::IrPair => {
                    crate::canonical::pair(self.arena(), signature)
                },
                gandr_kernel_term::Builtin::IrArgs | gandr_kernel_term::Builtin::IrDecode => Ok(()),
            };
            canonical.map_err(|departure| CheckRefusal::BuiltinNotCanonical { role, departure })?;
        }
        match self.builtins.entry(role) {
            alloc::collections::btree_map::Entry::Occupied(held) if *held.get() != constant => {
                Err(CheckRefusal::BuiltinRepeated {
                    role,
                    holder: *held.get(),
                })
            },
            alloc::collections::btree_map::Entry::Occupied(_) => Ok(()),
            alloc::collections::btree_map::Entry::Vacant(vacant) => {
                let _held = vacant.insert(constant);
                Ok(())
            },
        }
    }

    /// The declaration that holds the built-in `role`.
    ///
    /// # Specification
    /// - ensures: the holder [`Self::claim_builtin`] recorded for `role`.
    /// - fails: [`gandr_kernel_term::Departure::Reads`] naming `role` when no
    ///   declaration holds it, the departure of a canonical form that reads it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`gandr_kernel_term::Departure::Reads`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `E` read before the pair type has a holder is refused
    ///   for the role it reads, and read after it compares its answers.
    /// - witness: `canonical::tests::a_holder_of_e_is_refused_at_its_first_departing_answer_5255`
    #[spec(ensures: |ret| match ret {
        | Ok(holder) => self.builtins.get(&role) == Some(&holder),
        | Err(departure) => departure == gandr_kernel_term::Departure::Reads(role) && !self.builtins.contains_key(&role),
    })]
    #[inline]
    pub(crate) fn builtin_holder(
        &self,
        role: gandr_kernel_term::Builtin,
    ) -> Result<ConstantIndex, gandr_kernel_term::Departure>
    {
        self.builtins
            .get(&role)
            .copied()
            .ok_or(gandr_kernel_term::Departure::Reads(role))
    }

    /// Take the built-in `role` from the declaration at `constant`, whose
    /// judged body departs from the role's canonical body.
    ///
    /// # Specification
    /// - ensures: no declaration holds `role` when `constant` held it; the
    ///   table is unchanged otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a holder of `E` refused for its answers gives its
    ///   role back, so the next holder is refused for its own answers and not
    ///   as a second holder.
    /// - witness: `module::tests::a_builtin_role_is_held_once_by_a_declaration_of_its_judgement_3575`
    #[spec(
        captures: before = self.builtins.get(&role).copied(),
        ensures: if before == Some(constant) {
            !self.builtins.contains_key(&role)
        } else {
            self.builtins.get(&role).copied() == before
        },
    )]
    #[inline]
    pub(crate) fn release_builtin(
        &mut self,
        role: gandr_kernel_term::Builtin,
        constant: ConstantIndex,
    )
    {
        if self.builtins.get(&role) == Some(&constant) {
            let _released = self.builtins.remove(&role);
        }
    }

    /// Re-form and adopt an abstract type a previous run admitted, minting its
    /// atom again in this context.
    ///
    /// # Specification
    /// - requires: identifiers are read in this context; no cached formation
    ///   claim is trusted across arenas.
    /// - ensures: the fresh position holds the abstract type, its site minted;
    ///   on refusal no atom is minted and no abstract type retained, though a
    ///   repeated site leaves the position admitted, as a judged refusal does.
    /// - fails: the formation refusal, a repeated site, or admission out of
    ///   source order.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a formation refusal, [`CheckRefusal::SealSiteRepeated`] or the
    /// ordinary admission-order refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reusing a sealed module's checkpoint must mint the
    ///   atom again, answering its level as a judgement would, and a second
    ///   adoption at the same site is refused with nothing retained.
    /// - witness: `context::tests::an_adopted_abstract_type_mints_its_site_again`
    #[spec(ensures: |ret| ret.is_err() || self.sealed.contains_key(&constant))]
    #[inline]
    pub fn adopt_abstract(
        &mut self,
        constant: ConstantIndex,
        declared: AbstractType,
    ) -> Result<(), CheckRefusal>
    {
        let level = crate::former::form_abstract(self, declared)?;
        self.admit(constant)?;
        let _atom = self.seal_abstract(constant, declared, level)?;
        Ok(())
    }

    /// The level of the universe the abstract type at `atom` inhabits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the level of the admitted abstract type's kind.
    /// - fails: [`CheckRefusal::NotAnAbstractType`] when no abstract type was
    ///   admitted at `atom`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::NotAnAbstractType`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an atom of an admitted abstract type and one naming a
    ///   value declaration separate the answer.
    /// - witness: `module::tests::an_atom_naming_no_abstract_type_is_refused`
    #[spec(ensures: |ret| match self.sealed.get(&atom) {
        | Some(sealed) => ret.as_ref() == Ok(&sealed.level),
        | None => ret == Err(CheckRefusal::NotAnAbstractType(atom)),
    })]
    pub(crate) fn abstract_level(
        &self,
        atom: ConstantIndex,
    ) -> Result<Level, CheckRefusal>
    {
        self.sealed
            .get(&atom)
            .map(|sealed| sealed.level.clone())
            .ok_or(CheckRefusal::NotAnAbstractType(atom))
    }

    /// Whether the abstract type at `atom` crosses outside its seal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the mobility the admitted abstract type's signature marks.
    /// - fails: [`CheckRefusal::NotAnAbstractType`] when no abstract type was
    ///   admitted at `atom`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::NotAnAbstractType`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marked and an unmarked atom separate the answer.
    /// - witness: `worlds::tests::mobility_is_decided_on_every_former`
    #[spec(ensures: |ret| match self.sealed.get(&atom) {
        | Some(sealed) => ret == Ok(sealed.declared.mobility()),
        | None => ret == Err(CheckRefusal::NotAnAbstractType(atom)),
    })]
    pub(crate) fn abstract_mobility(
        &self,
        atom: ConstantIndex,
    ) -> Result<crate::worlds::Mobility, CheckRefusal>
    {
        self.sealed
            .get(&atom)
            .map(|sealed| sealed.declared.mobility())
            .ok_or(CheckRefusal::NotAnAbstractType(atom))
    }

    /// Bound every declaration's entry by the host's: the world each body is
    /// judged at and the capabilities it holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every declaration judged after this stands at `host`'s entry,
    ///   or within it as it states its own.
    /// - panics: none.
    /// - executable: none — the clause speaks of the judgements after this
    ///   call, which no predicate at the call can observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::worlds::Worlds::resolve`].
    /// - witness: `worlds::tests::a_stated_entry_is_bounded_by_the_host_s`
    #[inline]
    pub fn enter_at(
        &mut self,
        host: crate::worlds::HostEntry,
    )
    {
        self.worlds.host(host);
    }

    /// Admit the world declaration at `constant`, requiring `requirement`, as
    /// its judgement admits it: a pass that adopts the declaration's earlier
    /// verdict declares the world without judging it again.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` is admitted and declares a world, and code that
    ///   runs at it performs in `requirement`.
    /// - fails: admission out of source order.
    /// - panics: none.
    ///
    /// # Errors
    /// The ordinary admission-order refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — after the adopted worlds, an entry that migrates to
    ///   one of them checks as on a fresh pass.
    /// - witness: `worlds::tests::an_adopted_located_program_judges_as_a_fresh_pass_3381`
    #[spec(ensures: |ret| ret.is_err() || self.worlds.declared().contains(&constant))]
    #[inline]
    pub fn adopt_world(
        &mut self,
        constant: ConstantIndex,
        requirement: &gandr_core_term::effect::EffectRow,
    ) -> Result<(), CheckRefusal>
    {
        self.admit(constant)?;
        self.worlds.declare(constant, requirement);
        Ok(())
    }

    /// Record what the register holds of `constant`'s declaration, as its
    /// judgement settles it: a pass that adopts the declaration settles it
    /// without judging it again.
    ///
    /// # Specification
    /// - requires: `constant` is admitted.
    /// - ensures: [`Self::located`] answers `located` for `constant`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an adopted entry settled as its judgement left it
    ///   refuses its reader as a fresh pass does; settled at the host's world,
    ///   unspent, the reader checks.
    /// - witness: `worlds::tests::an_adopted_located_program_judges_as_a_fresh_pass_3381`
    #[spec(ensures: self.located(constant) == located)]
    #[inline]
    pub fn settle_adopted(
        &mut self,
        constant: ConstantIndex,
        located: crate::worlds::Located,
    )
    {
        self.worlds
            .settle(constant, located.home(), located.spending());
    }

    /// What the register holds of `constant`'s declaration: its home and
    /// whether a run of it spent a capability.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn located(
        &self,
        constant: ConstantIndex,
    ) -> crate::worlds::Located
    {
        self.worlds.located(constant)
    }

    /// The entry `declaration` is judged at under the host's entry, as its
    /// judgement resolves it: the host's world with no capability for a
    /// declaration with neither a signature nor a body, and for every
    /// declaration that is no value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a value declaration with a signature or a body, the entry
    ///   [`crate::worlds::Worlds::resolve`] gives; the default entry otherwise.
    /// - fails: as [`crate::worlds::Worlds::resolve`] fails.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`crate::worlds::Worlds::resolve`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — with no host entry a stated entry resolves as stated
    ///   and an unstated one to the host's world; within a host's entry the
    ///   unstated one takes the host's.
    /// - witness: `worlds::tests::an_adopted_located_program_judges_as_a_fresh_pass_3381`
    #[spec(ensures: |ref ret| matches!(
        *declaration.content(),
        crate::DeclarationContent::Value { signature: Maybe::Present(_), .. }
            | crate::DeclarationContent::Value { body: Maybe::Present(_), .. }
    ) || ret.as_ref().is_ok_and(|entry| *entry == crate::worlds::Entry::default()))]
    #[inline]
    pub fn resolve_entry(
        &self,
        declaration: &crate::Declaration,
    ) -> Result<crate::worlds::Entry, crate::worlds::LocatedDefect>
    {
        match *declaration.content() {
            crate::DeclarationContent::Value {
                signature: Maybe::Present(_),
                ..
            }
            | crate::DeclarationContent::Value {
                body: Maybe::Present(_),
                ..
            } => self
                .worlds
                .resolve(declaration.constant(), declaration.entry()),
            crate::DeclarationContent::Value { .. }
            | crate::DeclarationContent::Data(_)
            | crate::DeclarationContent::Codata(_)
            | crate::DeclarationContent::Abstract(_)
            | crate::DeclarationContent::World(_) => Ok(crate::worlds::Entry::default()),
        }
    }

    /// The located state: the worlds declared, the homes and the entries.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn worlds(&self) -> &crate::worlds::Worlds
    {
        &self.worlds
    }

    /// The located state, to admit a world, enter or settle a declaration.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn worlds_mut(&mut self) -> &mut crate::worlds::Worlds
    {
        &mut self.worlds
    }

    /// The abstract types admitted, ascending by position, as offered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn abstract_types(&self) -> impl Iterator<Item = (ConstantIndex, AbstractType)> + '_
    {
        self.sealed
            .iter()
            .map(|(&constant, sealed)| (constant, sealed.declared))
    }

    /// The sites the context minted atoms for, in minting order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn seal_table(&self) -> &SealTable
    {
        &self.seals
    }

    /// The representation the atom at `atom` stands for while the declaration
    /// admitted last is judged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the representation exactly when an abstract type was admitted
    ///   at `atom` and the position admitted last lies in `atom + 1 ..= atom +
    ///   extent`; otherwise the atom is rigid.
    /// - provides: the one decision of where a seal reaches.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member inside the seal, the atom's own position and
    ///   a declaration past the extent separate the reach.
    /// - witness: `module::tests::a_sealed_member_checks_at_the_representation_inside`
    #[spec(ensures: |ret| match (self.admitted, self.sealed.get(&atom)) {
        | (Maybe::Present(reader), Some(sealed)) if reader > atom
            && usize::from(reader).saturating_sub(usize::from(atom)) <= usize::from(sealed.declared.extent()) =>
            ret == Maybe::Present(sealed.declared.representation()),
        | _ => ret == Maybe::Absent(unfolding::Absent::Rigid),
    })]
    fn manifest(
        &self,
        atom: ConstantIndex,
    ) -> Maybe<ValueTypeId, unfolding::Absent>
    {
        let Maybe::Present(reader) = self.admitted
        else {
            return Maybe::Absent(unfolding::Absent::Rigid);
        };
        match self.sealed.get(&atom) {
            Some(sealed)
                if reader > atom
                    && usize::from(reader).saturating_sub(usize::from(atom))
                        <= usize::from(sealed.declared.extent()) =>
            {
                Maybe::Present(sealed.declared.representation())
            },
            Some(_) | None => Maybe::Absent(unfolding::Absent::Rigid),
        }
    }

    /// The interface the atom at `atom` relates its elements by, with its
    /// kind, when the atom was admitted with one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the interface and kind exactly when an abstract type was
    ///   admitted at `atom` with an interface, whether or not it states a law.
    /// - provides: the identity system an identity at the atom reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lawful atom's identity reads its relation, a
    ///   lawless one refuses the relation's evidence by name, and an atom
    ///   stating no interface keeps its neutral fibre.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_atom_stating_no_law_refuses_the_relation_s_evidence_by_name`
    #[spec(ensures: |ret| ret.is_some() == self.sealed.get(&atom).is_some_and(|sealed| matches!(sealed.declared.interface(), Maybe::Present(_))))]
    pub(crate) fn interface_of(
        &self,
        atom: ConstantIndex,
    ) -> Option<(crate::declaration::AtomInterface, ValueTypeId)>
    {
        let sealed = self.sealed.get(&atom)?;
        match sealed.declared.interface() {
            Maybe::Present(interface) => Some((interface, sealed.declared.kind())),
            Maybe::Absent(_) => None,
        }
    }

    /// The allowance each judgement starts with.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn budget(&self) -> CheckBudget
    {
        self.budget
    }

    /// The type the declaration at `constant` supplied.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the type recorded for `constant` when one was.
    /// - provides: `signature_table::Absent::Untyped` when no declaration at
    ///   that position supplied a type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the ascending search,
    ///   separated by a position recorded, a position admitted without a type,
    ///   and a position never admitted.
    /// - witness: `module::tests::a_later_declaration_reads_an_earlier_type`
    /// - witness: `module::tests::a_body_that_synthesised_nothing_supplies_no_type`
    #[spec(ensures: |ret| {
        let next = self.signatures.partition_point(|&(held, _)| held < constant);
        match self.signatures.get(next) {
            | Some(&(held, declared)) if held == constant => ret == Maybe::Present(declared),
            | Some(_) | None => ret == Maybe::Absent(signature_table::Absent::Untyped),
        }
    })]
    #[inline]
    pub fn signature(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<FormedValueType, signature_table::Absent>
    {
        self.signatures
            .binary_search_by_key(&constant, |&(held, _)| held)
            .map_or(
                Maybe::Absent(signature_table::Absent::Untyped),
                |found| match self.signatures.get(found) {
                    Some(&(_, declared)) => Maybe::Present(declared),
                    None => Maybe::Absent(signature_table::Absent::Untyped),
                },
            )
    }

    /// Admit the declaration at `constant` with the type an earlier judgement
    /// of it supplied, without judging it again.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-order position is admissible input and
    ///   refused.
    /// - ensures: on success `constant` is the highest position admitted,
    ///   [`Self::signature`] answers `supplied` for it, and a present body is
    ///   defined only when a type is supplied, with the elaboration performed
    ///   by [`Self::define`]. A body without a supplied type is not installed.
    ///   An absent body owed ([`unfolding::Absent::Owed`]) or waiting
    ///   ([`unfolding::Absent::Waiting`]) is held so, as the judgement that
    ///   gave it holds it, for a later judgement to suspend on.
    /// - provides: the seat an incremental caller places a reused verdict in;
    ///   the caller, not the context, vouches that the verdict still answers,
    ///   and passes the body exactly when the verdict it reuses accepted it,
    ///   and the reason it has none otherwise.
    /// - fails: [`CheckRefusal::AdmissionOrder`] when `constant` is not above
    ///   the highest position admitted; the context is unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::AdmissionOrder`] — `constant` does not follow every
    ///   position admitted before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the admission, the record and the
    ///   definition, separated by an adopted type a later declaration reads, an
    ///   adopted absence a later declaration finds no type at, an adoption out
    ///   of order refused with the table unchanged, an adopted body a later
    ///   decode unfolds to, and an adopted hole a later decode suspends on.
    /// - witness: `module::tests::an_adopted_answer_is_read_as_if_judged`
    /// - witness: `context::tests::an_adopted_untyped_body_does_not_become_a_definition`
    /// - witness: `gandr-core-checker::tests::elaboration::incremental_equals_from_scratch`
    #[spec(
        captures: [admitted = self.admitted, entries = self.signatures.len(), previous = self.definitions.body(constant)],
        ensures: |ret| match ret {
            | Ok(()) => self.admitted == Maybe::Present(constant)
                && self.signature(constant) == supplied
                && matches!((supplied, unfolds, self.definitions.body(constant)),
                    (Maybe::Present(_), Maybe::Present(_), Maybe::Present(_))
                        | (Maybe::Absent(_), _, Maybe::Absent(_))
                        | (_, Maybe::Absent(_), Maybe::Absent(_)))
                && (unfolds != Maybe::Absent(unfolding::Absent::Owed) || self.deferrals.owed.contains(&constant))
                && (unfolds != Maybe::Absent(unfolding::Absent::Waiting) || self.deferrals.suspended.contains(&constant)),
            | Err(_) => self.admitted == admitted && self.signatures.len() == entries
                && self.definitions.body(constant) == previous,
        },
    )]
    #[inline]
    pub fn adopt(
        &mut self,
        constant: ConstantIndex,
        supplied: Maybe<FormedValueType, signature_table::Absent>,
        unfolds: Maybe<ValueId, unfolding::Absent>,
    ) -> Result<(), CheckRefusal>
    {
        self.admit(constant)?;
        if let Maybe::Present(declared) = supplied {
            self.record(constant, declared);
            if let Maybe::Present(body) = unfolds {
                self.define(constant, declared, body);
            }
        }
        match unfolds {
            Maybe::Absent(unfolding::Absent::Owed) => {
                self.deferrals.owed.insert(constant);
            },
            Maybe::Absent(unfolding::Absent::Waiting) => {
                self.deferrals.suspended.insert(constant);
            },
            Maybe::Present(_) | Maybe::Absent(unfolding::Absent::Rigid) => {},
        }
        Ok(())
    }

    /// [`Self::adopt`] of a verdict whose judgement formed `declared`: the
    /// type is seated as that judgement formed it, without forming it again.
    ///
    /// # Specification
    /// - requires: `declared` is a type the reused verdict's judgement formed,
    ///   read in this context from the same content and under the same
    ///   consulted answers and unfoldings, so forming it here answers as it
    ///   answered there; the caller vouches for both, as for [`Self::adopt`].
    /// - ensures: as [`Self::adopt`] with `declared` supplied as formed.
    /// - fails: as [`Self::adopt`].
    /// - panics: none.
    /// - economy: no formation walk; the reused verdict's own formation is the
    ///   claim.
    ///
    /// # Errors
    /// - [`CheckRefusal::AdmissionOrder`] — as [`Self::adopt`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type seated as formed is the answer a later
    ///   declaration reads, and the adopted body is the unfolding a later
    ///   decode of it reads, as for [`Self::adopt`].
    /// - witness: `module::tests::an_adopted_answer_is_read_as_if_judged`
    #[spec(ensures: |ret| ret.is_err() || self.signature(constant) == Maybe::Present(FormedValueType::derived(declared)))]
    #[inline]
    pub fn adopt_formed(
        &mut self,
        constant: ConstantIndex,
        declared: ValueTypeId,
        unfolds: Maybe<ValueId, unfolding::Absent>,
    ) -> Result<(), CheckRefusal>
    {
        self.adopt(
            constant,
            Maybe::Present(FormedValueType::derived(declared)),
            unfolds,
        )
    }

    /// The type the declaration at `constant` supplied, as the judgement reads
    /// it: logged when a supported judgement runs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer [`Self::signature`] gives; while a supported
    ///   judgement runs, the answer is also appended to its log, beside what
    ///   the world register holds of the declaration.
    /// - provides: the one read of the table the judgement makes, so the
    ///   support is complete by construction.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the log append, separated by a
    ///   supported judgement whose support is asserted entry by entry and an
    ///   unsupported judgement before it whose reads stay out.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    #[spec(
        captures: before = match self.support { SupportLog::Off => None, SupportLog::Recording { ref values,.. } => Some(values.len()) },
        ensures: |ret| ret == self.signature(constant) && match (&self.support, before) {
            | (&SupportLog::Off, None) => true,
            | (&SupportLog::Recording { ref values,.. }, Some(count)) => values.len().checked_sub(1) == Some(count)
                && values.last() == Some(&Consulted::new(constant, ret, self.worlds.located(constant))),
            | _ => false,
        },
    )]
    pub(crate) fn consult(
        &mut self,
        constant: ConstantIndex,
    ) -> Maybe<FormedValueType, signature_table::Absent>
    {
        let answer = self.signature(constant);
        if let SupportLog::Recording { ref mut values, .. } = self.support {
            values.push(Consulted::new(
                constant,
                answer,
                self.worlds.located(constant),
            ));
        }
        self.deferrals.read(constant);
        answer
    }

    /// Start logging the answers handed out, discarding any earlier log.
    ///
    /// # Specification
    /// - requires: nothing; an earlier log is intentionally discarded.
    /// - ensures: logging is active with no earlier consultation retained.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consecutive supported judgements and preceding
    ///   unsupported reads expose their own exact supports; stale entries or
    ///   failure to start logging change the observed consultation sets.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    #[spec(ensures: matches!(self.support, SupportLog::Recording { ref values,ref data,ref codata } if values.is_empty() && data.is_empty() && codata.is_empty()))]
    pub(crate) fn start_support(&mut self)
    {
        self.support = SupportLog::Recording {
            values: Vec::new(),
            data: Vec::new(),
            codata: Vec::new(),
        };
    }

    /// Stop logging and return the support the log stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the support of every answer logged since
    ///   [`Self::start_support`], or the empty support when none was started;
    ///   logging is off afterwards.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successful and refused supported judgements expose
    ///   the sorted answers actually read, including an interrupted prefix;
    ///   lost entries or retained recording change the next observed support.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    /// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
    #[spec(
        captures: before = match self.support { SupportLog::Off => (0,0,0), SupportLog::Recording { ref values,ref data,ref codata } => (values.len(),data.len(),codata.len()) },
        ensures: |ret| matches!(self.support, SupportLog::Off)
            && ret.consulted().len() <= before.0 && ret.consulted().is_empty() == (before.0 == 0)
            && ret.data_consulted().len() <= before.1 && ret.data_consulted().is_empty() == (before.1 == 0)
            && ret.codata_consulted().len() <= before.2 && ret.codata_consulted().is_empty() == (before.2 == 0),
    )]
    pub(crate) fn finish_support(&mut self) -> Support
    {
        match core::mem::replace(&mut self.support, SupportLog::Off) {
            SupportLog::Recording {
                values,
                data,
                codata,
            } => Support::from_log(values, data, codata),
            SupportLog::Off => Support::default(),
        }
    }

    /// Stop logging and keep the log as it stands, so that the reads after
    /// this call stay out of it until [`Self::restore_support`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: logging is off, and the log is returned unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed run's support equals the support of the same
    ///   declaration judged with no typed run.
    /// - witness: `module::tests::a_kept_support_is_the_support_of_the_judgement_alone_6573`
    #[spec(captures: was = core::mem::discriminant(&self.support), ensures: |ret| matches!(self.support, SupportLog::Off) && core::mem::discriminant(&ret) == was)]
    pub(crate) fn hold_support(&mut self) -> SupportLog
    {
        core::mem::replace(&mut self.support, SupportLog::Off)
    }

    /// Log again into `held`, the log [`Self::hold_support`] kept.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn restore_support(
        &mut self,
        held: SupportLog,
    )
    {
        self.support = held;
    }

    /// The arena every id resolves in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arena(&self) -> &CoreArena
    {
        self.arena
    }

    /// The arena, for minting the types the judgement rewrites and the types
    /// an incremental pass seats. A caller only mints into it: the context's
    /// ids stay valid because the arena only grows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn arena_mut(&mut self) -> &mut CoreArena
    {
        self.arena
    }

    /// The bodies a code constant unfolds to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn definitions(&self) -> &CodeDefinitions
    {
        &self.definitions
    }

    /// Record body reads in `probe`.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "unfolding-probe")]
    #[inline]
    pub fn observe_unfoldings(
        &mut self,
        probe: UnfoldingProbe,
    )
    {
        self.definitions.observe_unfoldings(probe);
    }

    /// Set the declaration that owns later body reads.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "unfolding-probe")]
    #[inline]
    pub(crate) fn unfolding_subject(
        &self,
        subject: ConstantIndex,
    )
    {
        self.definitions.unfolding_subject(subject);
    }

    /// Define `constant`, accepted at `declared` with `body`: a later decode
    /// of a code naming it unfolds to the body, elaborated.
    ///
    /// # Specification
    /// - requires: `body` was accepted at `declared`.
    /// - ensures: [`Self::definitions`] holds, at `constant`, `body` itself
    ///   unless `body` is a `ua` the judgement derived a path for or a path
    ///   product it elaborated, which holds that native path instead, or
    ///   `declared` is, at its weak head, a value universe above the level of
    ///   the universe `body` inhabits; then the lift of `body` to that
    ///   universe, minted. The definition is the code the kernel admits for the
    ///   declaration, so a decode or a transport unfolds alike on either side.
    /// - fails: never; a body whose level cannot be read is defined as it
    ///   stands, and the kernel's replay of an unfolding over it declines
    ///   rather than certifies a wrong one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — code definitions at their natural universe and a
    ///   larger universe are observed by subsequent decoding and independent
    ///   readmission, and a transport along a constant defined by `ua` or by a
    ///   path product computes along its native path; a missing body, lift or
    ///   path changes those outcomes.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    /// - witness: `tests::ua::a_written_statement_derives_the_path_at_its_stratum`
    /// - witness: `tests::product::a_product_of_written_paths_elaborates_to_the_native_product`
    #[spec(ensures: matches!(self.definitions.body(constant), Maybe::Present(defined)
        if defined == body || self.natives.get(&body) == Some(&defined)
            || matches!(self.arena.value(defined), Some(Value::Quote(lifted))
            if matches!(value_type_view(self.arena, *lifted), Ok(ValueTypeView::Lift { .. })))))]
    pub(crate) fn define(
        &mut self,
        constant: ConstantIndex,
        declared: FormedValueType,
        body: ValueId,
    )
    {
        let elaborated = match self.natives.get(&body) {
            Some(&path) => path,
            None => self.elaborate(declared, body).unwrap_or(body),
        };
        self.definitions.define(constant, elaborated);
    }

    /// `body` at the universe `declared` names: lifted when `declared` is a
    /// value universe above the body's own.
    ///
    /// # Specification
    /// - requires: `body` was accepted at `declared`.
    /// - ensures: as [`Self::define`] states of the definition.
    /// - fails: the refusal reading `declared`'s weak head or the body's level
    ///   gives.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quoted small type declared at its own universe or a
    ///   larger one is observed through conversion and kernel readmission;
    ///   dropped or incorrectly shaped elaborations change these decisions.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|elaborated| elaborated == body
        || matches!(self.arena.value(elaborated), Some(Value::Quote(lifted))
            if matches!(value_type_view(self.arena, *lifted), Ok(ValueTypeView::Lift { .. })))))]
    fn elaborate(
        &mut self,
        declared: FormedValueType,
        body: ValueId,
    ) -> Result<ValueId, CheckRefusal>
    {
        let head = self.whnf_value_type(declared.id())?;
        let ValueTypeView::Universe {
            sort: GroundSort::Value,
            level,
        } = value_type_view(self.arena, head)?
        else {
            return Ok(body);
        };
        let target = level.clone();
        let natural = self.code_level(body, &target)?;
        if bool::from(natural.lt(&target)) {
            Ok(Lift::new(natural, target).mint(self.arena, body))
        }
        else {
            Ok(body)
        }
    }

    /// The codes the judgement checked at a universe above their own, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lifts(&self) -> &BTreeMap<ValueId, Lift>
    {
        &self.lifts
    }

    /// The residual collector: the holes owed, the declarations suspended and
    /// what the running judgement left.
    ///
    /// # Specification
    /// trivial.
    pub const fn deferrals(&self) -> &crate::elaboration::Deferrals
    {
        &self.deferrals
    }

    /// The residual collector, for the module run and the elaboration driver
    /// to open, read and mark.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn deferrals_mut(&mut self) -> &mut crate::elaboration::Deferrals
    {
        &mut self.deferrals
    }

    /// Whether the machine's `verdict` on a pair waits for a fill: it declined
    /// because a side stands on a hole or a mark, and a hole the running
    /// judgement nominated is still unbound, so the run that judges the
    /// filled body meets the pair again.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::elaboration::Deferred::Yes`] exactly when `verdict`
    ///   is the machine's indeterminate decline and
    ///   [`crate::elaboration::Deferrals::awaits`] answers it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reflexivity and an ascription whose path endpoints
    ///   call a definition over an omitted model are met once the model is
    ///   resolved, and refused when the filled endpoints are apart; reading the
    ///   decline as apart refuses the first before the resolution.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_endpoint_over_an_omitted_model_waits_for_its_resolution_2391`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_path_type_over_an_omitted_model_converts_once_resolved_2391`
    #[spec(ensures: |ret| ret == crate::elaboration::Deferred::No || verdict == gandr_core_nbe::MachineVerdict::Declined(gandr_core_nbe::DeclineReason::Indeterminate))]
    pub(crate) fn awaits_fill(
        &self,
        verdict: gandr_core_nbe::MachineVerdict,
    ) -> crate::elaboration::Deferred
    {
        if verdict
            == gandr_core_nbe::MachineVerdict::Declined(
                gandr_core_nbe::DeclineReason::Indeterminate,
            )
        {
            self.deferrals.awaits(self.arena())
        }
        else {
            crate::elaboration::Deferred::No
        }
    }

    /// The machine's relation of `point` to `endpoint`
    /// ([`crate::code::CodeDefinitions::relation`]). When the written sides
    /// refuse, the relation reads them again with the solution of each hole
    /// that the running judgement nominated and the solver bound
    /// ([`Self::read_solved`]). The run over the filled body reads the sides
    /// so.
    ///
    /// # Specification
    /// - requires: both sides stand under the context's intuitionistic binders.
    /// - ensures: the relation of the sides so read when the written sides
    ///   refuse, the read changes a side, and the sides so read relate or wait
    ///   for a fill ([`Self::awaits_fill`]); otherwise the relation of the
    ///   written sides.
    /// - provides: the verdict the run over the filled body gives, before the
    ///   fill. A hole that the signature's formation solves stands in a body
    ///   node that reads a binder's type, and the machine reads no solution. A
    ///   pair that the written sides relate costs no read and mints no node.
    ///   The read only ever adds an acceptance: every refusal is the written
    ///   sides' refusal.
    /// - fails: never; a refusal of the relation is its answer.
    /// - panics: none.
    /// - executable: none — the verdicts are the machine's own readings; a
    ///   predicate restating them would run the readings again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a composite whose first path omits its carrier, at
    ///   its own reflexivity, reads the carrier its signature solves; the
    ///   checker and the kernel admit it, and a composite at an endpoint that
    ///   the carrier does not reach is refused as on a written carrier.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_body_reads_the_carrier_its_signature_solves_5272`
    pub(crate) fn relate_solved(
        &mut self,
        point: ValueId,
        endpoint: ValueId,
        returning: &[gandr_kernel_term::DeBruijnIndex],
    ) -> Result<
        (
            gandr_core_nbe::MachineVerdict,
            Vec<gandr_kernel_conversion_trace::ConversionDecision<gandr_core_nbe::TraceNode>>,
        ),
        CheckRefusal,
    >
    {
        // A relation holds for the run when the machine relates the pair, or
        // when its verdict waits for a fill.
        let holds =
            |context: &Self, answer: &Result<(gandr_core_nbe::MachineVerdict, _), CheckRefusal>| {
                match *answer {
                    Ok((gandr_core_nbe::MachineVerdict::Convertible, _)) => true,
                    Ok((verdict, _)) => {
                        context.awaits_fill(verdict) == crate::elaboration::Deferred::Yes
                    },
                    Err(_) => false,
                }
            };
        let related = self
            .definitions()
            .relation(self.arena(), point, endpoint, returning);
        if holds(self, &related) {
            return related;
        }
        let solved = (self.read_solved(point), self.read_solved(endpoint));
        if solved == (point, endpoint) {
            return related;
        }
        let again = self
            .definitions()
            .relation(self.arena(), solved.0, solved.1, returning);
        if holds(self, &again) { again } else { related }
    }

    /// `value` read with the solution of each hole that the running judgement
    /// nominated and the solver bound. The run over the filled body reads the
    /// value so. A hole that the solver left unbound stays a hole.
    ///
    /// # Specification
    /// - requires: `value` stands under the context's intuitionistic binders.
    /// - ensures: `value` itself when the running judgement bound no hole, or
    ///   when the binders are past the count a binder index can name; otherwise
    ///   `value` with each bound hole filled by its solution, raised past the
    ///   binders between the solution's scope and where the hole stands, or
    ///   `value` itself when it holds none.
    /// - provides: the side that [`Self::relate_solved`] and the endpoint
    ///   conversion read again after the written side refuses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::relate_solved`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_body_reads_the_carrier_its_signature_solves_5272`
    #[spec(ensures: |ret| ret == value || self.arena.value(ret).is_some())]
    pub(crate) fn read_solved(
        &mut self,
        value: ValueId,
    ) -> ValueId
    {
        let bound = self.deferrals.bound(self.arena);
        if bound.is_empty() {
            return value;
        }
        let Ok(under) = u32::try_from(usize::from(self.depth(Zone::Intuitionistic)))
            .map(gandr_core_term::Binders::from)
        else {
            return value;
        };
        gandr_core_term::fill_value_holes(self.arena, (value, under), &bound)
    }

    /// Record a permitted residual, or retain ordinary rigid conversion.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn defer(
        &mut self,
        left: TypeNode,
        right: TypeNode,
    ) -> crate::elaboration::Deferred
    {
        self.deferrals.defer(self.arena, left, right)
    }

    /// Pose `left` against `right` to the solver when a side is the decode of
    /// a metavariable, under the intuitionistic binders open now.
    ///
    /// # Specification
    /// - requires: as [`crate::elaboration::Deferrals::unify`].
    /// - ensures: its answer, posed at the current depth.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a depth past any binder
    ///   count.
    /// - panics: none.
    /// - executable: none — the answer is
    ///   [`crate::elaboration::Deferrals::unify`]'s, checked by its own
    ///   specification; this call only reads the depth it is posed at.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::elaboration::Deferrals::unify`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_supplied_before_the_kernel_1216`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_refused_unforced_or_apart_1216`
    pub(crate) fn unify(
        &mut self,
        left: TypeNode,
        right: TypeNode,
    ) -> Result<crate::elaboration::Unified, CheckRefusal>
    {
        let scope = self.intuitionistic_scope()?;
        Ok(self.deferrals.unify(self.arena, scope, left, right))
    }

    /// Pose the value `left` against `right` to the solver when a side is a
    /// metavariable, under the intuitionistic binders open now.
    ///
    /// # Specification
    /// - requires: as [`crate::elaboration::Deferrals::unify_values`].
    /// - ensures: its answer, posed at the current depth.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a depth past any binder
    ///   count.
    /// - panics: none.
    /// - executable: none — the answer is
    ///   [`crate::elaboration::Deferrals::unify_values`]'s, checked by its own
    ///   specification; this call only reads the depth it is posed at.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::elaboration::Deferrals::unify_values`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_ascription_solves_the_wildcard_its_type_holds_1979`
    pub(crate) fn unify_values(
        &mut self,
        left: ValueId,
        right: ValueId,
    ) -> Result<crate::elaboration::Unified, CheckRefusal>
    {
        let scope = self.intuitionistic_scope()?;
        Ok(self.deferrals.unify_values(self.arena, scope, left, right))
    }

    /// Pose the row `left` against `right` to the solver when a side is open
    /// through a metavariable, under the intuitionistic binders open now.
    ///
    /// # Specification
    /// - requires: as [`crate::elaboration::Deferrals::unify_rows`].
    /// - ensures: its answer, posed at the current depth.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a depth past any binder
    ///   count.
    /// - panics: none.
    /// - executable: none — the answer is
    ///   [`crate::elaboration::Deferrals::unify_rows`]'s, checked by its own
    ///   specification; this call only reads the depth it is posed at.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::elaboration::Deferrals::unify_rows`].
    /// - witness: `elaboration::tests::a_row_open_through_an_implicit_is_solved_by_the_row_equation_2270`
    pub(crate) fn unify_rows(
        &mut self,
        rows: (
            &gandr_core_term::effect::EffectRow,
            &gandr_core_term::effect::EffectRow,
        ),
    ) -> Result<crate::elaboration::Unified, CheckRefusal>
    {
        let scope = self.intuitionistic_scope()?;
        Ok(self.deferrals.unify_rows(self.arena, scope, rows))
    }

    /// Declare the nominated hole `hole` at `at` a metavariable whose context
    /// is the intuitionistic binders open now.
    ///
    /// # Specification
    /// - requires: as [`crate::elaboration::Deferrals::nominate`].
    /// - ensures: as it, at the current depth.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a depth past any binder
    ///   count.
    /// - panics: none.
    /// - executable: none — the declaration is
    ///   [`crate::elaboration::Deferrals::nominate`]'s, checked by its own
    ///   specification; this call only reads the depth it is made at.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::elaboration::Deferrals::nominate`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_supplied_before_the_kernel_1216`
    pub(crate) fn nominate(
        &mut self,
        at: ValueId,
        hole: gandr_core_term::hole::HoleId,
    ) -> Result<(), CheckRefusal>
    {
        let scope = self.intuitionistic_scope()?;
        self.deferrals.nominate(at, hole, scope);
        Ok(())
    }

    /// The intuitionistic binders open now, as the count a metavariable's
    /// context and an equation are posed under.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn intuitionistic_scope(&self) -> Result<gandr_core_term::Binders, CheckRefusal>
    {
        u32::try_from(usize::from(self.depth(Zone::Intuitionistic)))
            .map(gandr_core_term::Binders::from)
            .map_err(|_overflow| CheckRefusal::MachineInvariant)
    }

    /// Record a code occurrence that needs no universe transport.
    ///
    /// # Specification
    /// - requires: this occurrence checks at its natural universe.
    /// - ensures: elaboration records an identity occurrence; ordinary checking
    ///   is unchanged. Neither mode writes the ordinary lift side table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — one shared code used at a higher and an equal
    ///   universe distinguishes an identity occurrence from a missing record.
    /// - witness: `gandr-core-checker::tests::elaboration::shared_code_occurrences_keep_distinct_transports`
    /// - witness: `conversion::tests::the_value_bridge_lifts_a_small_value_code_and_nothing_else`
    #[spec(
        captures: [count = self.lifts.len(), held = self.lifts.contains_key(&at)],
        ensures: self.lifts.len() == count && self.lifts.contains_key(&at) == held,
    )]
    pub(crate) fn record_unlifted(
        &mut self,
        at: ValueId,
    )
    {
        if let crate::elaboration::Emission::Recording(ref mut transports) = self.deferrals.emission
        {
            transports.record(at, crate::elaboration::CodeUse::Unchanged);
        }
    }

    /// How many code uses the elaboration recorded: zero outside elaboration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn code_uses(&self) -> crate::elaboration::CodeUses
    {
        self.deferrals.emission.recorded()
    }

    /// Record that the code `at` was checked at a universe above its own.
    ///
    /// # Specification
    /// - requires: the natural level is strictly below the target.
    /// - ensures: ordinary checking records this lift at `at`, replacing any
    ///   earlier record there. Elaboration appends an occurrence instead,
    ///   leaving the ordinary side table unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the value bridge on equal, lower and higher code
    ///   levels distinguishes recording a genuine lift from recording an
    ///   equality or refusal; readmission observes the resulting coercion;
    ///   shared uses distinguish occurrence-specific output from one transport
    ///   per source node.
    /// - witness: `conversion::tests::the_value_bridge_lifts_a_small_value_code_and_nothing_else`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    /// - witness: `gandr-core-checker::tests::elaboration::shared_code_occurrences_keep_distinct_transports`
    #[spec(
        requires: bool::from(lift.natural().lt(lift.target())),
        captures: [
            count = self.lifts.len(),
            held = self.lifts.contains_key(&at),
            expected = lift.clone(),
        ],
        ensures: match self.deferrals.emission {
            | crate::elaboration::Emission::Off => self.lifts.get(&at) == Some(&expected),
            | crate::elaboration::Emission::Recording(_) =>
                self.lifts.len() == count && self.lifts.contains_key(&at) == held,
        },
    )]
    pub(crate) fn record_lift(
        &mut self,
        at: ValueId,
        lift: Lift,
    )
    {
        match self.deferrals.emission {
            crate::elaboration::Emission::Off => {
                self.lifts.insert(at, lift);
            },
            crate::elaboration::Emission::Recording(ref mut transports) => {
                transports.record(at, crate::elaboration::CodeUse::Lifted(lift));
            },
        }
    }

    /// The function extensionalities the judgement decided, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn funexts(&self) -> &BTreeMap<ValueId, crate::funext::Funext>
    {
        &self.funexts
    }

    /// Record the components the judgement decided the `funext` at `at` by.
    ///
    /// # Specification
    /// - requires: `funext` is what [`crate::funext`] decided at `at`.
    /// - ensures: `at` has `funext` as its record, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decided funext crosses with exactly its recorded
    ///   components.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    #[spec(ensures: self.funexts.contains_key(&at))]
    pub(crate) fn record_funext(
        &mut self,
        at: ValueId,
        funext: crate::funext::Funext,
    )
    {
        self.funexts.insert(at, funext);
    }

    /// The values the value bridge coerced in to a patched type, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn coercions(&self) -> &BTreeMap<ValueId, crate::conversion::Coercion>
    {
        &self.coercions
    }

    /// Record that the value bridge coerced the value `at` in to a patched
    /// type, whose fixed fields it compared as `fixed` holds them.
    ///
    /// # Specification
    /// - requires: each field of `at` converts with the value `fixed` holds at
    ///   its label.
    /// - ensures: `at` has `fixed` as its coercion, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a base value at a patched type crosses as the
    ///   restriction to its free fields.
    /// - witness: `tests::module::a_base_value_at_a_patched_type_crosses_as_a_restriction_5578`
    #[spec(ensures: self.coercions.contains_key(&at))]
    pub(crate) fn record_coercion(
        &mut self,
        at: ValueId,
        fixed: crate::conversion::Coercion,
    )
    {
        self.coercions.insert(at, fixed);
    }

    /// The universe equivalences the judgement decided, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn equivalences(&self) -> &BTreeMap<ValueId, crate::equiv::Equivalence>
    {
        &self.equivalences
    }

    /// Record the evidence the judgement decided the `equiv` at `at` by.
    ///
    /// # Specification
    /// - requires: `equivalence` is what [`crate::equiv`] decided at `at`.
    /// - ensures: `at` has `equivalence` as its record, replacing an earlier
    ///   one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decided equivalence crosses with exactly its
    ///   recorded classifier and evidence.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_equiv_crosses_as_a_universe_path`
    #[spec(ensures: self.equivalences.contains_key(&at))]
    pub(crate) fn record_equivalence(
        &mut self,
        at: ValueId,
        equivalence: crate::equiv::Equivalence,
    )
    {
        self.equivalences.insert(at, equivalence);
    }

    /// The session statements the judgement decided, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flows(&self) -> &BTreeMap<ValueId, crate::flow::Statement>
    {
        &self.flows
    }

    /// Record the session statement the judgement decided at `at`.
    ///
    /// # Specification
    /// - requires: `statement` is what [`crate::flow`] decided at `at`.
    /// - ensures: `at` has `statement` as its record, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decided statement crosses with exactly its recorded
    ///   classifier and evidence.
    /// - witness: `tests::flow::statements_decide_by_the_engine_and_replay`
    #[spec(ensures: self.flows.contains_key(&at))]
    pub(crate) fn record_flow(
        &mut self,
        at: ValueId,
        statement: crate::flow::Statement,
    )
    {
        self.flows.insert(at, statement);
    }

    /// The forward and function flows the judgement decided, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn directed(&self) -> &BTreeMap<ValueId, crate::forward::Directed>
    {
        &self.directed
    }

    /// Record the forward or function flow the judgement decided at `at`.
    ///
    /// # Specification
    /// - requires: `directed` is what [`crate::forward`] decided at `at`.
    /// - ensures: `at` has `directed` as its record, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decided statement crosses with exactly its recorded
    ///   classifier, images and dialogues.
    /// - witness: `tests::forward::directed_statements_cross_and_replay`
    #[spec(ensures: self.directed.contains_key(&at))]
    pub(crate) fn record_directed(
        &mut self,
        at: ValueId,
        directed: crate::forward::Directed,
    )
    {
        self.directed.insert(at, directed);
    }

    /// The family each transport or ride above level zero formed its motive
    /// as, by node.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ModuleReport::motives`], which a batch run
    ///   copies from this table and a fill extends with it.
    /// - witness: `tests::flow::a_motive_above_level_zero_reads_its_binder_at_the_carriers_level_1837`
    /// - witness: `gandr-core-checker::tests::elaboration::a_filled_ride_above_level_zero_readmits_at_its_recorded_motive_1837`
    ///
    /// [`ModuleReport::motives`]: crate::ModuleReport::motives
    #[inline]
    #[must_use]
    pub const fn motives(&self) -> &BTreeMap<ComputationId, ValueTypeId>
    {
        &self.motives
    }

    /// The family the transport or ride at `at`, written over `written`,
    /// formed its motive as.
    ///
    /// # Specification
    /// - requires: `written` is the motive `at` is written over.
    /// - ensures: the family recorded at `at`, or `written` where none is.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_motive`].
    /// - witness: `tests::flow::a_motive_above_level_zero_reads_its_binder_at_the_carriers_level_1837`
    #[spec(ensures: |ret| ret == self.motives.get(&at).copied().unwrap_or(written))]
    #[inline]
    #[must_use]
    pub fn motive(
        &self,
        at: ComputationId,
        written: ValueTypeId,
    ) -> ValueTypeId
    {
        self.motives.get(&at).copied().unwrap_or(written)
    }

    /// Record the family the transport or ride at `at` formed its motive as.
    ///
    /// # Specification
    /// - requires: `family` is `at`'s written motive with its binder's decodes
    ///   read at the level of the universe its path or flow lives in.
    /// - ensures: `at` has `family` as its motive, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ride and a transport above level zero each form and
    ///   cross with the recorded family, and one at level zero records none.
    /// - witness: `tests::flow::a_motive_above_level_zero_reads_its_binder_at_the_carriers_level_1837`
    #[spec(ensures: self.motives.get(&at) == Some(&family))]
    pub(crate) fn record_motive(
        &mut self,
        at: ComputationId,
        family: ValueTypeId,
    )
    {
        self.motives.insert(at, family);
    }

    /// The payload type each send and each receive the judgement checked
    /// moves, by node.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ModuleReport::payloads`], which a run copies
    ///   from this table.
    /// - witness: `tests::judgement::session::a_received_value_crosses_as_an_assumption_1319`
    ///
    /// [`ModuleReport::payloads`]: crate::ModuleReport::payloads
    #[inline]
    #[must_use]
    pub const fn payloads(&self) -> &BTreeMap<ComputationId, ValueTypeId>
    {
        &self.payloads
    }

    /// Record the payload type the send or receive at `at` moves.
    ///
    /// # Specification
    /// - requires: `moved` is read where the action stands: the type a send's
    ///   value is checked at, or the type a receive opens its slot at.
    /// - ensures: `at` has a recorded type: the first recorded, when one node
    ///   is judged more than once.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a received value crosses as an assumption of the
    ///   recorded type, a sent one ascribed it, and the kernel checks the body
    ///   that reads each.
    /// - witness: `tests::judgement::session::a_received_value_crosses_as_an_assumption_1319`
    #[spec(ensures: self.payloads.contains_key(&at))]
    pub(crate) fn record_payload(
        &mut self,
        at: ComputationId,
        moved: ValueTypeId,
    )
    {
        let _first = self.payloads.entry(at).or_insert(moved);
    }

    /// The types each handler and capability scope the judgement checked was
    /// judged at, by node.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ModuleReport::handled`], which a run copies from
    ///   this table.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_deep_handler_crosses_as_the_fold_of_its_free_model_1624`
    ///
    /// [`ModuleReport::handled`]: crate::ModuleReport::handled
    #[inline]
    #[must_use]
    pub const fn handled(&self) -> &BTreeMap<ComputationId, crate::handler::Handled>
    {
        &self.handled
    }

    /// Record the types the handler or capability scope at `at` is judged at.
    ///
    /// # Specification
    /// - requires: `handled` is read in the handler's own context.
    /// - ensures: `at` has a record: the first recorded, when one node is
    ///   judged more than once.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handler crosses as the fold of its free model at
    ///   the recorded types, and the kernel checks the fold there.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_deep_handler_crosses_as_the_fold_of_its_free_model_1624`
    #[spec(ensures: self.handled.contains_key(&at))]
    pub(crate) fn record_handled(
        &mut self,
        at: ComputationId,
        handled: crate::handler::Handled,
    )
    {
        let _first = self.handled.entry(at).or_insert(handled);
    }

    /// The computations the judgement checked or synthesised at a returner
    /// over a row of operations, and the levels of those returners.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ModuleReport::rows`], which a run copies from
    ///   this record.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    ///
    /// [`ModuleReport::rows`]: crate::ModuleReport::rows
    #[inline]
    #[must_use]
    pub const fn rows(&self) -> &crate::program::Rows
    {
        &self.rows
    }

    /// Record that the judgement checks `at` against `expected`, when
    /// `expected` is a returner over a row of operations.
    ///
    /// # Specification
    /// - requires: `expected` is read in the context `at` is checked in.
    /// - ensures: `at` reads `expected`, and `expected` reads the level of its
    ///   result, when `expected` is such a returner whose level reads; the
    ///   first record stands when one node is checked more than once; nothing
    ///   changes otherwise.
    /// - panics: none.
    /// - executable: none — the record is the statement; the witness crosses
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration at a row crosses as a program of the
    ///   row's model at the recorded returner.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    pub(crate) fn record_checked_row(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    )
    {
        if let Maybe::Present(level) = self.row_level(expected) {
            self.rows
                .check(at, (expected, level), &mut self.gained_rows);
        }
    }

    /// Record that `at` synthesised `synthesised`, when it is a returner over
    /// a row of operations or `against` is one: the type `at` crosses to, or
    /// the bound of the bind whose body `at` is.
    ///
    /// # Specification
    /// - requires: `synthesised` is read in the context `at` is judged in.
    /// - ensures: `at` reads `synthesised` when it is such a returner, with the
    ///   level of its result when that level reads; `at` reads it without a
    ///   level when `against` is such a returner and `synthesised` is not; the
    ///   first record stands when one node is judged more than once; nothing
    ///   changes otherwise.
    /// - panics: none.
    /// - executable: none — the record is the statement; the witness crosses
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call of a declaration at a row binds its program
    ///   into the caller's, and a pure call at a row returns its value as a
    ///   program.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    pub(crate) fn record_synthesised_row(
        &mut self,
        at: ComputationId,
        (synthesised, against): (CompTypeId, Option<CompTypeId>),
    )
    {
        match self.row_level(synthesised) {
            Maybe::Present(level) => {
                self.rows
                    .synthesise(at, (synthesised, Some(level)), &mut self.gained_rows);
            },
            Maybe::Absent(_)
                if against.is_some_and(|ty| {
                    matches!(
                        crate::program::programmed(self.arena(), ty),
                        Maybe::Present(_)
                    )
                }) =>
            {
                self.rows
                    .synthesise(at, (synthesised, None), &mut self.gained_rows);
            },
            Maybe::Absent(_) => {},
        }
    }

    /// Record the level of `formed`'s result, when `formed` is a returner over
    /// a row of operations.
    ///
    /// # Specification
    /// - requires: `formed` is read in the context it is formed in.
    /// - ensures: `formed` reads the level of its result when it is such a
    ///   returner whose level reads; nothing changes otherwise.
    /// - panics: none.
    /// - executable: none — the record is the statement; the witness crosses
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared type at a row crosses as a returner of the
    ///   row's model at this level.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    pub(crate) fn record_formed_row(
        &mut self,
        formed: CompTypeId,
    )
    {
        if let Maybe::Present(level) = self.row_level(formed) {
            self.rows.form(formed, level, &mut self.gained_rows);
        }
    }

    /// Start the log of the rows records that the first run of a body gains.
    ///
    /// # Specification
    /// - ensures: [`Self::forget_rows`] forgets exactly the records that
    ///   [`Self::rows`] gains after this call.
    /// - panics: none.
    /// - executable: none — the log is the statement; the witness crosses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::program::Rows::forget`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_case_on_a_run_at_a_row_crosses_at_its_second_run_6672`
    pub(crate) fn open_rows(&mut self)
    {
        self.gained_rows.clear();
    }

    /// Forget each rows record gained since [`Self::open_rows`]: the second
    /// run of a body judges its elaborated nodes, and one node can stand in
    /// both bodies beneath other binders.
    ///
    /// # Specification
    /// - ensures: [`Self::rows`] holds no record that it gained since
    ///   [`Self::open_rows`], and every record that it held before.
    /// - panics: none.
    /// - executable: none — as [`Self::open_rows`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::program::Rows::forget`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_case_on_a_run_at_a_row_crosses_at_its_second_run_6672`
    pub(crate) fn forget_rows(&mut self)
    {
        self.rows.forget(self.gained_rows.drain(..));
    }

    /// The level of the result of `ty`, when `ty` is a returner over a row
    /// of operations: the level recorded for it, or the level it reads at.
    ///
    /// # Specification
    /// - ensures: present exactly when `ty` is such a returner and its level is
    ///   recorded or reads.
    /// - panics: none.
    /// - executable: none — the level reads the judgement's records, which a
    ///   predicate reads as the body does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record_formed_row`].
    /// - witness: `gandr-core-checker-bridge::bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    fn row_level(
        &self,
        ty: CompTypeId,
    ) -> Maybe<Level, crate::program::unprogrammed::Absent>
    {
        if let Maybe::Absent(absent) = crate::program::programmed(self.arena(), ty) {
            return Maybe::Absent(absent);
        }
        if let Some(level) = self.rows.level(ty) {
            return Maybe::Present(level.clone());
        }
        level_of(self, TypeNode::Computation(ty)).map_or(
            Maybe::Absent(crate::program::unprogrammed::Absent::NoReturner),
            Maybe::Present,
        )
    }

    /// The reflexivities the judgement checked, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reflexivities(&self) -> &BTreeMap<ValueId, crate::code::Reflexivity>
    {
        &self.reflexivities
    }

    /// Record the dialogues the judgement related the reflexivity at `at` to
    /// its endpoints by.
    ///
    /// # Specification
    /// - requires: `reflexivity` is what the endpoint condition recorded at
    ///   `at`.
    /// - ensures: `at` has `reflexivity` as its record, replacing an earlier
    ///   one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a checked reflexivity crosses with exactly its
    ///   recorded dialogues.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_reflexivity_crosses_with_the_dialogues_relating_its_endpoints`
    #[spec(ensures: self.reflexivities.contains_key(&at))]
    pub(crate) fn record_reflexivity(
        &mut self,
        at: ValueId,
        reflexivity: crate::code::Reflexivity,
    )
    {
        self.reflexivities.insert(at, reflexivity);
    }

    /// Record how the judgement decided the computation `at` stands for where
    /// a value is read. A value a refinement rewrote records its decision at
    /// the written value, which the elaboration rebuilds.
    ///
    /// # Specification
    /// - requires: `nesting` is what the rule at `at` decided.
    /// - ensures: the written value `at` stands for has `nesting` as its
    ///   decision, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested computation against a thunk type and against
    ///   an atom are each recorded as their rule decided.
    /// - witness: `module::tests::a_nested_computation_is_decided_by_its_expected_type`
    /// - witness: `tests::module::a_nested_run_elaborates_into_a_bind_before_its_region`
    /// - witness: `tests::native_formers::a_refined_arm_elaborates_its_nested_call_where_it_is_written_3483`
    #[spec(captures: written = self.written(at), ensures: self.nesting.get(&written) == Some(&nesting))]
    pub(crate) fn record_nesting(
        &mut self,
        at: ValueId,
        nesting: crate::nested::Nesting,
    )
    {
        let written = self.written(at);
        self.nesting.insert(written, nesting);
    }

    /// Every decision recorded since the last take: a run that holds one is
    /// a first run, whose verdict the elaborated body's second run replaces.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn nesting(&self) -> &BTreeMap<ValueId, crate::nested::Nesting>
    {
        &self.nesting
    }

    /// Take every decision recorded since the last take, leaving none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the decisions recorded since the last take, by node; none
    ///   remain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_nesting`]; a second
    ///   declaration's elaboration reads only its own decisions.
    /// - witness: `tests::module::a_nested_run_elaborates_into_a_bind_before_its_region`
    #[spec(ensures: self.nesting.is_empty())]
    pub(crate) fn take_nesting(&mut self) -> BTreeMap<ValueId, crate::nested::Nesting>
    {
        core::mem::take(&mut self.nesting)
    }

    /// Record that the value bridge carried the value `at` by `crossing`, at
    /// the written value `at` stands for.
    ///
    /// # Specification
    /// - requires: `crossing` names a kept map whose signature, at the
    ///   crossing's carriers, carries the type `at` synthesised to the type it
    ///   was checked against.
    /// - ensures: the written value `at` stands for crosses by `crossing`,
    ///   replacing an earlier record.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::keep_reducts`].
    /// - witness: `tests::module::a_model_crosses_to_an_included_theory_s_by_its_reduct`
    #[spec(captures: [kept = crossing.clone(), written = self.written(at)], ensures: self.crossings.get(&written) == Some(&kept))]
    pub(crate) fn record_crossing(
        &mut self,
        at: ValueId,
        crossing: gandr_core_term::Crossing,
    )
    {
        let written = self.written(at);
        self.crossings.insert(written, crossing);
    }

    /// Take every crossing recorded since the last take, leaving none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the crossings recorded since the last take, by node; none
    ///   remain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::keep_reducts`].
    /// - witness: `tests::module::a_model_crosses_to_an_included_theory_s_by_its_reduct`
    #[spec(ensures: self.crossings.is_empty())]
    pub(crate) fn take_crossings(&mut self) -> BTreeMap<ValueId, gandr_core_term::Crossing>
    {
        core::mem::take(&mut self.crossings)
    }

    /// Record that the record update `at` keeps its base's fields at `kept`,
    /// its overlay standing at every other label the update has. The record
    /// stands at the written value `at` stands for.
    ///
    /// # Specification
    /// - requires: `kept` is the base's labels the overlay does not write.
    /// - ensures: the written value `at` stands for keeps `kept`, replacing an
    ///   earlier record.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an update that overlays one field of two keeps the
    ///   other.
    /// - witness: `tests::module::a_record_update_builds_its_base_s_kept_fields_beside_its_overlay`
    #[spec(captures: [count = kept.len(), written = self.written(at)], ensures: self.updates.get(&written).map(Vec::len) == Some(count))]
    pub(crate) fn record_update(
        &mut self,
        at: ValueId,
        kept: Vec<gandr_kernel_term::FieldLabel>,
    )
    {
        let written = self.written(at);
        self.updates.insert(written, kept);
    }

    /// Record that the value `at` stands as its update by the record `overlay`,
    /// the update keeping `at`'s fields at `kept`: the coercion out of an
    /// element of a patched type, and the read of a field that the type fixes
    /// (#5579).
    ///
    /// # Specification
    /// - requires: `overlay` is a record of values that `at`'s patched type
    ///   fixes, and `kept` the labels of `at`'s free fields the record stands
    ///   at.
    /// - ensures: the written value `at` stands for crosses by the overlaid
    ///   crossing of `overlay`, and its update keeps `kept`, each replacing an
    ///   earlier record.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an element of a patched type at its base stands as
    ///   the record of its base's fields, and a selection of a fixed field
    ///   reads the value that the type fixes.
    /// - witness: `tests::module::an_element_of_a_patched_type_stands_at_its_base_as_its_record_5579`
    #[spec(captures: [count = kept.len(), written = self.written(at)], ensures: self.updates.get(&written).map(Vec::len) == Some(count)
        && self.crossings.get(&written).is_some_and(|crossing| crossing.operand == gandr_core_term::CrossedOperand::Overlaid(overlay)))]
    pub(crate) fn record_overlay(
        &mut self,
        at: ValueId,
        overlay: ValueId,
        kept: Vec<gandr_kernel_term::FieldLabel>,
    )
    {
        self.record_update(at, kept);
        self.record_crossing(at, gandr_core_term::Crossing {
            by: Maybe::Absent(()),
            carriers: Vec::new(),
            operand: gandr_core_term::CrossedOperand::Overlaid(overlay),
        });
    }

    /// Take every record update recorded since the last take, leaving none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the updates recorded since the last take, by node; none
    ///   remain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_update`].
    /// - witness: `tests::module::a_record_update_builds_its_base_s_kept_fields_beside_its_overlay`
    #[spec(ensures: self.updates.is_empty())]
    pub(crate) fn take_updates(&mut self) -> BTreeMap<ValueId, Vec<gandr_kernel_term::FieldLabel>>
    {
        core::mem::take(&mut self.updates)
    }

    /// Record the derivation the judgement related the path endpoints `left`
    /// and `right` by, where a type conversion met them.
    ///
    /// # Specification
    /// - requires: `decisions` is the machine's convertible trace from `left`
    ///   to `right`.
    /// - ensures: the pair has `decisions` as its derivation, replacing an
    ///   earlier one, until the next take.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ascription relating compound endpoints through a
    ///   definition's body keeps the pair and its derivation for the accepted
    ///   declaration.
    /// - witness: `module::tests::an_ascription_keeps_the_endpoints_it_related`
    #[spec(ensures: self.relating.contains_key(&(left, right)))]
    pub(crate) fn record_relation(
        &mut self,
        left: ValueId,
        right: ValueId,
        decisions: Vec<
            gandr_kernel_conversion_trace::ConversionDecision<gandr_core_nbe::TraceNode>,
        >,
    )
    {
        self.relating.insert(
            (left, right),
            crate::code::EndpointRelation::new(left, right, decisions),
        );
    }

    /// Take every endpoint pair recorded since the last take, leaving none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the pairs recorded since the last take, ascending by pair;
    ///   none remain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_relation`]; a second
    ///   declaration keeps only the pairs its own judgement related.
    /// - witness: `module::tests::an_ascription_keeps_the_endpoints_it_related`
    #[spec(ensures: self.relating.is_empty())]
    pub(crate) fn take_relating(&mut self) -> Vec<crate::code::EndpointRelation>
    {
        core::mem::take(&mut self.relating).into_values().collect()
    }

    /// Keep `relations` as the endpoint pairs the accepted declaration at
    /// `constant` related.
    ///
    /// # Specification
    /// - requires: `relations` is what [`CheckingContext::take_relating`] took
    ///   after the judgement at `constant` accepted.
    /// - ensures: `constant` has `relations` as its pairs, replacing earlier
    ///   ones, when any was related; otherwise nothing changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_relation`].
    /// - witness: `module::tests::an_ascription_keeps_the_endpoints_it_related`
    #[spec(captures: entry = relations.len(), ensures: entry == 0 || self.relations.get(&constant).map(Vec::len) == Some(entry))]
    pub(crate) fn keep_relations(
        &mut self,
        constant: ConstantIndex,
        relations: Vec<crate::code::EndpointRelation>,
    )
    {
        if !relations.is_empty() {
            self.relations.insert(constant, relations);
        }
    }

    /// The path endpoint pairs each accepted declaration's type conversions
    /// related, by position, with each derivation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relations(&self) -> &BTreeMap<ConstantIndex, Vec<crate::code::EndpointRelation>>
    {
        &self.relations
    }

    /// Record that the judgement checks `refined` in the place of `at`: an arm
    /// or a case refined by a solved variable ([`crate::solution`]).
    ///
    /// # Specification
    /// - requires: `refined` is the term the judgement checks where `at` is
    ///   read, in the same context, its rewrites in the order they were made.
    /// - ensures: `at` has `refined`'s term as its refinement, replacing an
    ///   earlier one, until the next take. Each rewrite stands for the written
    ///   node its source stands for, and each generalising lambda for the
    ///   binder it copies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arm refined by its equation crosses refined, and
    ///   the kernel admits it. A refined arm that holds a nested call
    ///   elaborates the call where it is written.
    /// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
    /// - witness: `tests::native_formers::a_refined_arm_elaborates_its_nested_call_where_it_is_written_3483`
    #[spec(ensures: self.restating.get(&TermNode::Computation(at)) == Some(&TermNode::Computation(refined.term)))]
    pub(crate) fn record_refinement(
        &mut self,
        at: ComputationId,
        refined: &crate::solution::Refined,
    )
    {
        let _earlier = self.restating.insert(
            TermNode::Computation(at),
            TermNode::Computation(refined.term),
        );
        self.readings.record(refined);
    }

    /// Record that the kernel reads `restated` in the place of the value `at`:
    /// a constructor at its stated application, ascribed the annotation it is
    /// written at, or `*{}` as the record of no fields at a patched type that
    /// fixes every field of its base.
    ///
    /// # Specification
    /// - requires: `restated` ascribes the constructor at the application it
    ///   states to `at`'s annotation, and the two types convert; or `at` is the
    ///   unit and `restated` the record of no fields.
    /// - ensures: `at` has `restated` as its refinement, replacing an earlier
    ///   one, until the next take.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor annotated at a call that computes its
    ///   stated index crosses restated, and the kernel admits it; so does `*{}`
    ///   at a patched type with no free field.
    /// - witness: `tests::native_formers::a_constructor_annotated_at_a_call_meets_its_stated_index_3627`
    /// - witness: `tests::native_formers::a_patched_type_with_no_free_field_holds_the_empty_record_5680`
    #[spec(ensures: self.restating.get(&TermNode::Value(at)) == Some(&TermNode::Value(restated)))]
    pub(crate) fn record_restated(
        &mut self,
        at: ValueId,
        restated: ValueId,
    )
    {
        let _earlier = self
            .restating
            .insert(TermNode::Value(at), TermNode::Value(restated));
    }

    /// Record that the kernel reads `restated` in the place of the split `at`:
    /// the dependent split of `at`'s scrutinee and body at the type `at` has.
    ///
    /// # Specification
    /// - requires: `at` splits a scrutinee whose type unfolds to a dependent
    ///   pair, at the ambient motive, and `restated` is the dependent split of
    ///   the same scrutinee and body at that motive.
    /// - ensures: `at` has `restated` as its refinement, replacing an earlier
    ///   one, until the next take.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a split by position of a pair a call computes crosses
    ///   restated, and the kernel admits it.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_split_by_position_of_a_computed_pair_reads_its_fibre_in_both_checkers_5290`
    #[spec(ensures: self.restating.get(&TermNode::Computation(at)) == Some(&TermNode::Computation(restated)))]
    pub(crate) fn record_restated_split(
        &mut self,
        at: ComputationId,
        restated: ComputationId,
    )
    {
        let _earlier = self
            .restating
            .insert(TermNode::Computation(at), TermNode::Computation(restated));
    }

    /// The written value `at` stands for: the value a refinement rewrote into
    /// `at`, read back to the body as written, or `at` itself.
    ///
    /// # Specification
    /// - ensures: as [`crate::solution::Written::value`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_refinement`].
    /// - witness: `tests::native_formers::a_refined_arm_elaborates_its_nested_call_where_it_is_written_3483`
    #[spec(ensures: |ret| ret == self.readings.value(at))]
    #[must_use]
    pub(crate) fn written(
        &self,
        at: ValueId,
    ) -> ValueId
    {
        self.readings.value(at)
    }

    /// Where `at` stands in the term as written, read through every
    /// refinement since the last take (#3694).
    ///
    /// # Specification
    /// - ensures: as [`crate::solution::Written::standing`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::solution::Written::standing`].
    /// - witness: `tests::native_formers::a_refusal_inside_a_refined_arm_names_the_written_term_3694`
    #[spec(ensures: |ret| ret == self.readings.standing(at))]
    #[must_use]
    pub(crate) fn standing(
        &self,
        at: TermNode,
    ) -> crate::solution::Standing
    {
        self.readings.standing(at)
    }

    /// Open the binder of the lambda or bind `at`, which the binders' innermost
    /// is: a generalising one's binder stands for the binder it copies.
    ///
    /// # Specification
    /// - requires: the binder of `at` is the innermost open.
    /// - ensures: as [`crate::solution::Written::open`] at the binder's place.
    /// - panics: none.
    /// - executable: none — the record's open copies have no observer short of
    ///   a typing read back, which the witness reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::solution::Written::open`].
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    pub(crate) fn open_copy(
        &mut self,
        at: ComputationId,
    )
    {
        let depth = self.depth(Zone::Intuitionistic);
        let place = BinderDepth::from(usize::from(depth).saturating_sub(1));
        self.readings.open(at, place);
    }

    /// Close the copies past the binders open now.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`crate::solution::Written::close`] at the depth now.
    /// - panics: none.
    /// - executable: none — as [`CheckingContext::open_copy`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::solution::Written::close`].
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    pub(crate) fn closed_binder(&mut self)
    {
        let depth = self.depth(Zone::Intuitionistic);
        self.readings.close(depth);
    }

    /// Take every restatement recorded since the last take, leaving none, and
    /// forget what reads the refinements among them back.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the restatements recorded since the last take, ascending by
    ///   the node restated; none remain, and no node reads back.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_refinement`].
    /// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
    #[spec(ensures: self.restating.is_empty())]
    pub(crate) fn take_restating(&mut self) -> Vec<(TermNode, TermNode)>
    {
        self.readings.clear();
        core::mem::take(&mut self.restating).into_iter().collect()
    }

    /// Keep `restatements` as the restated nodes of the accepted declaration at
    /// `constant`.
    ///
    /// # Specification
    /// - requires: `restatements` is what [`CheckingContext::take_restating`]
    ///   took after the judgement at `constant` accepted.
    /// - ensures: `constant` has `restatements` as its restated nodes,
    ///   replacing earlier ones, when any was restated; otherwise nothing
    ///   changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CheckingContext::record_refinement`].
    /// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
    #[spec(captures: entry = restatements.len(), ensures: entry == 0 || self.restatements.get(&constant).map(Vec::len) == Some(entry))]
    pub(crate) fn keep_restatements(
        &mut self,
        constant: ConstantIndex,
        restatements: Vec<(TermNode, TermNode)>,
    )
    {
        if !restatements.is_empty() {
            self.restatements.insert(constant, restatements);
        }
    }

    /// The restated nodes of each accepted declaration, by position, each
    /// beside the node the kernel reads in its place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn restatements(&self) -> &BTreeMap<ConstantIndex, Vec<(TermNode, TermNode)>>
    {
        &self.restatements
    }

    /// Keep `laws` as the laws the declaration at `constant` rests its folds
    /// on, before it is judged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` has `laws` as its laws when any is named;
    ///   otherwise nothing changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::respect::respected`]: the fold over the
    ///   circle reads the laws its declaration names.
    /// - witness: `tests::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
    #[spec(captures: entry = laws.len(), ensures: entry == 0 || self.laws.get(&constant).map(Vec::len) == Some(entry))]
    pub(crate) fn keep_laws(
        &mut self,
        constant: ConstantIndex,
        laws: Vec<ConstantIndex>,
    )
    {
        if !laws.is_empty() {
            self.laws.insert(constant, laws);
        }
    }

    /// The laws the declaration under judgement rests its folds on: none
    /// before any is admitted.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn admitted_laws(&self) -> &[ConstantIndex]
    {
        match self.admitted {
            Maybe::Present(constant) => self.laws.get(&constant).map_or(&[], Vec::as_slice),
            Maybe::Absent(_) => &[],
        }
    }

    /// The laws each lawful declaration's folds rest on, by position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn laws(&self) -> &BTreeMap<ConstantIndex, Vec<ConstantIndex>>
    {
        &self.laws
    }

    /// Keep `rules` as the rules of the operation the declaration at
    /// `constant` lowered from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` has `rules` when any is written; otherwise nothing
    ///   changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rules cross to the kernel with their declaration.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::an_operations_rules_cross_at_kernel_positions_and_the_kernel_decides_them`
    #[spec(captures: entry = rules.rules().len(), ensures: entry == 0 || self.operation_rules.get(&constant).map(|kept| kept.rules().len()) == Some(entry))]
    pub(crate) fn keep_operation_rules(
        &mut self,
        constant: ConstantIndex,
        rules: gandr_kernel_term::OperationRules,
    )
    {
        if !rules.rules().is_empty() {
            self.operation_rules.insert(constant, rules);
        }
    }

    /// Keep `covers` as the derivations of the matches in the body of the
    /// declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` has `covers` when any is given; otherwise nothing
    ///   changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the derivations cross to the kernel with their
    ///   declaration.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_matches_derivation_crosses_and_the_kernel_replays_it_5104`
    #[spec(captures: entry = covers.len(), ensures: entry == 0 || self.covers.get(&constant).map(Vec::len) == Some(entry))]
    pub(crate) fn keep_covers(
        &mut self,
        constant: ConstantIndex,
        covers: Vec<(ComputationId, gandr_kernel_term::cover::Cover)>,
    )
    {
        if !covers.is_empty() {
            self.covers.insert(constant, covers);
        }
    }

    /// The matches of each declaration's body with their derivations, by
    /// position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn covers(
        &self
    ) -> &BTreeMap<ConstantIndex, Vec<(ComputationId, gandr_kernel_term::cover::Cover)>>
    {
        &self.covers
    }

    /// The rules of the operation the declaration under judgement lowered
    /// from: none before any is admitted, and none for a declaration no
    /// operation's rules wrote.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn admitted_rules(&self) -> &[gandr_kernel_term::OperationRule]
    {
        match self.admitted {
            Maybe::Present(constant) => self
                .operation_rules
                .get(&constant)
                .map_or(&[], gandr_kernel_term::OperationRules::rules),
            Maybe::Absent(_) => &[],
        }
    }

    /// The rules of the operation each ruled declaration lowered from, by
    /// position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn operation_rules(
        &self
    ) -> &BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>
    {
        &self.operation_rules
    }

    /// The declaration that holds each built-in role.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn builtins(&self) -> &BTreeMap<gandr_kernel_term::Builtin, ConstantIndex>
    {
        &self.builtins
    }

    /// Keep `signature` as the stage signature of the definition at
    /// `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` has `signature` when it binds a stage; otherwise
    ///   nothing changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call reads the signature to instantiate the
    ///   definition's stages, and it crosses to the kernel with it.
    /// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
    #[spec(captures: entry = signature.bounds().is_empty(), ensures: entry || self.stage_signatures.contains_key(&constant))]
    pub(crate) fn keep_stage_signature(
        &mut self,
        constant: ConstantIndex,
        signature: gandr_kernel_term::StageSignature,
    )
    {
        if !signature.bounds().is_empty() {
            self.stage_signatures.insert(constant, signature);
        }
    }

    /// The stage signature of each definition quantified over stages, by
    /// position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stage_signatures(
        &self
    ) -> &BTreeMap<ConstantIndex, gandr_kernel_term::StageSignature>
    {
        &self.stage_signatures
    }

    /// The native universe path each univalence statement the judgement
    /// decided derives, each path product it judged elaborates to, and the
    /// value each fill's induction returns, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn natives(&self) -> &BTreeMap<ValueId, ValueId>
    {
        &self.natives
    }

    /// Record the native path the judgement derived for the `ua` or
    /// elaborated for the path product at `at`.
    ///
    /// # Specification
    /// - requires: `path` is the path [`crate::ua::decide`] derived or
    ///   [`crate::product::native`] elaborated at `at`.
    /// - ensures: `at` has `path` as its record, replacing an earlier one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decided statement and a judged product cross as
    ///   exactly their recorded paths, which the kernel admits.
    /// - witness: `tests::ua::a_written_statement_derives_the_path_at_its_stratum`
    /// - witness: `tests::product::a_product_of_written_paths_elaborates_to_the_native_product`
    #[spec(ensures: self.natives.get(&at) == Some(&path))]
    pub(crate) fn record_native(
        &mut self,
        at: ValueId,
        path: ValueId,
    )
    {
        self.natives.insert(at, path);
    }

    /// Record the induction `realised` the judgement built for the fill at
    /// `at`: the elaboration stands the fill as it, evaluation reads the fill
    /// as what it returns, and the bridge carries the fill across as it.
    ///
    /// # Specification
    /// - requires: `realised` is the induction [`crate::fill::realise`] built
    ///   at `at`, under `at`'s binders.
    /// - ensures: the written value `at` stands for has
    ///   [`crate::nested::Nesting::Filled`] of `realised` as its decision; the
    ///   code definitions read `realised` at `at`; the natives hold, at `at`,
    ///   the value `realised` returns. Each replaces an earlier record.
    /// - provides: the one place a fill's induction is recorded, so the three
    ///   readings of it never disagree.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill over a `here` cell in a type converts with
    ///   `here`, and the kernel replays the declaration holding it.
    /// - witness: `fill::tests::a_realised_fill_converts_with_here_in_a_type`
    #[spec(ensures: self.natives.contains_key(&at))]
    pub(crate) fn record_fill(
        &mut self,
        at: ValueId,
        realised: gandr_core_term::ComputationId,
    )
    {
        self.record_nesting(at, crate::nested::Nesting::Filled(realised));
        self.definitions.realise(at, realised);
        let returned = self.arena.value_returned(realised);
        self.natives.insert(at, returned);
    }

    /// Trace the conversion of two computations as
    /// [`CodeDefinitions::trace_conversion`] does, over the definitions this
    /// context holds.
    ///
    /// # Specification
    /// - requires: as [`CodeDefinitions::trace_conversion`].
    /// - ensures: as [`CodeDefinitions::trace_conversion`], over this context's
    ///   arena and definitions.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`CodeDefinitions::trace_conversion`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CodeDefinitions::trace_conversion`].
    /// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Undecided { at: found }) if found == at))]
    pub(crate) fn trace_conversion(
        &self,
        at: ValueId,
        claim: (
            gandr_core_term::ComputationId,
            gandr_core_term::ComputationId,
        ),
        open: crate::code::OpenBinders,
    ) -> Result<
        Maybe<
            Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>,
            crate::code::converted::Absent,
        >,
        CheckRefusal,
    >
    {
        self.definitions
            .trace_conversion(self.arena(), at, claim, open)
    }

    /// Evaluate the closed claim `claim` as [`CodeDefinitions::evaluate_claim`]
    /// does, over the definitions this context holds.
    ///
    /// # Specification
    /// - requires: as [`CodeDefinitions::evaluate_claim`].
    /// - ensures: as [`CodeDefinitions::evaluate_claim`], over this context's
    ///   arena and definitions.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`CodeDefinitions::evaluate_claim`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CodeDefinitions::evaluate_claim`].
    /// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(ref evaluation)) => self.arena().value(evaluation.returned()).is_some()
            && self.arena().value(evaluation.normal()).is_some(),
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    pub(crate) fn evaluate_claim(
        &mut self,
        claim: ValueId,
    ) -> Result<Maybe<crate::code::Evaluation, crate::code::evaluated::Absent>, CheckRefusal>
    {
        self.definitions.evaluate_claim(self.arena, claim)
    }

    /// Read the closed claim `claim` as [`CodeDefinitions::read_claim`] does,
    /// over the definitions this context holds.
    ///
    /// # Specification
    /// - requires: as [`CodeDefinitions::read_claim`].
    /// - ensures: as [`CodeDefinitions::read_claim`], over this context's arena
    ///   and definitions.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`CodeDefinitions::read_claim`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`CodeDefinitions::read_claim`].
    /// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
    #[spec(ensures: |ret| match ret {
        | Ok(crate::code::Reading::Returned(ref evaluation)) => self.arena().value(evaluation.returned()).is_some(),
        | Ok(crate::code::Reading::Stuck(ref reduction)) => self.arena().value(reduction.normal()).is_some(),
        | Err(_) => true,
    })]
    pub(crate) fn read_claim(
        &mut self,
        claim: ValueId,
    ) -> Result<crate::code::Reading, CheckRefusal>
    {
        self.definitions.read_claim(self.arena, claim)
    }

    /// The value type `value_type` stands for at its head: a decode of a code
    /// constant with a body read as the type the body denotes, and a sealed
    /// atom inside its seal read as its representation, until the head is
    /// anything else.
    ///
    /// # Specification
    /// - requires: `value_type` is formed.
    /// - ensures: `value_type` itself unless its head is a decode of a constant
    ///   with a body or a manifest atom; otherwise the decode of that body at
    ///   the decode's level, or the atom's representation, read again. A body
    ///   is defined at the universe its constant was declared at, so the decode
    ///   is at the body's own level. Each unfolding is certified by the
    ///   normaliser's conversion and its constant logged as consulted.
    /// - provides: the weak head every rule that reads a type's former reads.
    /// - fails: [`CheckRefusal::Undecided`] at a code whose unfolding the
    ///   machine did not certify; [`CheckRefusal::DanglingNode`] for a node
    ///   that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — an unfolding was not certified.
    /// - [`CheckRefusal::DanglingNode`] — a node does not resolve.
    ///
    /// # Termination
    /// - reason: the `loop` below takes one unfolding per turn, not recursion.
    /// - measure: a representation names only atoms admitted before its own, so
    ///   a chain of manifest atoms descends in position; a chain of code
    ///   unfoldings is bounded as [`Self::whnf_code`]'s is.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rigid formers and decodes through defined codes are
    ///   observed by conversion, including a static instance; a sealed atom
    ///   inside and outside its seal separates reading through from keeping it
    ///   rigid.
    /// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    /// - witness: `module::tests::a_sealed_member_checks_at_the_representation_inside`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|head|
        value_type_view(self.arena, head).is_ok()
            && (matches!(value_type_view(self.arena, value_type), Ok(ValueTypeView::Element { .. } | ValueTypeView::Abstract(_))) || head == value_type)))]
    pub(crate) fn whnf_value_type(
        &mut self,
        value_type: ValueTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let mut head = value_type;
        loop {
            let (code, target) = match value_type_view(self.arena, head)? {
                ValueTypeView::Element { code, target } => (code, target.clone()),
                ValueTypeView::Abstract(atom) => match self.manifest(atom) {
                    Maybe::Present(representation) => {
                        head = representation;
                        continue;
                    },
                    Maybe::Absent(_) => return Ok(head),
                },
                ValueTypeView::Data { .. }
                | ValueTypeView::Record(_)
                | ValueTypeView::Patched { .. }
                | ValueTypeView::Stack { .. }
                | ValueTypeView::Capability { .. }
                | ValueTypeView::Buffer
                | ValueTypeView::Qubit
                | ValueTypeView::Row
                | ValueTypeView::RowTail(_)
                | ValueTypeView::PathUniverse(..)
                | ValueTypeView::Path { .. }
                | ValueTypeView::Bridge { .. }
                | ValueTypeView::Flow { .. }
                | ValueTypeView::Run(_)
                | ValueTypeView::Prefix(_)
                | ValueTypeView::Dialogue(_)
                | ValueTypeView::Web
                | ValueTypeView::Sum(_)
                | ValueTypeView::List(_)
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Character
                | ValueTypeView::Float64
                | ValueTypeView::Fixed(_)
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Universe { .. }
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Product(_)
                | ValueTypeView::Sigma { .. }
                | ValueTypeView::StaticPi { .. }
                | ValueTypeView::Session(_)
                | ValueTypeView::Staged { .. }
                | ValueTypeView::Kept { .. }
                | ValueTypeView::World(_)
                | ValueTypeView::Unknown => return Ok(head),
            };
            let Maybe::Present(body) = self.unfold(code)?
            else {
                return Ok(head);
            };
            head = self.arena.value_type_element(body, target);
        }
    }

    /// The type of words the path type `Path[.A = carrier](left, right)` reads
    /// as: the declaration whose free cells loop at a point both endpoints
    /// spell, over the parameterless data type `carrier` is.
    ///
    /// # Specification
    /// - requires: `carrier` is formed.
    /// - ensures: `Some(words)` exactly when `carrier` is a parameterless data
    ///   type as written, `words` an admitted signature whose cells are over
    ///   it, and `left` and `right` each a constructor term of that type
    ///   spelling the cells' point; the words' signature is then logged as
    ///   consulted. The kernel reads the same words, the carrier as written
    ///   (`Presentations::words`), and admission keeps one per point.
    /// - provides: the identification every reader of a path type shares: a
    ///   word's check at its path, a case and a descent over a path, and
    ///   conversion between the two.
    /// - fails: [`CheckRefusal::DanglingNode`] for a carrier that does not
    ///   resolve, or one outside the fragment.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop checks at its path, a fold over a
    ///   path splits its words, and both checkers admit the same declarations.
    /// - witness: `tests::native_formers::a_loop_is_a_word_at_its_path_in_both_checkers`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |words| words.is_none_or(|words| self.data_signatures.get(&words).is_some_and(|signature| signature.presentation().cells().is_some()))))]
    pub(crate) fn words(
        &mut self,
        carrier: ValueTypeId,
        (left, right): (ValueId, ValueId),
    ) -> Result<Option<ConstantIndex>, CheckRefusal>
    {
        // The view refuses a carrier that does not resolve; the reading itself
        // is the one every reader of a path type shares.
        let _view = value_type_view(self.arena, carrier)?;
        let found = match gandr_core_term::identified_words(
            self.arena,
            &self.data_signatures,
            carrier,
            (left, right),
        ) {
            Maybe::Present(words) => Some(words),
            Maybe::Absent(gandr_core_term::unworded::Absent::Unlooped) => None,
        };
        if let Some(words) = found {
            let _logged = self.consult_data(words);
        }
        Ok(found)
    }

    /// `value_type`, or the data type of the words it reads as when its weak
    /// head is a path type at a looped point ([`Self::words`]).
    ///
    /// # Specification
    /// - requires: `value_type` is formed.
    /// - ensures: a fresh `Data(words, [])` exactly when the weak head is
    ///   `Path[.A = carrier](left, right)` and [`Self::words`] reads it as
    ///   `words`; `value_type` itself otherwise.
    /// - provides: the reading of a scrutinee's type and of a fold's domain.
    /// - fails: as [`Self::whnf_value_type`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::words`].
    /// - witness: `tests::native_formers::a_loop_is_a_word_at_its_path_in_both_checkers`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|read| read == value_type || matches!(value_type_view(self.arena, read), Ok(ValueTypeView::Data { arguments: [], .. }))))]
    pub(crate) fn identified(
        &mut self,
        value_type: ValueTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let head = self.whnf_value_type(value_type)?;
        if let ValueTypeView::Path {
            carrier,
            left,
            right,
        } = value_type_view(self.arena, head)?
            && let Some(words) = self.words(carrier, (left, right))?
        {
            return Ok(self.arena.value_type_data(words, Vec::new()));
        }
        Ok(value_type)
    }

    /// The computation type `comp_type` stands for at its head, as
    /// [`Self::whnf_value_type`] reads a value type.
    ///
    /// # Specification
    /// - requires: `comp_type` is formed.
    /// - ensures: `comp_type` itself unless its head is a decode of a constant
    ///   with a body; otherwise the decode of that body at the decode's level,
    ///   read again. A computation code is never lifted: the judgement refuses
    ///   one checked above its level.
    /// - provides: the weak head every rule that reads a computation type's
    ///   former reads.
    /// - fails: as [`Self::whnf_value_type`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — an unfolding was not certified.
    /// - [`CheckRefusal::DanglingNode`] — a node does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a computation decode and rigid returner or arrow
    ///   expose the head through checking and readmission; a wrong head or
    ///   altered rigid id changes these results. Arbitrary reduction lengths
    ///   are outside these finite examples.
    /// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|head|
        comp_type_view(self.arena, head).is_ok()
            && (matches!(comp_type_view(self.arena, comp_type), Ok(CompTypeView::Element { .. })) || head == comp_type)))]
    pub(crate) fn whnf_comp_type(
        &mut self,
        comp_type: CompTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let mut head = comp_type;
        loop {
            let CompTypeView::Element { code, target } = comp_type_view(self.arena, head)?
            else {
                return Ok(head);
            };
            let target = target.clone();
            let Maybe::Present(body) = self.unfold(code)?
            else {
                return Ok(head);
            };
            head = self.arena.comp_type_element(body, target);
        }
    }

    /// The reduct of one certified step at the code `code`'s head.
    ///
    /// # Specification
    /// - requires: `code` stands beneath the binders the judgement is under.
    /// - ensures: the reduct [`CodeDefinitions::reduce`] gives `code` — a
    ///   constant's body, a static definition at a saturated instance, a static
    ///   redex — its step certified by the normaliser's conversion beneath the
    ///   context's binders and an unfolded definition logged as consulted;
    ///   nothing for any other code. A reduct is another node than `code`, and
    ///   resolves. The first unfold of a code certifies its step and holds it;
    ///   a later unfold of that code gives the held reduct, mints nothing and
    ///   logs the consult again.
    /// - fails: [`CheckRefusal::Undecided`] when the machine does not certify
    ///   the step; [`CheckRefusal::DanglingNode`] for a code that does not
    ///   resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a constant's δ-step, a static instance's
    ///   δβ-step, and a rigid code; the certification is the normaliser's,
    ///   witnessed where it is defined.
    /// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
    /// - witness: `context::tests::a_second_unfold_of_a_code_takes_its_held_step`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(reduct)) => reduct != code && self.arena.value(reduct).is_some(),
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    pub(crate) fn unfold(
        &mut self,
        code: ValueId,
    ) -> Result<Maybe<ValueId, unfolding::Absent>, CheckRefusal>
    {
        let (reduct, unfolded) = if let Some(&held) = self.unfolded.get(&code) {
            held
        }
        else {
            let Maybe::Present(step) = self.definitions.reduce(self.arena, code)?
            else {
                return Ok(Maybe::Absent(unfolding::Absent::Rigid));
            };
            let certificate = self.definitions.certify(self.arena, step)?;
            let held = (certificate.reduct(), certificate.unfolded());
            let _replaced = self.unfolded.insert(code, held);
            held
        };
        if let Unfolded::Definition(constant) = unfolded {
            let _answer = self.consult(constant);
        }
        Ok(Maybe::Present(reduct))
    }

    /// The code `code` reduces to at its head: [`Self::unfold`] taken until
    /// it gives nothing, an ascription read as the value it ascribes.
    ///
    /// # Specification
    /// - requires: as [`Self::unfold`].
    /// - ensures: `code` itself when no step fires at its head, otherwise the
    ///   last reduct of the chain of certified steps and ascriptions passed;
    ///   the result resolves in the arena. An ascription passed takes no
    ///   certificate: the bridge crosses its value alone, so the kernel never
    ///   meets it. That no step fires at the result is not restated executably:
    ///   deciding it is another step, which mints into the arena.
    /// - fails: as [`Self::unfold`].
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `loop` below takes one certified step or passes one
    ///   ascription per turn, not recursion.
    /// - measure: the static normal form's distance: each step reduces a δ- or
    ///   β-redex of a well-formed code, and the judgement's step allowance
    ///   bounds every certificate's evaluation; an ascription's value is minted
    ///   before it, so passing one descends the arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a rigid head, a chain of two constants,
    ///   and a static definition that does not reduce short of its arguments.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|head| self.arena.value(head).is_some()))]
    pub(crate) fn whnf_code(
        &mut self,
        code: ValueId,
    ) -> Result<ValueId, CheckRefusal>
    {
        let mut head = code;
        loop {
            if let Some(&Value::Ascribe { value, .. }) = self.arena.value(head) {
                head = value;
                continue;
            }
            match self.unfold(head)? {
                Maybe::Present(reduct) => head = reduct,
                Maybe::Absent(_) => return Ok(head),
            }
        }
    }

    /// The level of the universe a closed code `code` inhabits, read off the
    /// code: a quote's type's level, a constant's declared universe.
    ///
    /// # Specification
    /// - requires: `code` is an accepted declaration body; `otherwise` is the
    ///   fallback level when its syntax exposes no natural level.
    /// - ensures: the level of the quoted type for a quote, the level of the
    ///   universe a constant was declared at for a constant, and `otherwise`
    ///   for any other code.
    /// - fails: [`CheckRefusal::DanglingNode`] or the refusal reading a quoted
    ///   type's level gives.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted and named type codes at equal and increased
    ///   declaration levels expose their natural level through the inserted
    ///   lift and independent readmission; other syntax uses the fallback,
    ///   without a claim that it independently reveals a classifier.
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    /// - witness: `gandr-core-checker-bridge::bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    #[spec(ensures: |ret| match self.arena.value(code) {
        | None => ret == Err(CheckRefusal::DanglingNode { node: CoreNode::Term(TermNode::Value(code)) }),
        | Some(&Value::Constant(constant)) => match self.signature(constant) {
            | Maybe::Present(declared) => match value_type_view(self.arena, declared.id()) {
                | Ok(ValueTypeView::Universe { level, .. }) => ret.as_ref() == Ok(level),
                | Ok(_) => ret.as_ref() == Ok(otherwise),
                | Err(refusal) => ret == Err(CheckRefusal::from(refusal)),
            },
            | Maybe::Absent(_) => ret.as_ref() == Ok(otherwise),
        },
        | Some(&(Value::Quote(_) | Value::QuoteComputation(_))) => true,
        | Some(_) => ret.as_ref() == Ok(otherwise),
    })]
    fn code_level(
        &mut self,
        code: ValueId,
        otherwise: &Level,
    ) -> Result<Level, CheckRefusal>
    {
        let Some(node) = self.arena.value(code)
        else {
            return Err(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(code)),
            });
        };
        match *node {
            Value::Quote(quoted) => level_of(self, TypeNode::Value(quoted)),
            Value::QuoteComputation(quoted) => level_of(self, TypeNode::Computation(quoted)),
            Value::Constant(constant) => match self.consult(constant) {
                Maybe::Present(declared) => match value_type_view(self.arena, declared.id())? {
                    ValueTypeView::Universe { level, .. } => Ok(level.clone()),
                    ValueTypeView::PathUniverse(..)
                    | ValueTypeView::Path { .. }
                    | ValueTypeView::Bridge { .. }
                    | ValueTypeView::Flow { .. }
                    | ValueTypeView::Run(_)
                    | ValueTypeView::Prefix(_)
                    | ValueTypeView::Dialogue(_)
                    | ValueTypeView::Web
                    | ValueTypeView::Data { .. }
                    | ValueTypeView::Record(_)
                    | ValueTypeView::Patched { .. }
                    | ValueTypeView::Sum(..)
                    | ValueTypeView::List(_)
                    | ValueTypeView::Stack { .. }
                    | ValueTypeView::Capability { .. }
                    | ValueTypeView::Buffer
                    | ValueTypeView::Qubit
                    | ValueTypeView::Row
                    | ValueTypeView::RowTail(_)
                    | ValueTypeView::Integer
                    | ValueTypeView::String
                    | ValueTypeView::Character
                    | ValueTypeView::Float64
                    | ValueTypeView::Fixed(_)
                    | ValueTypeView::Unit
                    | ValueTypeView::Thunk(_)
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::Product(..)
                    | ValueTypeView::Sigma { .. }
                    | ValueTypeView::StaticPi { .. }
                    | ValueTypeView::Abstract(_)
                    | ValueTypeView::Session(_)
                    | ValueTypeView::Staged { .. }
                    | ValueTypeView::Kept { .. }
                    | ValueTypeView::World(_)
                    | ValueTypeView::Unknown => Ok(otherwise.clone()),
                },
                Maybe::Absent(_) => Ok(otherwise.clone()),
            },
            Value::PathRefl(_)
            | Value::Here(_)
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)
            | Value::SessionRelated { .. }
            | Value::Recorded(_)
            | Value::Dialogue(_)
            | Value::Web(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::Ua { .. }
            | Value::Compose { .. }
            | Value::Fill { .. }
            | Value::Returned(_)
            | Value::Nested(_)
            | Value::Run(_)
            | Value::RecordUpdate { .. }
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Reify(_)
            | Value::Primitive { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Variable { .. }
            | Value::Tuple(_)
            | Value::ListNil
            | Value::ListCons(..)
            | Value::Literal(_)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Ascribe { .. }
            | Value::Lift { .. }
            | Value::StaticLambda(_)
            | Value::StaticApplication(..)
            | Value::Hole(_)
            | Value::Mark { .. }
            | Value::Row(_) => Ok(otherwise.clone()),
        }
    }

    /// The number of binders open in `zone`, without borrowing them mutably.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn depth(
        &self,
        zone: Zone,
    ) -> BinderDepth
    {
        self.binders.depth(zone)
    }

    /// The types of the intuitionistic binders open above `entry`, outermost
    /// first: the hypotheses a refusal met there stands under.
    ///
    /// # Specification
    /// - requires: nothing; `entry` at or above the depth gives none.
    /// - ensures: one type per binder between `entry` and the depth, in the
    ///   order the binders were opened; the binders are left as they stand.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal under a bind keeps the bind's binder, and a
    ///   refused data field keeps the parameters and fields before it.
    /// - witness: `judgement::tests::a_refusal_under_a_bind_keeps_its_hypothesis`
    /// - witness: `former::tests::a_refused_field_keeps_the_binders_it_was_formed_under_4028`
    #[spec(
        captures: depth = self.depth(Zone::Intuitionistic),
        ensures: |ret| self.depth(Zone::Intuitionistic) == depth
            && ret.len() <= usize::from(depth).saturating_sub(usize::from(entry)),
    )]
    pub(crate) fn opened_since(
        &mut self,
        entry: BinderDepth,
    ) -> Vec<ValueTypeId>
    {
        let opened = usize::from(self.binders.depth(Zone::Intuitionistic))
            .saturating_sub(usize::from(entry));
        let mut hypotheses = Vec::with_capacity(opened);
        for index in (0 .. opened).rev() {
            let Ok(index) = u32::try_from(index)
            else {
                break;
            };
            let Ok(declared) = self
                .binders
                .occurrence(Zone::Intuitionistic, DeBruijnIndex::from(index))
            else {
                break;
            };
            hypotheses.push(declared);
        }
        hypotheses
    }

    /// The world the judgement stands at, without borrowing the binders
    /// mutably.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn world(&self) -> gandr_core_term::world::World
    {
        self.binders.world()
    }

    /// The binders the judgement is under.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn binders(&mut self) -> &mut Context
    {
        &mut self.binders
    }

    /// Open a binder of the intuitionistic zone over `ty` at `grade`, and
    /// refuse a type with no comonoid.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one more intuitionistic binder, over `ty`, when the result is
    ///   `Ok`; no change otherwise.
    /// - fails: as [`crate::comonoid::require`], at `at`.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda, a bind and a case arm over a qubit are
    ///   refused, and a binder over a type with a comonoid opens.
    /// - witness: `judgement::session::tests::each_binder_over_a_qubit_is_refused_5739`
    #[spec(
        captures: depth = usize::from(self.depth(Zone::Intuitionistic)),
        ensures: |ret| usize::from(self.depth(Zone::Intuitionistic)) == depth.saturating_add(usize::from(ret.is_ok())),
    )]
    pub(crate) fn open_intuitionistic(
        &mut self,
        at: CoreNode,
        ty: ValueTypeId,
        grade: crate::comonoid::Grade,
    ) -> Result<(), CheckRefusal>
    {
        crate::comonoid::require(self.arena(), at, ty, grade)?;
        self.binders.open(Zone::Intuitionistic, ty);
        Ok(())
    }

    /// The stages the recursion typing minted since the declaration under way
    /// began.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn stages(&self) -> &gandr_kernel_core::stage_order::StageOrder
    {
        &self.stages
    }

    /// The stages the recursion typing minted, to mint more.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn stages_mut(&mut self) -> &mut gandr_kernel_core::stage_order::StageOrder
    {
        &mut self.stages
    }

    /// The stages the declaration under way's calls supply their callees'
    /// binders at.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn supplies(&self) -> &[gandr_core_term::staged::Supply]
    {
        &self.supplies
    }

    /// Hold the declaration under way's calls to `supplies`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn supply(
        &mut self,
        supplies: &[gandr_core_term::staged::Supply],
    )
    {
        self.supplies.clear();
        self.supplies.extend_from_slice(supplies);
    }

    /// Resolve each of the model slots `models` the judgement under way met,
    /// at the part `part` of the declaration, as
    /// [`crate::elaboration::Deferrals::resolve`] does over the arena.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn resolve_models(
        &mut self,
        models: &[gandr_core_term::model::ModelSlot],
        part: crate::elaboration::Signing,
    ) -> Result<(), (ValueId, CheckRefusal)>
    {
        self.deferrals
            .resolve(self.arena, &self.definitions, models, part)
    }

    /// Forget every stage minted and the fixpoint opened: a declaration's
    /// stages are its own, so the stages a refusal names do not depend on the
    /// declarations before it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn forget_stages(&mut self)
    {
        self.stages = gandr_kernel_core::stage_order::StageOrder::default();
        self.own = (
            Maybe::Absent(own::Absent::Unopened),
            Maybe::Absent(own::Absent::Unopened),
        );
    }

    /// Read the result of the definition under way's own fixpoint as `stage`
    /// says.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn read_result(
        &mut self,
        stage: crate::recursion::ResultStage,
    )
    {
        self.result_stage = stage;
    }

    /// How the definition under way's own fixpoint reads its result.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn result_stage(&self) -> crate::recursion::ResultStage
    {
        self.result_stage
    }

    /// Note that the result of the definition at `constant` stands at the
    /// stage of its parameter at `position`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn record_following(
        &mut self,
        constant: ConstantIndex,
        position: gandr_kernel_term::StagedPosition,
    )
    {
        let _earlier = self.following.insert(constant, position);
    }

    /// The position of the parameter whose stage the result of the definition
    /// at `constant` stands at, when it follows one.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn following(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<gandr_kernel_term::StagedPosition, crate::recursion::Unstaged>
    {
        self.following.get(&constant).map_or(
            Maybe::Absent(crate::recursion::Unstaged::Plain),
            |&position| Maybe::Present(position),
        )
    }

    /// The position of the parameter whose stage each definition's result
    /// stands at, by position, for each definition whose result follows one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn followings(&self) -> &BTreeMap<ConstantIndex, gandr_kernel_term::StagedPosition>
    {
        &self.following
    }

    /// Take `body`, the definition under way's body, as its own fixpoint's
    /// when the definition is a mutual block's and its body thunks one, with
    /// none open yet: only a block's families name its definitions.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn own_body(
        &mut self,
        body: ValueId,
    )
    {
        let root = match (&self.mutual, self.arena.value(body)) {
            (&Maybe::Present(_), Some(&Value::Thunk(root)))
                if matches!(
                    self.arena.computation(root),
                    Some(&Computation::Fixpoint { .. })
                ) =>
            {
                Maybe::Present(root)
            },
            (&(Maybe::Present(_) | Maybe::Absent(_)), Some(_) | None) => {
                Maybe::Absent(own::Absent::Unopened)
            },
        };
        self.own = (root, Maybe::Absent(own::Absent::Unopened));
    }

    /// Open `fixpoint`, whose self binder of type `binder` is about to be
    /// bound at the current depth, as the definition's own when it is the
    /// fixpoint its body thunks.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn open_own(
        &mut self,
        fixpoint: ComputationId,
        binder: ValueTypeId,
    )
    {
        if matches!(self.own.0, Maybe::Present(root) if root == fixpoint) {
            self.own.1 = Maybe::Present((self.depth(Zone::Intuitionistic), binder));
        }
    }

    /// The declaration's own constant and the index of its self binder, while
    /// its own fixpoint is open and that binder is in scope.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when the declaration under way opened its own
    ///   fixpoint and the binder at the index past the depth it was opened at
    ///   still has the type it was opened with.
    /// - provides: what a case inside a mutual block's definition identifies
    ///   that definition's constant with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decoder's arm reads its family's field through its
    ///   self binder.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(ensures: |ret| match ret {
        Maybe::Present((constant, index)) => {
            self.admitted == Maybe::Present(constant) && self.hypothesis(index).is_ok()
        },
        Maybe::Absent(_) => true,
    })]
    pub(crate) fn own_fixpoint(
        &self
    ) -> Maybe<(ConstantIndex, gandr_kernel_term::DeBruijnIndex), own::Absent>
    {
        let (Maybe::Present((below, binder)), Maybe::Present(constant)) =
            (self.own.1, self.admitted)
        else {
            return Maybe::Absent(own::Absent::Unopened);
        };
        let distance = usize::from(self.depth(Zone::Intuitionistic))
            .checked_sub(usize::from(below))
            .and_then(|past| past.checked_sub(1))
            .and_then(|distance| u32::try_from(distance).ok())
            .map(gandr_kernel_term::DeBruijnIndex::from);
        match distance {
            Some(index) if self.hypothesis(index) == Ok(binder) => {
                Maybe::Present((constant, index))
            },
            Some(_) | None => Maybe::Absent(own::Absent::Closed),
        }
    }

    /// The type of the intuitionistic hypothesis `index` binders out.
    ///
    /// # Specification
    /// - ensures: the declared type of that binder, as the context holds it.
    /// - fails: [`CheckRefusal::MachineInvariant`] for an index past the depth.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — read through the room rule, whose witnesses separate
    ///   a hypothesis at a stage from one past it.
    /// - witness: `tests::recursion::a_nullary_argument_needs_a_value_below_the_stage`
    #[spec(ensures: |ret| ret.is_ok() == usize::try_from(u32::from(index)).is_ok_and(|at| at < usize::from(self.depth(Zone::Intuitionistic))))]
    pub(crate) fn hypothesis(
        &self,
        index: gandr_kernel_term::DeBruijnIndex,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        self.binders
            .declared(Zone::Intuitionistic, index)
            .map_err(|_unbound| CheckRefusal::MachineInvariant)
    }

    /// The type a leaf rule synthesises.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn atom(
        &self,
        atom: Atom,
    ) -> FormedValueType
    {
        match atom {
            Atom::Unit => self.atoms.unit,
            Atom::Integer => self.atoms.integer,
            Atom::String => self.atoms.string,
            Atom::Character => self.atoms.character,
            Atom::Float64 => self.atoms.float64,
            Atom::Fixed(IntegerWidth::U32) => self.atoms.u32,
            Atom::Fixed(IntegerWidth::U64) => self.atoms.u64,
            Atom::Fixed(IntegerWidth::I32) => self.atoms.i32,
            Atom::Fixed(IntegerWidth::I64) => self.atoms.i64,
        }
    }

    /// Admit the declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-order position is admissible input and
    ///   refused.
    /// - ensures: on success `constant` is the highest position admitted.
    /// - provides: the order resolution by position rests on.
    /// - fails: [`CheckRefusal::AdmissionOrder`] when `constant` is not above
    ///   the highest position admitted; the context is unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::AdmissionOrder`] — `constant` does not follow every
    ///   position admitted before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is one strict comparison,
    ///   separated by a first admission, a repeated position and a lower one,
    ///   each refusal asserted with both positions.
    /// - witness: `module::tests::an_admission_out_of_order_is_refused`
    #[spec(
        captures: previous = self.admitted,
        ensures: |ret| match previous {
            | Maybe::Present(admitted) if constant <= admitted => self.admitted == previous
                && ret == Err(CheckRefusal::AdmissionOrder { constant, admitted }),
            | Maybe::Present(_) | Maybe::Absent(_) => ret == Ok(()) && self.admitted == Maybe::Present(constant),
        },
    )]
    pub(crate) fn admit(
        &mut self,
        constant: ConstantIndex,
    ) -> Result<(), CheckRefusal>
    {
        if let Maybe::Present(admitted) = self.admitted
            && constant <= admitted
        {
            return Err(CheckRefusal::AdmissionOrder { constant, admitted });
        }
        self.admitted = Maybe::Present(constant);
        Ok(())
    }

    /// Record the type the admitted declaration at `constant` supplied.
    ///
    /// # Specification
    /// - requires: `constant` is the position admitted last, and every type
    ///   recorded at a later position was foreseen, so the table stays strictly
    ///   ascending.
    /// - ensures: [`Self::signature`] answers `declared` for `constant`; a type
    ///   foreseen there is replaced, and nothing else changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — later declarations read earlier supplied types,
    ///   including a refused signed body; absent types remain absent. These
    ///   cases separate omitted or mispositioned records in ordered modules; a
    ///   mutual block's decoder records over the type it foresaw.
    /// - witness: `module::tests::a_later_declaration_reads_an_earlier_type`
    /// - witness: `module::tests::a_refused_signed_body_still_supplies_its_type`
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(
        requires: self.admitted == Maybe::Present(constant),
        ensures: self.signature(constant) == Maybe::Present(declared),
    )]
    pub(crate) fn record(
        &mut self,
        constant: ConstantIndex,
        declared: FormedValueType,
    )
    {
        self.foresee(constant, declared);
    }

    /// Record the type the declaration at `constant`, a later member of the
    /// mutual block being admitted, declares, before it is admitted.
    ///
    /// # Specification
    /// - requires: nothing — a position already recorded is replaced.
    /// - ensures: [`Self::signature`] answers `declared` for `constant`, the
    ///   table stays strictly ascending, and every other entry is unchanged.
    /// - provides: the step of a mutual block's admission schedule between its
    ///   families' formation and their constructors': the constructors name its
    ///   definitions at the types they declare.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe's constructor naming its decoder forms at
    ///   the decoder's declared type before the decoder is admitted.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(ensures: self.signature(constant) == Maybe::Present(declared))]
    pub(crate) fn foresee(
        &mut self,
        constant: ConstantIndex,
        declared: FormedValueType,
    )
    {
        match self
            .signatures
            .binary_search_by_key(&constant, |&(held, _)| held)
        {
            Ok(found) => {
                if let Some(entry) = self.signatures.get_mut(found) {
                    entry.1 = declared;
                }
            },
            Err(slot) => self.signatures.insert(slot, (constant, declared)),
        }
    }

    /// Forget the declared types recorded at and past `from`: what a mutual
    /// block foresaw for its families' fields, once its definitions are
    /// judged. The forgotten types stay in hindsight, which
    /// [`Self::foresee_hindsight`] reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::signature`] answers nothing at and past `from`, and
    ///   every entry before it is unchanged; the hindsight holds what was
    ///   foreseen at and past `from`, ascending.
    /// - provides: the step of a mutual block's schedule that judges each
    ///   definition as a lone one is judged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decoder whose body names a later definition of its
    ///   block is refused as a forward reference.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(ensures: self.signatures.last().is_none_or(|&(last, _)| last < from)
        && self.hindsight.first().is_none_or(|&(held, _)| held >= from))]
    pub(crate) fn unforesee(
        &mut self,
        from: ConstantIndex,
    )
    {
        let kept = self.signatures.partition_point(|&(held, _)| held < from);
        let forgotten = self.signatures.split_off(kept);
        self.hindsight.retain(|&(held, _)| held >= from);
        self.hindsight.extend(forgotten);
        self.hindsight.sort_by_key(|&(held, _)| held);
        self.hindsight.dedup_by_key(|&mut (held, _)| held);
    }

    /// Foresee the open mutual block's definitions not yet admitted again at
    /// their declared types, as the block's families formed: a family's field
    /// read inside a definition may name them. The foresight lasts until
    /// [`Self::forget_foresight`] is given the mark returned.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::signature`] answers each type in hindsight, every
    ///   position it did not answer before recorded as foreseen; the mark is
    ///   the foreseen count before the call.
    /// - provides: the scope a definition's identified field is formed in.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe whose field decodes a later definition of
    ///   its block reaches the decoder's stage check rather than an unknown
    ///   constant.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(
        captures: before = self.foreseen.len(),
        ensures: |ret| ret == Foresight(before) && self.foreseen.len() >= before,
    )]
    pub(crate) fn foresee_hindsight(&mut self) -> Foresight
    {
        let mark = self.foresight();
        let held = core::mem::take(&mut self.hindsight);
        for &(constant, declared) in &held {
            if let Maybe::Absent(_) = self.signature(constant) {
                self.foresee(constant, declared);
                self.foreseen.push(constant);
            }
        }
        self.hindsight = held;
        mark
    }

    /// The mark of the foresights open now: what a judgement that refuses
    /// part-way returns the signature table to.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn foresight(&self) -> Foresight
    {
        Foresight(self.foreseen.len())
    }

    /// Close the foresights opened since `mark`: every definition they
    /// foresaw leaves [`Self::signature`] again.
    ///
    /// # Specification
    /// - requires: nothing; a mark past what is open closes nothing.
    /// - ensures: the foreseen count is at most the mark's, and the signature
    ///   table holds no more entries than before.
    /// - provides: the close of [`Self::foresee_hindsight`], on the frame stack
    ///   or on a refusal's unwinding.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decoder's arm formed in foresight, and its body
    ///   after it naming a later definition refused as a forward reference.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(
        captures: before = self.signatures.len(),
        ensures: self.foreseen.len() <= mark.0 && self.signatures.len() <= before,
    )]
    pub(crate) fn forget_foresight(
        &mut self,
        mark: Foresight,
    )
    {
        let at = mark.0.min(self.foreseen.len());
        let forgotten: BTreeSet<ConstantIndex> = self.foreseen.drain(at ..).collect();
        self.signatures
            .retain(|&(held, _)| !forgotten.contains(&held));
    }
}

#[cfg(test)]
mod tests;
