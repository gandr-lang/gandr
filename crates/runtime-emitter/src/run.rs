//! Running a lowered command: the tier the policy picks, the content cache
//! native code is served from, the regions a run uses, and the outcome moved
//! into the caller's store.
//!
//! A run lowers its command every time — the lowered function is the cache
//! key, compared by value — and either serves the function's emitted code
//! from the process's cache, emitting it on a miss, or builds the executor's
//! program. Both run over the calling thread's heap and frame regions, each
//! allocated at its bound once per thread and committed page by page as runs
//! touch it; a run that would pass a bound declines exhausted. The
//! alternative was a small region doubled and the run repeated from its
//! start, which offers a host handler its requests a second time; the bound
//! costs address space only. The choice reverses if a workload needs more
//! than a bound holds, when the bound becomes the caller's to set.
//!
//! A command closed over a store's values runs the same way, its captures
//! laid out on the run's heap first, as a host's reply is, and the run
//! allocating past them: a cut's writer runs so, on a thread of its own, apart
//! from its reader's heap. The writer's captures cross by location, a
//! `HeapValueId` in the store, inside one process; they are never committed by
//! content.
//!
//! # Boundaries
//!
//! A run's regions are its LAM, the location-addressable memory of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`
//! § 4, and the value representation is what of LAM's judgements they
//! realise:
//!
//! - **Materialisation** is a read: a match reads a header and its fields at
//!   the value's address and allocates nothing.
//! - **Duplication** copies the address and counts one owner more on the word
//!   before the header. Every value is an object, an integer included, so every
//!   field is an address and a copy is one word at any type.
//! - **Evacuation** moves an outcome into the caller's [`Store`], children
//!   before parents, each object once however many hold it, so sharing survives
//!   as LAM's forwarding map keeps it. A store's values enter a run the same
//!   way, laid out once each, and a value the run moved out answers its own
//!   object.
//!
//! It departs from LAM in three places. A location is recycled: a block freed
//! at its last owner joins its size's free list, and the thread's next run
//! reuses the regions whole, so no collector evacuates within a run. Nothing
//! is laid inline, so there is no wrapping constructor and nothing to splice.
//! And a block is written after its allocation: a match whose scrutinee has
//! one owner hands its block to the constructor its arm rebuilds.
//!
//! # Witnesses
//!
//! The rebuild in place rests on `storage-conjecture-exclusivity`, a named
//! target rather than a fact: a write into a block whose count is one is
//! deep-equal to the copy LAM's store would extend by, since no other holder
//! reads the block. That is value independence as
//! `Racordon-2020-formal_definition_swifts_value_semantics` states it, an
//! assignment through a path being the copy with the path substituted.
//! `gandr-runtime-stencils`' `a_unique_scrutinee_is_rebuilt_in_its_own_block`
//! and `a_shared_scrutinee_is_rebuilt_in_a_fresh_block` witness the rebuild,
//! and `corpus/model/runtime/exclusive-update.gandr` holds an update through
//! an exclusive view to the copy's answer on both tiers. Measured, that update
//! rebuilds in a fresh block at either grade: the held cell keeps its owner
//! while the view is out, so the match meets two. A pair the match alone
//! holds is rebuilt in its own block.
//!
//! # References
//!
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: a cut's writer is
//!   its producer run on its own, the cut's concurrent schedule beside the
//!   sequential one (§ futures-in-gandr item 1, § futures-try-first).
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: the
//!   LAM whose materialisation, duplication and evacuation the regions
//!   realise, and the immutable append-only store they depart from (§ 4).
//! - `Racordon-2020-formal_definition_swifts_value_semantics` — background: the
//!   independence value semantics states, which a rebuild in place must keep:
//!   an assignment through a path is the copy with the path substituted.
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage
//!   programme, § storage-programme-memory-model-reading: LAM as the value
//!   representation's specification, and `storage-conjecture-exclusivity`.
//! - `vault:01a178aa-608d-75d0-8f71-e6fe4289f327` — lineage: the compiled
//!   runtime's representation question (§ runtime-question-what-runtime-means).

#[cfg(gandr_patcher)]
use alloc::sync::Arc;
use core::cell::RefCell;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::Environment;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::Observed;
use gandr_runtime_stencils::Refusal;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Status;
use gandr_runtime_stencils::Word;

use crate::executor::Program;
use crate::function::Unbound;
use crate::host;
use crate::host::Calls;
use crate::host::Codes;
use crate::host::Parts;
use crate::host::Refused;
use crate::host::Unlaid;
use crate::lower::Form;
use crate::lower::Lowered;
use crate::lower::lower;
use crate::lower::lower_suspended;
use crate::lower::lower_unfused;
#[cfg(gandr_patcher)]
use crate::native::EmitRefusal;
#[cfg(gandr_patcher)]
use crate::native::Emitted;
#[cfg(gandr_patcher)]
use crate::native::Native;
use crate::seam::Adapter;
use crate::seam::HostHandler;
use crate::seam::HostOutcome;
use crate::seam::Offer;
use crate::transfer::Sites;
use crate::transfer::TransferRefusal;
use crate::world::Unmigrated;

/// The environment variable the policy is read from.
pub const POLICY_VARIABLE: &str = "GANDR_NATIVE";

/// When a run takes native code.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum Policy
{
    /// Emit on a function's first run and serve the cache after: native
    /// wherever a patcher exists.
    #[default]
    Always,
    /// Never emit: every run takes the portable executor.
    Never,
    /// Serve a function the cache already holds; take the executor on a
    /// miss, emitting nothing.
    Cached,
}

impl Policy
{
    /// The policy `GANDR_NATIVE` names: `always`, `never` or `cached`;
    /// [`Policy::Always`] when the variable is unset or names none of them.
    ///
    /// # Specification
    /// - ensures: the spelling decides, case-sensitively; anything else is the
    ///   default.
    /// - executable: none — the spellings are [`From<&str>`]'s, which the
    ///   witness reads directly; the environment is the process's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each spelling and an unknown one select their policy.
    /// - witness: `run::tests::the_policy_reads_its_three_spellings`
    #[inline]
    #[must_use]
    pub fn from_environment() -> Self
    {
        Self::from(std::env::var(POLICY_VARIABLE).ok().as_deref().unwrap_or(""))
    }
}

impl From<&str> for Policy
{
    /// The policy a spelling names: `always`, `never` or `cached`, the
    /// default for anything else.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(spelling: &str) -> Self
    {
        match spelling {
            "never" => Self::Never,
            "cached" => Self::Cached,
            _ => Self::Always,
        }
    }
}

/// Which code a run takes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Tier
{
    /// Emitted native code, served from the cache.
    Native,
    /// The portable executor.
    Executor,
}

/// Why a run gave no outcome.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Declined
{
    /// The lowering refused a form.
    Lowering(Form),
    /// The host has no patcher, and the native tier was asked for.
    NoPatcher,
    /// Emission refused the function.
    #[cfg(gandr_patcher)]
    Emission(EmitRefusal),
    /// A label of the function is unbound.
    Unbound,
    /// The policy serves only cached code and the cache misses.
    Uncached,
    /// The run stopped stuck where nothing named why: a host call refused
    /// operands no well-formed command gives it.
    Stuck,
    /// The run spent its fuel, or a region past its bound.
    Exhausted(Status),
    /// The answer, or a value the run stopped at or offered, could not be
    /// moved into the store.
    Transfer(TransferRefusal),
    /// The host resumed with a value its store does not hold, or one a run
    /// cannot hold: code the host built rather than a value the run moved out.
    Reply(HeapValueId),
    /// A value the environment binds that the run cannot hold — a closure, a
    /// stack, a capability, or code the function does not table — or one its
    /// store does not hold.
    Capture(HeapValueId),
    /// The environment binds other than the command's captures.
    Environment,
    /// This migration answered nothing, for the reason named.
    Migration(CommandId, Unmigrated),
}

impl From<Form> for Declined
{
    /// The lowering's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(form: Form) -> Self
    {
        Self::Lowering(form)
    }
}

impl From<Unbound> for Declined
{
    /// An unbound label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_unbound: Unbound) -> Self
    {
        Self::Unbound
    }
}

impl From<TransferRefusal> for Declined
{
    /// The transfer's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: TransferRefusal) -> Self
    {
        Self::Transfer(refusal)
    }
}

impl core::fmt::Display for Declined
{
    /// Says why the run gave no outcome, in a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Lowering(form) => write!(f, "the lowering refused {form}"),
            Self::NoPatcher => f.write_str("the host has no patcher for native code"),
            #[cfg(gandr_patcher)]
            Self::Emission(_) => f.write_str("native emission refused the function"),
            Self::Unbound => f.write_str("a label of the function is unbound"),
            Self::Uncached => f.write_str("the cache holds no code for the function"),
            Self::Stuck => f.write_str("the run stopped stuck where nothing named why"),
            Self::Exhausted(Status::FuelExhausted) => f.write_str("the run spent its budget"),
            Self::Exhausted(Status::HeapExhausted) => {
                f.write_str("the heap region passed its bound")
            },
            Self::Exhausted(Status::FramesExhausted) => {
                f.write_str("the frame region passed its bound")
            },
            Self::Exhausted(
                Status::Running | Status::Halted | Status::Unmatched | Status::Stuck,
            ) => f.write_str("the run exited with a status no run returns"),
            Self::Transfer(_) => f.write_str("a value could not be moved into the store"),
            Self::Reply(value) => {
                write!(
                    f,
                    "the host resumed with {value}, which the run cannot hold"
                )
            },
            Self::Capture(value) => {
                write!(
                    f,
                    "the environment binds {value}, which the run cannot hold"
                )
            },
            Self::Environment => {
                f.write_str("the environment binds other than the command's captures")
            },
            Self::Migration(at, why) => write!(
                f,
                "the migration at {} answered nothing: {why}",
                gandr_core_sequent::NodeAddress::Command(at)
            ),
        }
    }
}

/// The process's emitted code, by the function it runs.
#[cfg(gandr_patcher)]
#[derive(Debug, Default)]
struct Cache
{
    /// The regions the code lives in.
    native: Native,
    /// Each function's emitted code.
    entries: std::collections::HashMap<crate::function::Function, Arc<Emitted>>,
}

/// The process's cache. A run-count gate before emission would be a no-op
/// here: a function is lowered from its source each process, so the first
/// run is the only run the gate could skip. The cache that serves code
/// across processes is the persistent, content-keyed one.
#[cfg(gandr_patcher)]
static CACHE: std::sync::LazyLock<std::sync::Mutex<Cache>> =
    std::sync::LazyLock::new(|| std::sync::Mutex::new(Cache::default()));

/// The policy, read once per process.
static POLICY: std::sync::LazyLock<Policy> = std::sync::LazyLock::new(Policy::from_environment);

/// The regions a run uses, per thread, each allocated at its bound and
/// committed as a run first touches it.
#[derive(Debug)]
struct Buffers
{
    /// The heap region: capacity only, every word written before it is read.
    heap: Vec<Word>,
    /// The frame region: capacity only, the sentinel frame written in its
    /// first two words.
    frames: Vec<Word>,
    /// The entry window.
    window: Vec<Word>,
    /// The window region every closure entry's window is taken from:
    /// capacity only, every slot written before it is read.
    windows: Vec<Word>,
}

/// The heap region's bound, in words: past it the run declines.
const HEAP_BOUND: usize = 1 << 25;
/// The frame region's bound, in words: past it the run declines.
const FRAME_BOUND: usize = 1 << 23;
/// The window region's bound, in words: past it the run declines.
const WINDOW_BOUND: usize = 1 << 24;

std::thread_local! {
    /// The calling thread's regions.
    static BUFFERS: RefCell<Buffers> = RefCell::new(Buffers {
        heap: Vec::with_capacity(HEAP_BOUND),
        frames: Vec::with_capacity(FRAME_BOUND),
        window: Vec::new(),
        windows: Vec::with_capacity(WINDOW_BOUND),
    });
}

/// Check that the constant table of `globals` fits the heap region `heap`,
/// at whose base it sits: one word a constant, within the region's capacity.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Declined::Exhausted`] with [`Status::HeapExhausted`] when `globals`
/// holds more constants than `heap` has capacity for words.
///
/// # Adequacy
/// - hypothesis: L3 — a table exactly the region's capacity fits and one word
///   more does not; a strict or a reversed comparison changes one answer.
/// - witness: `run::tests::a_constant_table_fits_its_region_up_to_its_capacity`
fn hold_table(
    heap: &Vec<Word>,
    globals: &[ConstantIndex],
) -> Result<(), Declined>
{
    if globals.len() > heap.capacity() {
        return Err(Declined::Exhausted(Status::HeapExhausted));
    }
    Ok(())
}

/// The code a run enters.
#[derive(Clone, Copy, Debug)]
enum Code<'program>
{
    /// Emitted code: its entry and its region's halt.
    #[cfg(gandr_patcher)]
    Native(Word, Word),
    /// An executor program.
    Executor(&'program Program),
}

/// How a run ended, the host's abort apart.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ran
{
    /// The run halted or stopped stuck.
    Ended(Outcome),
    /// The host stopped the run.
    Aborted,
}

impl Ran
{
    /// The outcome of a run with no host, which nothing aborts.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Declined::Stuck`] for an abort, which no run without a host makes.
    fn hostless(self) -> Result<Outcome, Declined>
    {
        match self {
            Self::Ended(outcome) => Ok(outcome),
            Self::Aborted => Err(Declined::Stuck),
        }
    }
}

/// Run `root` under the process's policy and move its outcome into `store`.
///
/// # Specification
/// - ensures: as [`evaluate_on`], on the tier the policy picks: native under
///   [`Policy::Always`] where a patcher exists and emits the function, the
///   executor under [`Policy::Never`], on a miss under [`Policy::Cached`], and
///   wherever native code is not to be had.
/// - executable: none — the tiers' agreement is the differential's to show; a
///   postcondition would run every command twice.
///
/// # Errors
/// As [`evaluate_on`], but never [`Declined::NoPatcher`] or an emission
/// refusal: the executor runs the command instead.
///
/// # Adequacy
/// - hypothesis: L2 — every named program runs through this entry and is
///   compared with each tier's outcome; the policy's spellings are witnessed
///   apart.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `run::tests::the_policy_reads_its_three_spellings`
#[inline]
pub fn evaluate(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<Outcome, Declined>
{
    let lowered = lower(arena, definitions, root)?;
    by_policy(&lowered, (arena, definitions), fuel, store, &[], None)?.hostless()
}

/// Run `root` on `tier` with `fuel` code-word jumps and move its outcome into
/// `store`; an operation no handler of the run claims stops it stuck.
///
/// # Specification
/// - requires: every constant `root` reaches is defined in `definitions`.
/// - ensures: on success how the run ended: the value it halted with, or the
///   reason it stopped stuck, every value either names moved into the store as
///   its readback reads it.
/// - executable: none — the tiers' agreement is the differential's to show; a
///   postcondition would run every command twice.
///
/// # Errors
/// [`Declined`] naming why the run gave no outcome: a form the lowering
/// refuses, a spent budget, a region past its bound, or a migration whose body
/// answers nothing at its world or whose crossing fails.
///
/// # Adequacy
/// - hypothesis: L2 — the named programs run on both tiers and their outcomes
///   are compared value by value, and with the outcome each states.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub fn evaluate_on(
    tier: Tier,
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<Outcome, Declined>
{
    let lowered = lower(arena, definitions, root)?;
    on_tier(tier, &lowered, (arena, definitions), fuel, store, &[], None)?.hostless()
}

/// As [`evaluate_on`], the command's unfused lowering run: every instruction
/// its own dispatch, the reference a fused function answers to.
///
/// # Specification
/// - requires: as [`evaluate_on`].
/// - ensures: as [`evaluate_on`], over [`lower_unfused`]'s function.
/// - executable: none — as [`evaluate_on`].
///
/// # Errors
/// As [`evaluate_on`].
///
/// # Adequacy
/// - hypothesis: L2 — every named, generated and corpus program runs unfused
///   beside its fused function, with equal outcomes.
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
#[inline]
pub fn evaluate_unfused_on(
    tier: Tier,
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<Outcome, Declined>
{
    let lowered = lower_unfused(arena, definitions, root)?;
    on_tier(tier, &lowered, (arena, definitions), fuel, store, &[], None)?.hostless()
}

/// Run `body`, a command binding one covariable, on `tier` over the values
/// `environment` binds in `store`, and move its outcome into `store`.
///
/// A cut's writer runs so, closed over a store's values apart from its
/// reader's heap.
///
/// # Specification
/// - requires: `environment` binds the producer bindings `body`'s support
///   selects, innermost first, as a transfer binds a thunk suspending `body`;
///   every constant `body` reaches is defined in `definitions`.
/// - ensures: as [`evaluate_on`] for `body` with its covariable delivering to
///   `★`, each bound value first laid out on the run's heap as a host's reply
///   is.
/// - executable: none — as [`evaluate_on`].
///
/// # Errors
/// As [`evaluate_on`]; [`Declined::Environment`] for an environment binding
/// other than `body`'s captures, and [`Declined::Capture`] naming a bound
/// value the run cannot hold.
///
/// # Adequacy
/// - hypothesis: L2 — thunks a run answered with, over no capture, one, two and
///   one shared by two fields, run from the store on both tiers and answer what
///   forcing each in place answers; a capture slot swapped, dropped or left
///   uncounted changes an answer. L3 — an environment binding one value too few
///   or too many declines, and a captured function declines naming it.
/// - witness: `tests::closed::a_thunk_runs_from_the_store_as_it_runs_in_place`
/// - witness: `tests::closed::a_shared_capture_is_laid_out_once_and_counted_twice`
/// - witness: `tests::closed::an_environment_other_than_the_captures_declines`
#[inline]
pub fn evaluate_closed_on(
    tier: Tier,
    (arena, definitions): (&CommandArena, &Definitions),
    (body, environment): (CommandId, Environment),
    (fuel, store): (Fuel, &mut Store),
) -> Result<Outcome, Declined>
{
    let lowered = lower_suspended(arena, definitions, body)?;
    let captured: Vec<HeapValueId> = store.bound_values(environment).collect();
    if captured.len() != lowered.captures.len() {
        return Err(Declined::Environment);
    }
    on_tier(
        tier,
        &lowered,
        (arena, definitions),
        fuel,
        store,
        &captured,
        None,
    )?
    .hostless()
}

/// As [`evaluate`], an operation no handler of the run claims offered to
/// `host`.
///
/// # Specification
/// - ensures: as [`evaluate_on_with_host`], on the tier the policy picks as
///   [`evaluate`] picks it.
/// - executable: none — as [`evaluate`].
///
/// # Errors
/// As [`evaluate_on_with_host`], but never [`Declined::NoPatcher`] or an
/// emission refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a host reply runs on through the policy's tier as it does
///   on each tier alone.
/// - witness: `tests::seam::a_host_reply_flows_into_the_rest_of_the_run`
#[inline]
pub fn evaluate_with_host<Host>(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    (fuel, store): (Fuel, &mut Store),
    host: &mut Host,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Host: HostHandler,
{
    let lowered = lower(arena, definitions, root)?;
    let mut adapter = Adapter {
        host,
        aborted: None,
    };
    let ran = by_policy(
        &lowered,
        (arena, definitions),
        fuel,
        store,
        &[],
        Some(&mut adapter),
    )?;
    hosted(ran, adapter)
}

/// As [`evaluate_on`], an operation no handler of the run claims offered to
/// `host`.
///
/// # Specification
/// - requires: as [`evaluate_on`].
/// - ensures: as [`evaluate_on`], each unclaimed operation offered to the host
///   once, its payload moved into the store: a reply continues the operation's
///   continuation, a decline leaves the run stuck at the operation, and an
///   abort ends the run with the host's result.
/// - executable: none — as [`evaluate_on`].
///
/// # Errors
/// As [`evaluate_on`], and [`Declined::Reply`] for a reply the run cannot
/// hold.
///
/// # Adequacy
/// - hypothesis: L3 — scripted hosts that resume, abort and decline, offered
///   operations claimed and unclaimed by the run's handlers, on each tier.
/// - witness: `tests::seam::a_host_resumes_a_single_unhandled_perform`
/// - witness: `tests::seam::a_host_abort_never_resumes_and_a_missing_reply_declines`
#[inline]
pub fn evaluate_on_with_host<Host>(
    tier: Tier,
    (arena, definitions, root): (&CommandArena, &Definitions, CommandId),
    (fuel, store): (Fuel, &mut Store),
    host: &mut Host,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Host: HostHandler,
{
    let lowered = lower(arena, definitions, root)?;
    let mut adapter = Adapter {
        host,
        aborted: None,
    };
    let ran = on_tier(
        tier,
        &lowered,
        (arena, definitions),
        fuel,
        store,
        &[],
        Some(&mut adapter),
    )?;
    hosted(ran, adapter)
}

/// A hosted run's outcome: an abort carries the result the host kept.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Declined::Stuck`] for an abort the host kept no result for, which no
/// adapter makes.
fn hosted<Host>(
    ran: Ran,
    adapter: Adapter<'_, Host>,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Host: HostHandler,
{
    match ran {
        Ran::Ended(outcome) => Ok(HostOutcome::Completed(outcome)),
        Ran::Aborted => adapter
            .aborted
            .map(HostOutcome::Aborted)
            .ok_or(Declined::Stuck),
    }
}

/// Run `lowered`, closed over `captured`, on the tier the policy picks, the
/// executor wherever native code is not to be had.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate`], and [`Declined::Capture`] as [`on_tier`] names it.
pub fn by_policy(
    lowered: &Lowered,
    source: (&CommandArena, &Definitions),
    fuel: Fuel,
    store: &mut Store,
    captured: &[HeapValueId],
    mut offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    match *POLICY {
        Policy::Always => {
            match run_native(lowered, source, fuel, store, captured, offer.as_deref_mut()) {
                Err(Declined::NoPatcher) => {
                    run_executor(lowered, source, fuel, store, captured, offer)
                },
                #[cfg(gandr_patcher)]
                Err(Declined::Emission(_)) => {
                    run_executor(lowered, source, fuel, store, captured, offer)
                },
                ran => ran,
            }
        },
        Policy::Never => run_executor(lowered, source, fuel, store, captured, offer),
        Policy::Cached => run_cached(lowered, source, fuel, store, captured, offer),
    }
}

/// Run `lowered`, lowered from `source`'s arena over its definitions, on
/// `tier`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on_with_host`], and [`Declined::Capture`] naming a value of
/// `captured` the run cannot hold.
pub fn on_tier(
    tier: Tier,
    lowered: &Lowered,
    source: (&CommandArena, &Definitions),
    fuel: Fuel,
    store: &mut Store,
    captured: &[HeapValueId],
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    match tier {
        Tier::Native => run_native(lowered, source, fuel, store, captured, offer),
        Tier::Executor => run_executor(lowered, source, fuel, store, captured, offer),
    }
}

/// Run on the executor.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`on_tier`].
fn run_executor(
    lowered: &Lowered,
    (arena, definitions): (&CommandArena, &Definitions),
    fuel: Fuel,
    store: &mut Store,
    captured: &[HeapValueId],
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    let program = Program::build(&lowered.function)?;
    let codes = Codes::Executor(&program, &lowered.function);
    let sites = Sites::new(lowered, codes);
    run(
        Code::Executor(&program),
        Parts {
            lowered,
            codes,
            sites: &sites,
            arena,
            definitions,
            store,
            offer,
        },
        fuel,
        captured,
    )
}

/// Run emitted code, emitting on a miss.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`on_tier`].
#[cfg(gandr_patcher)]
fn run_native(
    lowered: &Lowered,
    source: (&CommandArena, &Definitions),
    fuel: Fuel,
    store: &mut Store,
    captured: &[HeapValueId],
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    let emitted = {
        let mut cache = CACHE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(held) = cache.entries.get(&lowered.function) {
            Arc::clone(held)
        }
        else {
            let emitted = Arc::new(
                cache
                    .native
                    .emit(&lowered.function)
                    .map_err(Declined::Emission)?,
            );
            cache
                .entries
                .insert(lowered.function.clone(), Arc::clone(&emitted));
            emitted
        }
    };
    run_emitted(&emitted, lowered, source, fuel, (store, captured, offer))
}

/// The native tier needs a patcher this host lacks.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Declined::NoPatcher`], always.
#[cfg(not(gandr_patcher))]
fn run_native(
    lowered: &Lowered,
    source: (&CommandArena, &Definitions),
    fuel: Fuel,
    store: &mut Store,
    captured: &[HeapValueId],
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    let _ = (lowered, source, fuel, store, captured, offer);
    Err(Declined::NoPatcher)
}

/// Serve cached code, or take the executor on a miss.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`on_tier`].
fn run_cached(
    lowered: &Lowered,
    source: (&CommandArena, &Definitions),
    fuel: Fuel,
    store: &mut Store,
    captured: &[HeapValueId],
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    #[cfg(gandr_patcher)]
    {
        let held = CACHE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .entries
            .get(&lowered.function)
            .map(Arc::clone);
        if let Some(emitted) = held {
            return run_emitted(&emitted, lowered, source, fuel, (store, captured, offer));
        }
    }
    run_executor(lowered, source, fuel, store, captured, offer)
}

/// Run code the cache served.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`on_tier`].
#[cfg(gandr_patcher)]
fn run_emitted(
    emitted: &Emitted,
    lowered: &Lowered,
    (arena, definitions): (&CommandArena, &Definitions),
    fuel: Fuel,
    (store, captured, offer): (&mut Store, &[HeapValueId], Option<&mut (dyn Offer + '_)>),
) -> Result<Ran, Declined>
{
    let codes = Codes::Native {
        labels: &emitted.labels,
        stubs: &emitted.stubs,
    };
    let sites = Sites::new(lowered, codes);
    run(
        Code::Native(emitted.entry, emitted.halt),
        Parts {
            lowered,
            codes,
            sites: &sites,
            arena,
            definitions,
            store,
            offer,
        },
        fuel,
        captured,
    )
}

/// Run `code` once over the calling thread's regions, the store's values
/// `captured` laid out in the entry window's capture slots, and move how it
/// ended into `parts`' store.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`on_tier`].
///
/// # Adequacy
/// - hypothesis: L2 — every named program run natively answers what the
///   interpreter answers, and a returned body leaves the window region where it
///   found it; a run that answered nothing, or gave the code no window region,
///   changes both. A command over captures answers as forcing it in place does;
///   a body entered at the heap's start allocates over its captures.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::count::a_returned_body_gives_its_window_back`
/// - witness: `tests::closed::a_thunk_runs_from_the_store_as_it_runs_in_place`
fn run(
    code: Code<'_>,
    parts: Parts<'_, '_>,
    fuel: Fuel,
    captured: &[HeapValueId],
) -> Result<Ran, Declined>
{
    let lowered = parts.lowered;
    BUFFERS.with_borrow_mut(|buffers| {
        buffers.window.clear();
        buffers
            .window
            .resize(lowered.function.slots().0.max(1), Word::ZERO);
        let halt = match code {
            #[cfg(gandr_patcher)]
            Code::Native(_, halt) => halt,
            Code::Executor(program) => program.halt(),
        };
        let table = buffers.heap.as_mut_ptr();
        let heap_limit = table.wrapping_add(buffers.heap.capacity());
        // The constant table sits at the heap's base, every word zero: no
        // constant is unfolded yet.
        let constants = lowered.globals.len();
        hold_table(&buffers.heap, &lowered.globals)?;
        // SAFETY: the heap region's capacity holds the table's words.
        unsafe {
            table.write_bytes(0, constants);
        }
        let heap = table.wrapping_add(constants);
        let frames = buffers.frames.as_mut_ptr();
        let frame_limit = frames.wrapping_add(buffers.frames.capacity());
        // SAFETY: the frame region's capacity holds far more than the
        // sentinel's two words.
        unsafe {
            frames.write(halt);
        }
        // SAFETY: as above.
        unsafe {
            frames.wrapping_add(1).write(Word::ZERO);
        }
        // A run that acts on a session stands every task on the joined frame,
        // laid above the sentinel once the entry window is known.
        let joined = lowered.joined.map(|label| parts.codes.label(label));
        let base = frames.wrapping_add(if joined.is_some() { 4 } else { 2 });
        let mut calls = Calls::new(parts);
        let mut runtime = Runtime::new(
            heap,
            heap_limit,
            frame_limit,
            base,
            fuel,
            host::enter,
            Word::from_pointer(&raw mut calls),
        );
        runtime.set_globals(table);
        let windows = buffers.windows.as_mut_ptr();
        runtime.set_windows(windows, windows.wrapping_add(buffers.windows.capacity()));
        // A command closed over the store runs over its captures laid out on
        // its heap, each held by its slot of the entry window.
        let laid = calls
            .laid_out(&mut runtime, captured)
            .map_err(|unlaid| match unlaid {
                Unlaid::Value(value) => Declined::Capture(value),
                Unlaid::Run(Refusal::Heap) => Declined::Exhausted(Status::HeapExhausted),
                Unlaid::Run(Refusal::Frames) => Declined::Exhausted(Status::FramesExhausted),
                Unlaid::Run(Refusal::Operands) => Declined::Stuck,
            })?;
        for (&slot, word) in lowered.captures.iter().zip(laid) {
            let held = usize::try_from(slot.0)
                .ok()
                .and_then(|at| buffers.window.get_mut(at))
                .ok_or(Declined::Environment)?;
            *held = word;
        }
        let window = buffers.window.as_mut_ptr();
        if let Some(code) = joined {
            // SAFETY: the frame region's capacity holds far more than the
            // sentinel's and the joined frame's four words.
            unsafe {
                frames.wrapping_add(2).write(code);
            }
            // SAFETY: as above.
            unsafe {
                frames.wrapping_add(3).write(Word::from_pointer(window));
            }
        }
        // The run allocates past the captures laid on its heap.
        let top = runtime.heap_top();
        let answer = match code {
            #[cfg(gandr_patcher)]
            // SAFETY: the entry is a copy the emitter patched in a region the
            // cache keeps mapped; the regions are this thread's, valid up to
            // their limits, the sentinel frame below the base mark, and the
            // window holds the function's slots.
            Code::Native(entry, _) => unsafe {
                gandr_runtime_stencils::enter(entry, &raw mut runtime, top, base, window)
            },
            // SAFETY: the program was built from this function and lives for
            // the call; the regions are as above.
            Code::Executor(program) => unsafe {
                gandr_runtime_stencils::execute(
                    program.entry(),
                    &raw mut runtime,
                    top,
                    base,
                    window,
                )
            },
        };
        let refused = calls.refused().cloned();
        // SAFETY: the run exited; its heap and the function's constants are
        // live until this closure returns, and every exit but the regions'
        // and the fuel's returns a value of that heap or zero.
        let mut moved = |word: Word| unsafe { calls.moved(word) };
        let stuck = match runtime.status() {
            Ok(Status::Halted) => return Ok(Ran::Ended(Outcome::Halted(moved(answer)?))),
            Ok(Status::Unmatched) => {
                let arms = lowered
                    .unmatched
                    .get(usize::from(runtime.observed()))
                    .copied()
                    .ok_or(Declined::Stuck)?;
                Stuck::Unmatched {
                    value: moved(answer)?,
                    arms,
                }
            },
            Ok(Status::Stuck) => match refused {
                Some(Refused::PerformNoHandler(at)) => Stuck::PerformNoHandler(at),
                Some(Refused::ShiftNoReset(at)) => Stuck::ShiftNoReset(at),
                Some(Refused::ResumedNonStack { at, value }) => Stuck::ResumedNonStack {
                    at,
                    value: moved(value)?,
                },
                Some(Refused::Primitive(error)) => Stuck::Primitive(error),
                Some(Refused::NonScalar(value)) => Stuck::NonScalar(moved(value)?),
                Some(Refused::Unended(at)) => Stuck::Unended(at),
                Some(Refused::Outside(at)) => Stuck::Outside(at),
                Some(Refused::UndefinedConstant(constant)) => Stuck::UndefinedConstant(constant),
                Some(Refused::CyclicConstant(constant)) => Stuck::CyclicConstant(constant),
                Some(Refused::Aborted) => return Ok(Ran::Aborted),
                Some(Refused::Operands) => return Err(Declined::Stuck),
                Some(Refused::Reply(value)) => return Err(Declined::Reply(value)),
                Some(Refused::Transfer(refusal)) => return Err(Declined::Transfer(refusal)),
                Some(Refused::Migration(at, why)) => return Err(Declined::Migration(at, why)),
                Some(Refused::Deadlock(waiting)) => Stuck::Deadlock(waiting),
                None => {
                    let head = match Observed::try_from(runtime.observed()) {
                        Ok(Observed::Apply) => DestructorTag::Apply,
                        Ok(Observed::Force) => DestructorTag::Force,
                        Ok(Observed::Project(component)) => {
                            DestructorTag::Project(Component::from(usize::from(component)))
                        },
                        Err(_unnamed) => return Err(Declined::Stuck),
                    };
                    Stuck::Unobservable {
                        value: moved(answer)?,
                        head,
                    }
                },
            },
            Ok(status) => return Err(Declined::Exhausted(status)),
            Err(_unknown) => return Err(Declined::Exhausted(Status::Running)),
        };
        Ok(Ran::Ended(Outcome::Stuck(stuck)))
    })
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use gandr_core_sequent::CommandId;
    use gandr_core_sequent::HeapValueId;
    use gandr_core_sequent::NodeAddress;
    use gandr_kernel_term::ConstantIndex;
    use gandr_runtime_stencils::Status;
    use gandr_runtime_stencils::Word;

    use super::Declined;
    use super::Policy;
    use super::hold_table;
    use crate::function::Function;
    use crate::lower::Form;
    use crate::transfer::TransferRefusal;
    use crate::world::Unmigrated;

    /// A constant table fills its heap region up to the region's capacity,
    /// and one constant more is refused before a word is written.
    #[test]
    fn a_constant_table_fits_its_region_up_to_its_capacity()
    {
        let heap: Vec<Word> = Vec::with_capacity(4);
        let globals = |count: usize| -> Vec<ConstantIndex> {
            (0 .. count).map(ConstantIndex::from).collect()
        };
        let capacity = heap.capacity();
        assert_eq!(Ok(()), hold_table(&heap, &globals(0)), "no table fits");
        assert_eq!(
            Ok(()),
            hold_table(&heap, &globals(capacity)),
            "a table of {capacity} words fills the region"
        );
        assert_eq!(
            Err(Declined::Exhausted(Status::HeapExhausted)),
            hold_table(&heap, &globals(capacity + 1)),
            "one word past the region is refused"
        );
    }

    /// Each spelling of the variable selects its policy, and anything else
    /// the default: a misspelt `never` emits rather than silently running
    /// slower.
    #[test]
    fn the_policy_reads_its_three_spellings()
    {
        assert_eq!(
            Policy::Always,
            Policy::from("always"),
            "the default's own spelling"
        );
        assert_eq!(Policy::Never, Policy::from("never"), "never emits");
        assert_eq!(Policy::Cached, Policy::from("cached"), "serves hits only");
        assert_eq!(Policy::Always, Policy::from(""), "unset is the default");
        assert_eq!(
            Policy::Always,
            Policy::from("Never"),
            "spellings are case-sensitive"
        );
    }

    /// Every reason a run gives no outcome renders apart from the others, a
    /// refusal carrying a form or a value names it, and the statuses no run
    /// exits with read as one reason.
    #[test]
    fn every_declined_run_renders_its_own_reason()
    {
        let mut function = Function::default();
        let label = function.label();
        let unbound = function
            .target(label)
            .expect_err("a label never bound has no target");
        let reply = HeapValueId::from(7_u32);
        let migration = CommandId::from(5_u32);
        let reasons = [
            Declined::from(Form::ConsumerFields),
            Declined::NoPatcher,
            Declined::from(unbound),
            Declined::Uncached,
            Declined::Stuck,
            Declined::Exhausted(Status::FuelExhausted),
            Declined::Exhausted(Status::HeapExhausted),
            Declined::Exhausted(Status::FramesExhausted),
            Declined::Exhausted(Status::Running),
            Declined::from(TransferRefusal::Producer),
            Declined::Reply(reply),
            Declined::Capture(reply),
            Declined::Environment,
            Declined::Migration(migration, Unmigrated::Unanswered),
            Declined::Migration(migration, Unmigrated::UnboundWorld),
        ];
        assert_eq!(
            Declined::Unbound,
            reasons[2],
            "an unbound label is its own reason"
        );
        assert_eq!(
            Declined::Transfer(TransferRefusal::Producer),
            reasons[9],
            "a transfer refusal is carried"
        );
        let mut rendered: Vec<String> = reasons.iter().map(ToString::to_string).collect();
        let count = rendered.len();
        rendered.sort();
        rendered.dedup();
        assert_eq!(rendered.len(), count, "{rendered:?}");
        assert!(
            reasons[0]
                .to_string()
                .contains(Form::ConsumerFields.to_string().as_str()),
            "names the refused form"
        );
        assert!(
            reasons[10].to_string().contains(reply.to_string().as_str()),
            "names the reply"
        );
        assert!(
            reasons[11].to_string().contains(reply.to_string().as_str()),
            "names the capture"
        );
        assert!(
            reasons[13]
                .to_string()
                .contains(NodeAddress::Command(migration).to_string().as_str()),
            "names the migration"
        );
        for status in [Status::Halted, Status::Unmatched, Status::Stuck] {
            assert_eq!(
                Declined::Exhausted(status).to_string(),
                reasons[8].to_string()
            );
        }
    }
}
