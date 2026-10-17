//! Running a lowered command: the tier the policy picks, the content cache
//! native code is served from, the regions a run uses, and the answer moved
//! into the machine's store.
//!
//! A run lowers its command every time — the lowered function is the cache
//! key, compared by value — and either serves the function's emitted code
//! from the process's cache, emitting it on a miss, or builds the executor's
//! program. Both run over the calling thread's heap and frame regions; an
//! exhausted region is doubled and the run repeated from its start, up to a
//! bound past which the L machine runs the command instead. A run is pure,
//! so a repeated run answers as the first would have.

use alloc::sync::Arc;
use core::cell::RefCell;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Store;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Status;
use gandr_runtime_stencils::Word;

use crate::executor::Program;
use crate::function::Unbound;
use crate::host;
use crate::host::Calls;
use crate::host::Codes;
use crate::lower::Form;
use crate::lower::Lowered;
use crate::lower::lower;
#[cfg(gandr_patcher)]
use crate::native::EmitRefusal;
#[cfg(gandr_patcher)]
use crate::native::Emitted;
#[cfg(gandr_patcher)]
use crate::native::Native;
use crate::transfer::Sites;
use crate::transfer::Tables;
use crate::transfer::TransferRefusal;
use crate::transfer::observed;
use crate::transfer::transfer;

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

/// Why a run did not answer: the L machine runs the command instead.
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
    /// A case met a constructor no arm answers: the machine's stuck answer.
    Unmatched,
    /// An observation met a value it does not observe, or a host call refused
    /// its operands: the machine's stuck answer, which it names.
    Stuck,
    /// An observation — a force, an application, a case — met the opaque
    /// constant: the machine's stuck answer at it, which blames the constant.
    Opaque(ConstantIndex),
    /// The run spent its fuel, or a region past its bound.
    Exhausted(Status),
    /// The answer could not be moved into the store.
    Transfer(TransferRefusal),
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

/// The regions a run uses, per thread.
#[derive(Debug)]
struct Buffers
{
    /// The heap region.
    heap: Vec<Word>,
    /// The frame region, the sentinel frame in its first two words.
    frames: Vec<Word>,
    /// The entry window.
    window: Vec<Word>,
}

/// The heap region's first size, in words.
const HEAP_WORDS: usize = 1 << 16;
/// The heap region's bound, in words: past it the machine runs the command.
const HEAP_BOUND: usize = 1 << 25;
/// The frame region's first size, in words.
const FRAME_WORDS: usize = 1 << 14;
/// The frame region's bound, in words.
const FRAME_BOUND: usize = 1 << 23;

std::thread_local! {
    /// The calling thread's regions.
    static BUFFERS: RefCell<Buffers> = RefCell::new(Buffers {
        heap: alloc::vec![Word::ZERO; HEAP_WORDS],
        frames: alloc::vec![Word::ZERO; FRAME_WORDS],
        window: Vec::new(),
    });
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

/// Run `root` under the process's policy and move its answer into `store`.
///
/// # Specification
/// - ensures: as [`evaluate_on`], on the tier the policy picks: native under
///   [`Policy::Always`] where a patcher exists, the executor under
///   [`Policy::Never`] and on a miss under [`Policy::Cached`].
/// - executable: none — agreeing with the machine is the differential's to
///   show; a postcondition would run the machine on every call.
///
/// # Errors
/// As [`evaluate_on`].
///
/// # Adequacy
/// - hypothesis: L2 — every named program runs through this entry and is
///   compared with the machine's answer; the policy's spellings are witnessed
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
) -> Result<HeapValueId, Declined>
{
    let policy = *POLICY;
    let tier = match policy {
        Policy::Always if cfg!(gandr_patcher) => Tier::Native,
        Policy::Always | Policy::Never => Tier::Executor,
        Policy::Cached => {
            let lowered = lower(arena, definitions, root)?;
            return run_cached(&lowered, arena, fuel, store);
        },
    };
    evaluate_on(tier, arena, definitions, root, fuel, store)
}

/// Run `root` on `tier` with `fuel` code-word jumps and move its answer into
/// `store`.
///
/// # Specification
/// - requires: every constant `root` reaches is defined in `definitions`.
/// - ensures: on success the store holds the answer the L machine would halt
///   with, as its readback reads it, and the answer's id is returned.
/// - executable: none — agreeing with the machine is the differential's to
///   show; a postcondition would run the machine on every call.
///
/// # Errors
/// [`Declined`] naming why the command did not run on the tier: the machine
/// runs it instead.
///
/// # Adequacy
/// - hypothesis: L2 — the named programs run on both tiers and the machine, and
///   their answers are compared value by value.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub fn evaluate_on(
    tier: Tier,
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
{
    let lowered = lower(arena, definitions, root)?;
    match tier {
        Tier::Native => run_native(&lowered, arena, fuel, store),
        Tier::Executor => run_executor(&lowered, arena, fuel, store),
    }
}

/// Run on the executor.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
fn run_executor(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
{
    let program = Program::build(&lowered.function)?;
    let sites = Sites::new(&lowered.sites, |site| {
        program
            .code(&lowered.function, site.label)
            .unwrap_or(Word::ZERO)
    });
    run(
        Code::Executor(&program),
        Codes::Executor(&program, &lowered.function),
        lowered,
        &sites,
        arena,
        fuel,
        store,
    )
}

/// Run emitted code, emitting on a miss.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
#[cfg(gandr_patcher)]
fn run_native(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
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
    run_emitted(&emitted, lowered, arena, fuel, store)
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
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
{
    let _ = (lowered, arena, fuel, store);
    Err(Declined::NoPatcher)
}

/// Serve cached code, or take the executor on a miss.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
fn run_cached(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
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
            return run_emitted(&emitted, lowered, arena, fuel, store);
        }
    }
    run_executor(lowered, arena, fuel, store)
}

/// Run code the cache served.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
#[cfg(gandr_patcher)]
fn run_emitted(
    emitted: &Emitted,
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
{
    let sites = Sites::new(&lowered.sites, |site| {
        emitted
            .labels
            .get(usize::from(site.label))
            .copied()
            .unwrap_or(Word::ZERO)
    });
    run(
        Code::Native(emitted.entry, emitted.halt),
        Codes::Native {
            labels: &emitted.labels,
            stubs: &emitted.stubs,
        },
        lowered,
        &sites,
        arena,
        fuel,
        store,
    )
}

/// Run `code` over the calling thread's regions, growing an exhausted one
/// and running again, and move the answer into `store`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
fn run(
    code: Code<'_>,
    codes: Codes<'_>,
    lowered: &Lowered,
    sites: &Sites<'_>,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
) -> Result<HeapValueId, Declined>
{
    BUFFERS.with_borrow_mut(|buffers| {
        loop {
            buffers.window.clear();
            buffers
                .window
                .resize(lowered.function.slots().0.max(1), Word::ZERO);
            let halt = match code {
                #[cfg(gandr_patcher)]
                Code::Native(_, halt) => halt,
                Code::Executor(program) => program.halt(),
            };
            let &mut [ref mut sentinel_code, ref mut sentinel_window, ..] =
                buffers.frames.as_mut_slice()
            else {
                return Err(Declined::Exhausted(Status::FramesExhausted));
            };
            *sentinel_code = halt;
            *sentinel_window = Word::ZERO;
            let heap = buffers.heap.as_mut_ptr();
            let heap_limit = heap.wrapping_add(buffers.heap.len());
            let frames = buffers.frames.as_mut_ptr();
            let frame_limit = frames.wrapping_add(buffers.frames.len());
            let base = frames.wrapping_add(2);
            let window = buffers.window.as_mut_ptr();
            let mut calls = Calls::new(lowered, codes);
            let mut runtime = Runtime::new(
                heap,
                heap_limit,
                frame_limit,
                base,
                fuel,
                host::enter,
                Word::from_pointer(&raw mut calls),
            );
            let answer = match code {
                #[cfg(gandr_patcher)]
                // SAFETY: the entry is a copy the emitter patched in a region
                // the cache keeps mapped; the regions are this thread's,
                // valid up to their limits, the sentinel frame below the base
                // mark, and the window holds the function's slots.
                Code::Native(entry, _) => unsafe {
                    gandr_runtime_stencils::enter(entry, &raw mut runtime, heap, base, window)
                },
                // SAFETY: the program was built from this function and lives
                // for the call; the regions are as above.
                Code::Executor(program) => unsafe {
                    gandr_runtime_stencils::execute(
                        program.entry(),
                        &raw mut runtime,
                        heap,
                        base,
                        window,
                    )
                },
            };
            match runtime.status() {
                Ok(Status::Halted) => {
                    let tables = Tables {
                        heads: &lowered.heads,
                        literals: calls.literals(),
                    };
                    // SAFETY: the run halted; its heap and the function's
                    // constants are live until this closure returns.
                    return unsafe { transfer(answer, sites, tables, arena, store) }
                        .map_err(Declined::from);
                },
                Ok(Status::HeapExhausted) if buffers.heap.len() < HEAP_BOUND => {
                    let doubled = buffers.heap.len().saturating_mul(2);
                    buffers.heap.resize(doubled, Word::ZERO);
                },
                Ok(Status::FramesExhausted) if buffers.frames.len() < FRAME_BOUND => {
                    let doubled = buffers.frames.len().saturating_mul(2);
                    buffers.frames.resize(doubled, Word::ZERO);
                },
                Ok(status @ (Status::Unmatched | Status::Stuck)) => {
                    // SAFETY: both exits return the value they observed, or
                    // zero when a host call refused, and the heap is live.
                    if let Some(constant) = unsafe { observed(answer) } {
                        return Err(Declined::Opaque(constant));
                    }
                    return Err(if status == Status::Unmatched {
                        Declined::Unmatched
                    }
                    else {
                        Declined::Stuck
                    });
                },
                Ok(status) => return Err(Declined::Exhausted(status)),
                Err(_unknown) => return Err(Declined::Exhausted(Status::Running)),
            }
        }
    })
}

#[cfg(test)]
mod tests
{
    use super::Policy;

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
}
