//! Copy-and-patch emission of the L machine's lowered commands. In the
//! storage picture a run's heap, frame and window regions are a LAM, a
//! location-addressable memory of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`:
//! a value stands at a location in its thread's regions, meaningful to that
//! run alone, and the thread's next run reuses them. They realise LAM's
//! materialisation, duplication and evacuation, and depart from it where a
//! freed block is reused and a block one owner holds is rebuilt in place, as
//! the run module states. What leaves a run moves into the caller's store. Its
//! wall is validity, upstream: it runs only a command the checker admitted.
//!
//! A command the checker admitted is lowered to a straight list of stencil
//! instructions ([`lower()`]), and that one list runs on either of two tiers
//! ([`Tier`]): native code copied stencil by stencil into executable memory
//! and patched in place, served from a cache keyed by the lowered function's
//! content; or the portable executor, which dispatches the same stencil
//! functions through a table. A run's outcome is moved into the caller's
//! store, so readback reads it ([`evaluate`]). The executor is the reference
//! native code is held to; a command the lowering refuses declines by the
//! form it refused.
//!
//! Before either tier runs it, each adjacent pair of instructions a rule
//! names ([`Rule`]) runs as one superinstruction. Each fusion is a decision
//! that [`replay`] re-derives from the unfused lowering ([`lower_unfused`]),
//! and each saves one dispatch ([`dispatches`]).
//!
//! # One definition, two tiers
//!
//! The L machine's transitions are written once, in the stencil crate. Its
//! default build is the executor: each hole is a function that reads the
//! current instruction record. Compiled under `--cfg gandr_stencil_object`,
//! which this crate's build script does with the toolchain's own `rustc`,
//! each hole is an undefined symbol and the object's relocations are the
//! patcher's input. The build script reads the object — each `stencil_*`
//! function's bytes and relocations — and refuses one it cannot patch,
//! checking the stencil list against the executor's
//! (`gandr_runtime_stencils::StencilId::ALL`), so the two tiers cannot drift.
//!
//! **Choice.** The executor lands with the emitter rather than after it. The
//! stencil crate's library build must link — an object with undefined holes
//! cannot — and its own tests witness its stencils, so its default build
//! defines the holes, and that definition is the executor. **Alternative.**
//! A stencil crate that builds only as an object, the executor a later
//! landing; declined because the crate's witnesses would then live in another
//! package. **Reversal.** None foreseen: the executor is the tier every host
//! without a patcher takes.
//!
//! # The policy
//!
//! [`Policy`] reads `GANDR_NATIVE` once per process: `always` (the default)
//! emits a function on its first run and serves it from the process's cache
//! after; `never` takes the executor; `cached` serves a function the cache
//! already holds and takes the executor otherwise, which is what a
//! differential between the tiers wants.
//!
//! **Choice.** Emit on the first run. A function is lowered from its source
//! in every process, so a gate on a run count before emitting would skip only
//! the first run — the one the cache cannot serve — and save nothing; the
//! cache that would make such a gate useful is the persistent, content-keyed
//! one that serves code across processes, which lands with the run memo.
//! **Alternatives.** An item per constant, so a shared helper is emitted once,
//! waits for a workload where shared helpers dominate; tiering a step at a
//! time by heat is the whole profile-guided design and declined here.
//! **Reversal.** The persistent cache, when it lands, keys the same
//! [`Function`] by content and serves it before emission.
//!
//! # The patchers
//!
//! Three hosts have a patcher, selected by the build script's `gandr_patcher`
//! configuration: arm64 on macOS (Mach-O, `BRANCH26` continuations,
//! `GOT_LOAD` pairs) and on Linux (ELF under the default position-independent
//! model, the same three kinds as `JUMP26` and `ADR_GOT_PAGE` /
//! `LD64_GOT_LO12_NC`), each pair relaxed to `movz`/`movk` or `adrp`/`add`;
//! and Linux x86-64 (ELF under the static relocation model, `PLT32`/`PC32`
//! displacements and `32`/`32S` absolute fields). Every other host takes the
//! executor. The x86-64 patcher applies each relocation's addend as a linker
//! does — the compiler folds an immediate's bias into it — where a patcher
//! refusing explicit addends would refuse every RIP-relative operand; the
//! arm64 object carries none, and the build script refuses one. Executable
//! memory is a `MAP_JIT` mapping toggled per thread on macOS and a `memfd`
//! mapped twice, writable and executable, on Linux — the executable view below
//! 2 GiB on x86-64; the region module states why.
//!
//! # The runtime support
//!
//! Each thread keeps its own heap, frame region, window region and entry
//! window, each allocated
//! at its bound and committed as a run first touches it; a run that would
//! pass a bound takes that region's exit and is declined. A run enters
//! through `enter` or `execute` with a fresh
//! [`gandr_runtime_stencils::Runtime`] record and a halting sentinel frame
//! under the base mark, and returns when an exit stencil writes its
//! status. Emitted code carries no unwind tables and calls only the host
//! entry, `host::enter`, which never unwinds: it evaluates primitives and
//! answers control — operations, captures, replays, reified stacks and the
//! memory forms — over the run's frame region, by the tables the lowering
//! wrote. That seam is where a Rust host — the dispatcher today — calls
//! emitted code, and where emitted code calls back.
//!
//! # The interpreter and the compile host retired
//!
//! This crate replaces two paths. An MLIR-hosted compile path rendered a
//! small positive fragment through a dialect; a hand-written L machine in
//! `gandr-core-sequent` stepped every other command through a dispatch loop
//! and was the oracle both tiers answered to. **Choice.** Emit from stencils
//! the toolchain compiles, so the native tier needs no compiler at run time,
//! and let the executor built from the same stencils be the reference and
//! the fallback both. **Alternatives.** A dialect lowered through MLIR per
//! item; declined for its compile latency and its native toolchain
//! dependency, neither of which buys an optimisation the stencils lack. A
//! hand-written interpreter kept beside the stencils as an independent
//! oracle; declined because two implementations of one transition table are
//! held together only by tests, which the corpus's stated runs and
//! normalisation by evaluation already supply. **Reversal.** An MLIR-hosted
//! dialect returns only if a dialect-level optimisation the certificates
//! cannot express is measured as needed; a second interpreter only if the
//! stated answers stop catching a stencil error the corpus reaches.
//!
//! **Thunks are called by name.** A thunk forced twice runs its body twice,
//! where the retired machine wrote each forcing's value back to a memo cell.
//! A pure body answers the same either way, and a linear one cannot be
//! forced twice; only the cost differs. **Alternative.** An update frame
//! per forcing writing the value back into the thunk, declined until a
//! measured run shows a shared thunk's re-forcing to dominate. **Reversal.**
//! That measurement; the update frame is the machine's design, ready to
//! port.
//!
//! # Dependencies
//!
//! The build script reads the stencil object with `object` (read-only, ELF
//! and Mach-O): one relocation view over both formats, maintained with the
//! toolchain's own backtrace and linker tools. `goblin` was the alternative,
//! declined for its per-format relocation types; the choice reverses if a
//! third format needs a reader `object` lacks. Executable memory is mapped
//! through `libc`: `rustix`, already in the graph, exposes neither `MAP_JIT`
//! nor `pthread_jit_write_protect_np`; the choice reverses if it grows both.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: the
//!   LAM a run's regions are, a regioned store whose locations no other run
//!   or world reads.

// Module documentation that predates the shape lint: 6 headings outside the
// vocabulary, 5 decision records, 1 issue reference and 3 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]

extern crate alloc;

pub mod crossing;
mod executor;
mod function;
mod fuse;
mod host;
mod lower;
#[cfg(gandr_patcher)]
mod native;
mod run;
mod seam;
mod transfer;
pub mod world;

pub use gandr_runtime_stencils::Fuel;
pub use gandr_runtime_stencils::Status;

pub use crate::function::Function;
pub use crate::function::Position;
pub use crate::fuse::Dispatches;
pub use crate::fuse::Fused;
pub use crate::fuse::FusionRefusal;
pub use crate::fuse::Rule;
pub use crate::fuse::dispatches;
pub use crate::fuse::replay;
pub use crate::host::release;
pub use crate::lower::Form;
pub use crate::lower::Lowered;
pub use crate::lower::OwnerRun;
pub use crate::lower::Window;
pub use crate::lower::lower;
pub use crate::lower::lower_suspended;
pub use crate::lower::lower_unfused;
#[cfg(gandr_patcher)]
pub use crate::native::EmitRefusal;
pub use crate::run::Declined;
pub use crate::run::POLICY_VARIABLE;
pub use crate::run::Policy;
pub use crate::run::Tier;
pub use crate::run::evaluate;
pub use crate::run::evaluate_closed_on;
pub use crate::run::evaluate_on;
pub use crate::run::evaluate_on_with_host;
pub use crate::run::evaluate_unfused_on;
pub use crate::run::evaluate_with_host;
pub use crate::seam::HostHandler;
pub use crate::seam::HostOutcome;
pub use crate::seam::HostReply;
pub use crate::seam::HostRequest;
pub use crate::seam::HostValues;
pub use crate::seam::Migrated;
pub use crate::seam::MigrationRequest;
pub use crate::transfer::TransferRefusal;

/// Whether this host has a patcher: native code runs here.
pub const PATCHER: bool = cfg!(gandr_patcher);
