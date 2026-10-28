# gandr-runtime-emitter

Copy-and-patch emission of the L machine's lowered commands: native code under a content cache where the host has a patcher, the portable executor everywhere else.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [Mutation backlog](#mutation-backlog)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `lower` turns a focused command into a `Function`: a straight list of stencil instructions over one slot per binder, frames on the frame region, constructor fields pushed before their constructor and constants in the function's data. `evaluate` runs it on the tier the process's policy picks and moves the outcome into the caller's `Store`, where readback reads it; `evaluate_on` runs one tier. A command outside the lowered fragment is `Declined` by the form the lowering refused.

**Why.** Emitted code runs the L machine's transitions with the registers pinned and no dispatch loop, and the emission cost is a copy and a few patches per stencil; the executor built from the same stencils runs them anywhere and is the reference native code answers to. It replaces the MLIR compile host and the hand-written machine: `src/lib.rs` states both decisions and what would reverse them.

**How.** The build script compiles `gandr-runtime-stencils` under `--cfg gandr_stencil_object` with the toolchain's own `rustc`, reads the object with `object`, refuses any section, symbol or relocation the patcher cannot take, and writes the stencil table. Emission copies each instruction's stencil into a region of executable memory and patches its holes: operands, the next copy, a label, the shared exits. arm64 patches `BRANCH26` (ELF `JUMP26`) and relaxes `GOT_LOAD` pairs (ELF `ADR_GOT_PAGE`/`LD64_GOT_LO12_NC`) on macOS and Linux alike; Linux x86-64 patches `PLT32`/`PC32` displacements and `32`/`32S` absolute fields under the static relocation model. Emitted functions live in a process-wide cache keyed by the function's content. The executor tier builds an instruction array from the same `Function` and runs the same stencil functions through their dispatch table.

## References

- Haoran Xu and Fredrik Kjolstad. "Copy-and-Patch Compilation: A Fast Compilation Algorithm for High-Level Languages and Bytecode." _Proceedings of the ACM on Programming Languages_ 5 (OOPSLA), article 136, 2021. [doi:10.1145/3485513](https://doi.org/10.1145/3485513). The algorithm: stencils with holes, copied and patched per item.
- [`object`](https://docs.rs/object/0.40.0/object/): the relocation view over ELF and Mach-O the build script reads the stencil object through.
- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — the LAM, a regioned location-addressable store, that a run's regions are.
- `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design (§ futures-in-gandr item 1) — a cut's writer is its producer run on its own, which `evaluate_closed_on` runs apart from its reader's heap.
- `Pruiksma-2022-back_futures` — background: Klaas Pruiksma and Frank Pfenning. "Back to Futures." _Journal of Functional Programming_ 32, e6, 2022. [doi:10.1017/S0956796822000016](https://doi.org/10.1017/S0956796822000016) — § 4's configurations: a cut's one writer fills its cell, and a reader waits for it.
- `Racordon-2020-formal_definition_swifts_value_semantics` — background: Dimitri Racordon, "A Formal Definition of Swift's Value Semantics", 2020 — value semantics as copies, the independence a rebuild in place must keep.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage programme's memory-model reading (§ storage-programme-memory-model-reading) — LAM as the value representation's specification, and `storage-conjecture-exclusivity`.
- `vault:01a178aa-608d-75d0-8f71-e6fe4289f327` — lineage: the compiled runtime's representation question (§ runtime-question-what-runtime-means).
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: verdict reuse (§ kernel-verdict-reuse) — a host's reply read from verified chunks is checked for integrity alone; its reply type stays the host's to keep.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation ruling — a run records its channels' plays only when its caller asks.
- `vault:01a178aa-a1a9-7643-b2d9-98059c9273fb` — background: the effects page (§ One-shot linearity) — a clause's stack resumed or abandoned once; the frames left standing are the case a clause's body shows to resume at most once.

## Provided features

- `lower`, `Lowered`, `Function`, `Form`: the lowering, its closure sites and reified frames, the function it builds and the form it refuses.
- `Lowered::handlers` and `Lowered::marker`: each handler's clauses with the path an operation takes to each. A clause that resumes its stack only from its tail position, or never names it, runs on the frames left standing under the marker; any other has them captured into a stack.
- `lower_unfused`, `Rule`, `Fused`, `replay`, `FusionRefusal`, `dispatches`: the lowering before its adjacent pairs run as superinstructions, the rules that fuse them, the trace a fused function carries, the replay that re-derives it and its cost in dispatches.
- `evaluate`, `evaluate_on`, `evaluate_unfused_on`, `RunInputs`, `Tier`, `Declined`, `TransferRefusal`: a run under the policy or on one tier, fused or unfused, over the inputs the caller builds on its store, its outcome moved into that store, or why it gave none.
- `evaluate_with_host`, `evaluate_on_with_host`, `HostHandler`, `HostRequest`, `HostReply`, `HostOutcome`, `HostValues`: a run whose unhandled operations are offered to the caller, who answers, declines or aborts each, and may commit a payload to the value plane or deref a value from it as a reply. `HostHandler::migrate`, `MigrationRequest`, `Migrated`: the host decides where each migration runs — here, at another host whose answer it reads back, or nowhere, refused.
- `evaluate_closed_on`, `lower_suspended`: a command binding one covariable run over the values a store environment binds, laid out on the run's heap first: a cut's writer run apart from its reader's heap.
- `evaluate_cut_on`, `Writer`, `Reader`, `Forked`, `CELL`, `READ`: a cut's writer and reader joined on the caller's fork, the writer the left half; the reader's perform of `READ` of `CELL` replies with the writer's answer, crossed into its store.
- `crossing::{commit, deref, profile, CrossingRefusal, Uncrossable}`: a store's value committed to the value plane and read back into another store, fresh there: a literal or a constructor over crossing fields crosses, sharing unfolded, a thunk crosses as its body's command and its captures, and a closure, a stack, a code, a capability, an opaque constant or a session's record is refused by name.
- World forms run: `hold v` delivers `v`, `leta` binds the handle's content, and `migrate [w] { t }` runs where the host decides; here, `t` runs on a thread and over a store of its own, its captures crossed in and its answer crossed back by `crossing` through the one chunk store the process holds, and a thunk it answers is laid out at the site the caller's function keeps for each thunk literal the body reaches. `world::arrive` runs a migration another host shipped, by its place in the program both hosts hold, over captures read into a fresh store, and names why one ran nowhere by `gandr-core-term`'s `world::Unmigrated`. A value that does not cross, a body that answers nothing, or a host's refusal is `Declined::Migration`.
- Sessions run: `fork`, `send`, `recv`, `select`, `offer` and `close` are host calls on one cooperative, deterministic scheduler the run's host state holds, on the run's thread. A channel keeps one queue per direction; a receive or an offer with nothing sent parks its task's frames until its peer sends, and a run whose tasks all wait is `Stuck::Deadlock`, naming each waiting action. An end an abandoned stack's frames hold before its protocol ended is cancelled, read off the linear slots `Sites::linears` names for each frame: its queued payloads are released, an end among them cancelled too, and a waiting peer abandoned; a peer's later send or selection, or a receive or an offer with nothing queued, abandons that peer's continuation, and a root so abandoned is `Stuck::Cancelled` at that action.
- `RunInputs::traced`, `Trace`, `Play`, `Played`, `Carried`, `TaskNumber`, `ChannelNumber`: a run that records each channel it forks as a play, every move with the task and side that made it and its payload's place in the store, and reads a play's causal web, `Play::web`, by the facing rule a dialogue's is read by. A run over inputs not traced records nothing.
- `Policy` and `POLICY_VARIABLE`: `GANDR_NATIVE=always` (the default) emits on first run, `never` takes the executor, `cached` serves only what the cache holds.
- `PATCHER`: whether this host emits native code.
- `Fuel` and `Status`, re-exported: the code-word jumps a run may take, and why it returned.

## Expected features

- **A host with a patcher for native code.** arm64 on macOS or Linux, and Linux on x86-64; every other host runs the executor, with the same answers.
- **Executable memory.** macOS grants `MAP_JIT` to an unsigned or ad-hoc signed binary; a hardened-runtime binary needs the `com.apple.security.cs.allow-jit` entitlement. Linux needs `memfd_create`, and on x86-64 a mapping below 2 GiB.
- **Constants by position.** A constant the `Definitions` given do not hold sticks where a run reads it; an opaque one is carried as itself, and a run that observes it stops naming the constant, which the dispatcher blames.

## Examples

The emitter's witnesses run the named programs on both tiers and under the policy, each answer compared value by value with the executor's and with the answer the program states, and the host seam's operations answered, declined and aborted; the stencil crate's suite runs the generated programs and the corpus through the same paths.

```sh
cargo test -p gandr-runtime-emitter
GANDR_NATIVE=never cargo run -p gandr-lang -- test corpus/model
```

## Where the detail lives

`src/lib.rs` states the tiers, the policy, the patchers, the runtime support, the retired interpreter and compile host and the call-by-name thunks, each with its alternatives and reversal; `src/lower.rs` the linear form; `src/fuse.rs` the superinstructions, their replay and their cost; `src/run.rs` the regions, their bounds, the value representation against the LAM and the exclusivity conjecture's witnesses; `src/seam.rs` the host seam; `src/native.rs` and its `table`, `memory`, `aarch64` and `x86_64` modules emission, regions and patching; `src/transfer.rs` how an outcome reaches the store; `src/crossing.rs` the value plane's tag table, the sharing a crossing unfolds and what it refuses; `src/world.rs` a migration's far run, the process's chunk store and what a migration does not yet do; `build.rs` the stencil table and every refusal it makes.

## Mutation backlog

A standalone campaign over this crate's first landing should mutate the patch arithmetic in `src/native/aarch64.rs` and `src/native/x86_64.rs` (page offsets, displacements, addends, reach checks), the lowering's slot and label assignment, and the transfer's field order and capture binding. Hypotheses: the agreement suites reject a changed answer or a crash on either tier; the build script's refusals reject an unpatchable relocation. No mutation score is claimed.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
