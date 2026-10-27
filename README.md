# gandr

[![CI](https://github.com/gandr-lang/gandr/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/gandr-lang/gandr/actions/workflows/ci.yml) [![Nightly](https://github.com/gandr-lang/gandr/actions/workflows/nightly.yml/badge.svg?branch=main)](https://github.com/gandr-lang/gandr/actions/workflows/nightly.yml) [![codecov](https://codecov.io/gh/gandr-lang/gandr/graph/badge.svg)](https://codecov.io/gh/gandr-lang/gandr) [![licence](https://img.shields.io/badge/license-Apache--2.0_WITH_LLVM--exception-blue)](LICENSE.Apache-2.0.txt) [![rustc](https://img.shields.io/badge/rustc-nightly--2026--06--25-blue)](rust-toolchain.toml)

gandr is a dependently typed language for systems programming and industrial-scale mathematics in one tree, with a rewriting core and a replaying kernel. A program and a proof are one kind of object; a compiled artifact is a projected endpoint of a choreography, and a single local binary is that picture's degenerate case. The rule that holds it together: **keep the information other settings discard — counts, costs, distances, dependencies, decisions, sharing, place — and act on it**, so identity, incrementality, parallelism and distribution follow from what the checker knows instead of arriving as runtimes.

## The picture

**One choke point; replay, never trust.** A call-by-push-value core is checked by a defunctionalised machine over a flat content-addressed term arena (`crates/kernel-core`). Every declaration is re-checked before admission; a conversion an untrusted engine decides is replayed from its trace; a verdict reused is attested by its key, never by a hash alone. Integrity (bytes) and validity (replay) are two walls that never substitute for each other.

**Rewriting is the meaning of a rule.** Rule blocks are cells; completion, critical pairs and coherence tiers settle them; a run's steps carry their footprints, so the causal web, the flow projection and fusion read dependence and cost off the derivation (`crates/theory-*`, `ledger/concerns.sql`). One structure runs through the concurrency side — events labelled by footprints, an independence relation, a commuting square per independent pair — and template games, the causal web, message theories and atomic flows are its faces. Univalence is a theorem gandr builds toward, not an axiom it assumes.

**Types carry the quantities.** Dependent types with grades: today two points (`One`, `Many`) and capability grades; the intended carrier is quantale-valued, so a grade is a count, a cost or a distance and fusion can state what it saves. Modes give multiplicity, extent and locus; `A at w` says where a value is meaningful; `mobile` is authority and `Open` is representation. Effects are theories with handlers; capabilities are context hypotheses a handler supplies — no ambient authority, and sandboxing is the capability row.

**Two memories, one key space.** The storage tier is one content-addressable memory, the CAM (`crates/storage-*`: typed content-defined chunking, `cam_commit`/`cam_deref`, records as an authenticated search tree). Each world runs location-addressable heaps, its LAMs (regions, never recycled). Inside a world a value crosses by location; across worlds and sessions by content, with a locality bound on what an edit re-sends (`crates/README.md` § Storage and distribution).

**Incremental is the general case.** Checking tracks what each judgement read, so a change invalidates exactly its dependents and batch checking is the degenerate run (`crates/core-incremental`); parallel replay and migration consume the same bookkeeping.

**Oracles and sheaves.** Which part of a judgement is computed and which is decided by certificate replay is a modality over one substrate: the elaborator regime is the implemented oracle, the certificate regime the unimplemented one. The supports a judgement records are what incrementality, parallel replay and distributed migration glue together — the sheaf reading of the same bookkeeping.

**Worlds, sessions, choreographies.** A world is reachable by key; coordination is a session whose failure arms are branches of its type; `migrate [w] { t }` ships a closed configuration by content. Hand-written sessions are the foundation and the yardstick: a choreography is projected into them, one closed endpoint per role, and the build layer — store, recipe, builder, sandbox, memo, provenance, lock, all gandr's — provisions endpoints into processes, containers or unikernels. Deployment binds roles to world keys and never enters identity.

**Zero cost, checked.** A runtime component is demanded by a type — a grade above zero, a crossing, a branch — or it is a recipe policy off by default (run-time admission, session monitors, failure detection, dynamic providers, tracing). Nothing else runs, and a projected form is measured against the hand-written one.

## Built, and owed

Built: the kernel and its replay; the checker, NbE, the sequent machine and incremental checking; the CAM's value and record planes behind one store; the native emitter (copy-and-patch machine code); the foreign boundary (`extern` performed by the host); eight host interfaces, `Net` over an authenticated QUIC endpoint among them; two-point grades, located types and `Open`; grammar to driver, language server, MCP server, TUI and VS Code extension. Owed, each with its issue: the CAM over the wire and `migrate` between processes (#3184), futures as a theory with executors as models (#3191), remote imports and dynamic providers (#3195), choreographic projection and the deployment recipe (#3216), the build layer (#2765), quantale grades (#3166), univalence as a theorem (#212).

## Where to look

`crates/README.md`: layering, every crate, the storage-and-distribution topology, the concern map. `ledger/README.md`: the ledgers. Every change answers seven readings — identity, oracle, descent, located, resident, rewriting, zero-cost — and three concerns — fork, oracle, sharing — in its issue and PR (`.github/ISSUE_TEMPLATE/unit.yml`, `ledger/concerns.sql`): start there.

## Use and build

```sh
mise install && cargo build --release -p gandr-lang
gandr check crates/surface-corpus/strict   # every declaration checks, owing nothing
gandr run corpus/model/effects/hello.gandr # check, then run `main`
gandr test corpus                          # every fixture and pending source
mise run check                             # every gate
```

Exit codes: `0` settled, `1` a declaration did not, `2` an engine fault or a bad invocation. The [driver](crates/surface-driver/README.md) states every verb (`fmt`, `lsp`, `mcp`, `view`, `repl`, `tui`); `lsp` and `mcp` share one engine hub per workspace, and [`contrib/gandr-vscode`](contrib/gandr-vscode/README.md) connects to it.

## License

Apache-2.0 WITH LLVM-exception. See `LICENSE.Apache-2.0.txt` and `LICENSE.LLVM-exception.txt`.
