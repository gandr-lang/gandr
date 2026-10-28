# gandr

[![CI](https://github.com/gandr-lang/gandr/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/gandr-lang/gandr/actions/workflows/ci.yml) [![Nightly](https://github.com/gandr-lang/gandr/actions/workflows/nightly.yml/badge.svg?branch=main)](https://github.com/gandr-lang/gandr/actions/workflows/nightly.yml) [![codecov](https://codecov.io/gh/gandr-lang/gandr/graph/badge.svg)](https://codecov.io/gh/gandr-lang/gandr) [![licence](https://img.shields.io/badge/license-Apache--2.0_WITH_LLVM--exception-blue)](LICENSE.Apache-2.0.txt) [![rustc](https://img.shields.io/badge/rustc-nightly--2026--06--25-blue)](rust-toolchain.toml)

gandr is a dependently typed programming language for systems programming and mathematics in one tree.

## Synopsis

### Built for agents

Programs are increasingly written, checked and repaired by software agents. A language built for a human at a keyboard serves them badly. An agent needs to see the state of a check, not a wall of output. It needs to stop, inspect and resume partial work. It needs to be told what would complete a broken input. It needs to hand over evidence that another party can verify instead of trust. gandr is designed from the ground up for this.

The flagship application is domhringr, a software factory. Agent sessions do the work. Judges grade the work against rubrics. Playbooks say what a session does and how it reports. Every durable fact in the factory is content-addressed and signed, every participant is an endpoint, and there is no server. gandr is domhringr's language and its substrate. The decisions in the sections below are what that application demands: a checker whose state is data, incremental work at the finest grain, verdicts that are replayed instead of believed, and a parser that resumes and says what it needs.

One principle sits under all of it: the checker's state is data. Type checking is a machine whose stack is a data structure, not the host's call stack. The solver is a second machine with its own inspectable state. The whole state can be serialised and resumed. The properties that make the surface fast enough for interactive use are introspective state, resumption, and encoders over one state instead of logic implemented twice. The same properties make the surface steerable by an agent.

- `crates/kernel-core` — the checking machine
- `crates/core-incremental` — the machine's state checkpointed and resumed
- `crates/surface-session` — a session over the checker, resumed and inspected
- `crates/surface-mcp` — the Model Context Protocol face agents drive
- `corpus/model/effects/domhringr.gandr` — the factory's host interfaces, in gandr

### Incremental by default

An agent edits in small steps and asks a question after each one. Rechecking a whole project after a one-line edit does not scale for that, for a human, or for a proof assistant. The usual answer tracks dependencies between items such as definitions, modules and files, and rechecks every item that depends on a changed one. That is coarse. An item is rechecked whole even when the edit touched one judgement inside it.

gandr tracks dependencies between judgements. Each judgement records what it read, down to the term. An edit invalidates exactly the judgements that read what changed and nothing else. Checking a project from scratch is the same algorithm with nothing to reuse. A judgement's record names what the judgement needs, not where it was computed. The same records therefore let work be shared between processes and between machines. Incremental checking in one editor and replay across a cluster are one mechanism at two scales.

The records answer a deeper question too. Which part of a judgement was computed, and which part was decided by a certificate someone else produced? gandr treats this as a modality over one substrate. The elaborator is an oracle that happens to be implemented in the tree. A certificate is an oracle that is not. An external prover, a solver or a remote checker is admitted the same way: its answer enters as a certificate the kernel replays, under the same key discipline as everything else. Trusting an outside tool is a modality to be discharged, never a hole the checker is told to ignore.

- `crates/core-incremental` — the item seam, footprints, validated resume, checkpoints
- `crates/surface-session` — an editing session resumed through the incremental checker
- `crates/kernel-check-memo` — the check memo a kernel consults

### Tools and the corpus

The grammar is checked data with precedence bounds. The parser resumes after an error and reports what would complete the input. The formatter preserves meaning. The layout engine resolves line breaks by Pareto choice. A language server, a Model Context Protocol server, a terminal view, a REPL and a full-screen TUI share one engine per workspace, so every editor and every agent sees the same state. Diagnostics are one model with a terminal face and a remote face.

The corpus is the language's record. Each directory under `corpus/model` is one subject. Each source states what it expects. Each refused program sits beside the accepted one. Every feature in the ledger is witnessed there.

- `crates/surface-grammar`, `crates/surface-parser`, `crates/surface-format`
- `crates/surface-lsp`, `crates/surface-mcp`, `crates/surface-tui`
- `crates/surface-corpus` — the expectation schemas and the runner
- `ledger/features.sql`

### A small checker you can trust

A compiler or a proof assistant asks you to trust all of it. gandr asks you to trust one small part, the kernel. Everything else is untrusted and must show its work: the elaborator, the normaliser, the unifier and the rewriting engine.

Every declaration that reaches the kernel is checked again before it is admitted. When an untrusted engine decides that two terms are equal, it records the decisions it made, and the kernel replays them one by one. A result that was checked before can be reused, but only under a key the kernel itself attested. A matching hash is never enough on its own.

Two questions are kept apart on purpose. Did these bytes arrive intact? Does this term check? The first is integrity and the second is validity. gandr never lets one answer stand in for the other.

- `crates/kernel-core` — the checking machine, conversion and admission
- `crates/kernel-term` — the content-addressed term arena and its sharing format
- `crates/core-checker`, `crates/core-nbe`, `crates/core-unify` — the untrusted elaborator above it
- `corpus/model/identity/certificate-transport.gandr`

### Modular programming with models of higher-dimensional theories

A module system is usually a second language bolted onto the first, with its own rules for what matches what. Type classes and traits add a further rule: one instance per type for the whole program, and an instance may be written only in the module that owns the type or the class. These rules are not local. They are checked over the whole program, they fail when two libraries disagree, and they have no meaning across a distributed system where no single program owns every type.

gandr has one rule. A module is a model of a theory. A theory is a signature with its cells and laws, together with the completion those laws induce. A model gives the theory's sorts and operations and proves its laws. A functor is a model built over another model. A coercion from one model to another is a transport that univalence licenses, so two models of one theory with equivalent carriers are equal models.

Instances are modular implicits. A parameter names a theory, the candidates are the models of that theory in scope, and exactly one must remain. Resolution is static, order-free and local to the scope. Ambiguity is a type error at the use, not a global conflict, so no orphan rule and no global uniqueness are needed. Two worlds in one distributed program can hold different models of the same theory without contradiction, because a choice is made where it is used.

This makes gandr a language for lawful programming in the full sense. In most functional languages a law is a comment or a test property. In gandr a law is a cell of the theory, a model must prove it by conversion or by a certificate the kernel replays, and the engine then uses the law as a rewrite. The laws are part of a program's meaning and of its optimisation, not advice beside it. As far as the project knows, no other system holds its laws to this standard.

Terms in gandr are circuits, not trees. An operation can have many inputs and many outputs. A wire can split, join, or feed back into an earlier operation under a delay. A theory's signature is a circuit algebra, and a corolla is one operation with its ports, the smallest circuit. This is the shape of a string diagram, and it is what trees cannot express: sharing, dataflow with feedback, a protocol between several parties, a network. The site of shapes is the category of these circuits, and univalence is derived at its corollas.

- `corpus/model/modules/model-laws.gandr` — laws stated as equalities a model proves
- `corpus/model/modules/model-implicit.gandr` — a model resolved by its theory
- `corpus/model/modules/functor-pair.gandr`
- `corpus/model/circuit/circuit-feed-wheel.gandr` — a circuit with feedback under a delay
- `crates/theory-levitation`, `crates/theory-sites` — the universe of descriptions and the site of shapes

### Rewriting is computation

Most languages let you compute. Some proof assistants let you add equations as rewrite rules. Few let you do both in one system with the rules checked as carefully as the programs.

In gandr a block of rewrite rules is a set of cells over a signature. The engine completes the rules, finds their critical pairs, and settles the ways one rewrite can overlap another. The normal forms it produces are what the kernel uses to decide equality. This is higher-dimensional rewriting. There are rewrites between rewrites, and their coherence is certified and replayed like everything else.

A datatype's eliminator, a theory's law and a user's rewrite all run on this one machinery. The rewriting therefore sits beside ordinary computation instead of replacing it. Each step of a run carries its footprint, the set of what it read and wrote, so dependence and cost can be read off the derivation. Termination is shown by a path order that returns a derivation the checker replays.

Data takes the same form. A datatype in gandr is a computad: its constructors are cells, and an equation between constructors is a cell of the next dimension. Other systems add such equations as higher inductive types, which state the equation but do not compute with it. Here the equation is a rewrite, so it computes, its overlaps with other rules are completed, and its coherence is checked. One notion of data covers ordinary inductive types, quotients and higher structure, and it is the same notion the theories and the identity use.

Codata is the dual, and it keeps the rewriting well-behaved on infinite objects. A coinductive type is defined by the observations that can be made of it, and a corecursive definition is accepted only when every recursive call sits under an observation. A stream, a server loop and a session body are productive in this sense. The engine never unfolds an infinite object further than an observation asks, so normal forms stay finite and equality on codata is decided by the observations.

- `crates/theory-cell-complexes`, `crates/theory-coherent-resolutions` — cells, completion, critical pairs
- `crates/theory-computads` — descriptions elaborated into cells
- `crates/theory-deep-inference` — the causal web and the flow projection
- `crates/theory-path-orders` — termination with a replayable derivation
- `corpus/model/circuit/`

### Equality that behaves

Programmers expect that equal things are interchangeable. In most typed languages that promise breaks somewhere. Two functions that agree on every input are not equal, or two equivalent types are not equal, or an equality proof can be used but never computed with. Fixing one of these usually costs another.

gandr keeps all of them at once. Equality has a definitional eliminator, `J`. Functions that agree everywhere are equal, which is function extensionality. Equivalent types are equal, which is univalence, and here it is a theorem, not an axiom. An equality proof can be matched on as the reflexive case, `here`. As far as the project knows, no other system offers all four together.

Univalence is derived, not assumed. A signature's models are compared shape by shape, at the corollas of its site. The translation tables between two models build the path between the types. The construction follows the nerve-and-Reedy machinery and Shulman's argument for inverse diagrams. Function extensionality then follows from univalence in the usual way.

Equality here is directed first. The primitive is a flow from one type to another given by a translator. A symmetric path is the special case where the flow can be reversed. Virtual double categories, reflected over the universe of descriptions, justify the directed laws. Axiom K would collapse the higher equalities, and it is refused by name.

The same machinery gives quotients. A type can be taken up to the laws of a theory. Programs over a store that respect the put-put law are then folded by passing the state, and a model proves its laws as the equalities they are. The identity also decides questions that are ad hoc elsewhere. A session can migrate along a flow. Two memory layouts of one type are two models with a transport between them. An ornament between data descriptions is read the same way.

The identity is realised by the cells. A path between two terms is a cell of the next dimension, and a flow is a directed cell. The engine rewrites along them and the kernel replays them like any other step. Equality and computation are therefore one mechanism seen from two sides, which is why the identity computes and why its laws can be completed and checked for coherence like any rewrite block.

- `corpus/model/higher-cells/ua-corolla.gandr` — univalence built at the corollas
- `corpus/model/identity/funext-from-ua.gandr` — function extensionality derived
- `corpus/model/identity/flow-migration.gandr` — migration along a directed flow
- `corpus/model/layouts/ribbit-list.gandr` — one list, two layouts
- `crates/theory-sites`, `crates/theory-virtual-doctrines` — the site of shapes and the directed laws

### Types that measure

A compiler has to answer questions of degree. How many times is this value used? How much does this computation cost? How far apart are these two programs? What did this run touch? Most type systems answer none of them, so the compiler guesses and the runtime pays. Quantitative type systems answer the first by counting uses with a grade, and once the count reaches "many" the information is gone.

gandr's types keep the structure these questions need. A grade is a value in an algebra, not a fixed count. The algebra is a parameter of the type system, with a sum for alternatives and a product for composition, and the same typing rules hold for every choice. One choice counts uses exactly. Another measures cost. An ordered one, a quantale, measures the distance between two programs. The tropical one takes minimum as its sum and addition as its product, and it ranks the likely runs of a program that makes choices. A grade can also be a trace of what a computation touched.

The payoff is analysis that stays precise through abstraction. A fusion step can state the cost it saves in every context, with the context's grade as the factor, instead of estimating it. A rewrite can carry the distance between its two sides, so the engine knows how far a transformation moves a program. A step's footprint is the same kind of quantity. It is what the causal web and the concurrency analysis read.

Grades and effects are two halves of one design. A value's grade sits on the thunk that delays it. A computation's effects sit on the type that returns it. The two are the comonad and the monad of one polarised syntax. A graded presentation of an effect lets its operations carry grades, so one type says which effects a computation performs and how much of each.

Modes say how a value may be used: its multiplicity, its extent and its locus. A located type says at which world a value is meaningful. Whether a value may leave its world is authority. Whether it can be serialised is representation. The two are separate judgements, and the checker decides both.

- `corpus/model/effects/`
- `corpus/model/regions/`
- `corpus/model/worlds/seat-and-operator.gandr`
- `crates/core-checker` — grades, modes and located types
- `crates/theory-deep-inference` — footprints and the causal web

### Effects as relative monads

Effect systems come in two kinds. Monads are precise, but they combine awkwardly and cost at run time. Effect handlers compose well, but they hide what a program does from the type that describes it. gandr uses one structure that gives both.

In gandr a program is either a value or a computation. A thunk turns a computation back into a value. An effect is a monad relative to that shift. It is declared as a theory with a return and a bind, and its laws are rewrite rules. A model of the theory is an implementation that proves the laws. A monadic block is written once and translated away at checking time. When the model is known, nothing is dispatched at run time. The block becomes ordinary calls, and they normalise like any other.

The same shift carries the other direction. First-class stacks and thunks are the two halves of a focused, polarised adjunction. The relative monads and comonads over that adjunction are its syntax and its semantics. This is what lets gandr check that its control model is sound instead of assuming it, and it is the side the grades ride on. A handler is an algebra of the free relative monad on its effect's signature. A capability is permission to perform an effect, supplied by a handler as a hypothesis in the typing context. Nothing has ambient authority, so sandboxing a program is a matter of which capabilities it is given.

Which effects commute is a fact of the theory, not of the compiler. A commutative relative monad is one whose operations can be performed in either order with the same meaning. Where a pair of effects commutes, the engine records that no order was chosen, and the fusion pass may move code across the pair. Where they do not commute, the order is a dependence the footprints keep.

- `corpus/model/effects/`
- `corpus/model/desc/sealed-lawful-model.gandr` — a model proving a theory's laws
- `corpus/model/desc/second-order-rules.gandr` — laws with binding operations
- `corpus/model/codata/streams.gandr`
- `corpus/classifier/relative-monad-sort-errors.gandr` — what the checker refuses

### References dissolve, lifetimes remain

A language that lets you take a reference to a value lets two parts of a program see the same memory. From then on a change in one place is a surprise in another, and the type system spends its effort tracking who may see what. Rust tracks it well, and the cost is visible. A reference is at once a value, a place and a lifetime, and the programmer manages all three.

gandr separates the three and keeps two. Values are values. A program never observes sharing, so a mutation is local by construction. A place is something a program can project into and update through. An access to a place is shared beside shared, or exclusive beside nothing. A lifetime is a static extent, an ordered index on a type that the checker verifies and erases before anything runs. What is refused is the reference as a value, the part that makes sharing observable. Nothing that part did is lost.

Temporary access is control, not data. A function can pause, let its caller read or update a value, and resume when the caller is done. The access lives exactly as long as the suspension, and it needs no annotation. Some protocols need more. A buffer must stay valid until the kernel completes an I/O operation, and the completion must be accounted for. The extent and the obligation are then two typed parts of one value. This is the design the essay "References are like jumps" asks for, carried through to a type system.

- `corpus/model/regions/` — extents held, lent and passed
- `corpus/model/moves/`
- `crates/core-checker` — regions, access modes and deduced receivers
- [boats, "References are like jumps"](https://without.boats/blog/references-are-like-jumps/)

### The hard cases of resources and concurrency

Some problems stay hard in every mainstream language. Dropping a resource that must finish asynchronous work first. Cancelling a task safely. Keeping concurrent tasks inside the scope that started them. Values that refer to themselves. Moving a value without copying it. They share a shape. In each case something is suspended and owes something, such as a cleanup, a completion, a join or a return. The language has no place to hold that debt, so the debt becomes a convention, and a value can escape a convention by being forgotten.

gandr gives the debt a place. The typing context has a linear zone. Whatever lives there must be consumed exactly once and cannot be dropped silently. A suspended computation that owes something is a first-class, one-shot stack in that zone. Its protocol, what it still has to do before it is done, is a session type. Four carriers share the work, one job each. The linear zone says what must be accounted for. The grade says how many copies exist. The region index says how long a value lives. The world says where it lives. Unwinding is typed, so leaving a scope early is itself a program the checker sees.

Each hard case is then a question the types answer. An asynchronous drop is a session the unwind runs, and the unwind may await it. A cancelled task that holds a pending operation has exactly two sound exits. It awaits the completion, or it hands the operation to the reactor that owns the buffer. The buffer's region decides which, because a frame-local buffer forces the await. A scoped task's guard cannot be forgotten, so the scope's end is reached. A self-referential value is an extent, and a moved value is a non-duplication. Neither is an address. Iterators, generators, asynchronous functions and streams are one construction with different session types, and each session type is a small automaton. Every case has an accepting program in the corpus, and the programs that must be refused sit beside it.

- `corpus/model/cancellation/`, `corpus/model/drop/`
- `corpus/model/tasks/`, `corpus/model/self-reference/`, `corpus/model/moves/`
- `crates/core-session` — session types, endpoint replay, dialogues admitted by logical time
- `crates/core-term` — the two-zone context

### Memory by location, by content, and by provenance

Programs store values in two ways. Inside one process a value is found by its address. Between processes, or on disk, a value must be named by what it is. Most systems treat the second way as a serialisation library, and they lose sharing, deduplication and history along the way.

gandr has two memories with one key space. The storage tier is a content-addressable memory. Values are chunked by content, committed under the digest of their canonical bytes, and kept as records in an authenticated search tree. Each world runs its own location-addressable heaps, with regions that are never recycled. Inside a world a value crosses by location. Across worlds it crosses by content, and there is a bound on how much of an edited value must be re-sent.

A stored fact also says where it came from. A record is a receipt. It names its author by key, its inputs by content, and the step that produced it, and it is signed. A verdict that a declaration checks is recorded with the key of the kernel that attested it, and it is reused only under that key. When a value arrives from another machine, it arrives with its history, and a reader can refuse an author the record does not authorise. A distributed program needs this and almost no language gives it. The record says not only what a value is, but who said so and on what grounds.

- `crates/storage-values` — the content-addressed value plane
- `crates/storage-records`, `crates/storage-schema` — records as C-sets with checked equations
- `crates/storage-store` — one store over both planes
- `crates/kernel-check-memo` — verdicts under the attesting key
- `crates/README.md` § Storage and distribution — the topology

### Native code, at no hidden cost

A language with this much structure should not pay for it at run time. gandr compiles to native code through one abstract machine, the L machine. A program is focused into the machine's command language. The machine's transitions are written once as stencils. The emitter copies and patches the stencils into machine code under a content cache. The same stencils run under a portable executor on a host without a native backend. A call into the host is an effect performed at the boundary, and values cross the boundary by layout.

The rule for cost is simple to state and is checked on every change. A runtime component is either demanded by a type or it is a policy of the build recipe that is off by default. A grade above zero, a crossing between worlds and a branch of a session are demands, and the component they demand is part of the program. Run-time admission, session monitors, failure detection, dynamic linking and tracing are policies. Nothing else runs. When gandr generates code from a higher-level form, the generated code is measured against what a programmer would write by hand.

- `crates/core-sequent` — the command language a program is focused into
- `crates/runtime-stencils`, `crates/runtime-emitter` — the L machine and the native emitter
- `corpus/model/ffi/`, `corpus/model/interop/` — the host boundary
- `corpus/model/effects/domhringr.gandr` — the host interfaces

### Programs that span machines

A distributed program is usually several programs, a protocol written down somewhere else, and a deployment script. gandr makes these one thing.

A world is a place a program can run, reachable by its key. Coordination between worlds is a session. Failure is a branch of the session's type, not an exception. A closed computation can migrate to another world, shipped by content. The network is a host interface over an authenticated QUIC endpoint.

Sessions written by hand are the foundation. A choreography is one program that describes every party. It is compiled by projecting it into a session program for each role. The build layer provisions each role's program into a process, a container, a unikernel or a library. Deploying a choreography binds roles to worlds and never changes what the programs are. A program with one role, deployed to one machine, is the ordinary case of the same picture.

- `corpus/model/worlds/`, `corpus/model/sessions/`
- `corpus/model/distribution/ping.gandr` — two processes exchange bytes by key
- `crates/runtime-net` — the network a host holds
- `crates/core-session`

## Contents

```text
corpus/      the language's record: model/ one subject per directory, each source stating its expectation; pathological/ the refused twins; strict/ under crates/surface-corpus checks owing nothing
crates/      the workspace, named and layered by crates/README.md: theory, kernel, core, storage, runtime, surface, workflow
library/     std, a package like any other, written in gandr: layouts, the package and boundary vocabulary (library/std/README.md)
ledger/      what is built, as data: features, concerns, syntax, references, purposes; the crate map and the census
contrib/     the Visual Studio Code extension
```

## Build

```sh
mise install && cargo build --release -p gandr-lang
target/release/gandr run corpus/model/effects/hello.gandr
target/release/gandr test corpus
```

## License

Apache-2.0 WITH LLVM-exception. See `LICENSE.Apache-2.0.txt` and `LICENSE.LLVM-exception.txt`.
