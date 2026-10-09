# gandr-core-sequent

The sequent tier of the core: the command IL a call-by-push-value program is focused into, and the two-region store its abstract machine works over.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Covariables are indices](#covariables-are-indices)
- [Children before parents](#children-before-parents)
- [Focusing names only what is not a tail](#focusing-names-only-what-is-not-a-tail)
- [Unfocusing is the left inverse](#unfocusing-is-the-left-inverse)
- [The typed-IL check](#the-typed-il-check)
- [The machine runs over marks, not copies](#the-machine-runs-over-marks-not-copies)
- [Readback refuses rather than approximates](#readback-refuses-rather-than-approximates)
- [The polarity is the cell substrate's](#the-polarity-is-the-cell-substrates)
- [Two regions](#two-regions)
- [The store owns the cell protocol](#the-store-owns-the-cell-protocol)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `CommandArena` holds the three node families of a polarized sequent calculus — producers, consumers and commands — over the core language's vocabulary: a command `⟨p |ε c⟩` cuts a producer against a consumer at a polarity, constructor and destructor heads (`ConstructorTag`, `DestructorTag`) declare their own arities, and variables and covariables are de Bruijn indices. `focus_computation` and `focus_value` translate a core term into that IL and `unfocus_command` and `unfocus_value` read it back; `check_command` holds a command to the IL's typing discipline. `Store` is the two-region store an environment machine over that IL runs in: an append-only heap of values, memo cells and environment chains, and a walkable region of continuation frames addressed by marks. `Machine` is that environment machine for the pure fragment: it runs a command to a value under a step budget, unfolding constants from `Definitions`, and reads the value back as a core term.

**Why.** A call-by-push-value term has its evaluation order implicit in its syntax; a command makes it explicit, as a cut whose two sides say what is sent where. That is the form an abstract machine steps without a search for the next redex, the form a cell rule from the rewriting stack already speaks, and the form whose frames an effect handler will later need to walk. Fixing the IL and the store first fixes the contract every later piece — focusing, the machine, the bridge from cells — is written against.

**How.** Every node is minted only over children the arena already holds, so the arena is acyclic by construction, and a `SequentWatermark` with `CommandArena::truncate_to` drops exactly what a refused build minted. Binders count outward, producers and covariables in separate index spaces, so equal inputs build identical nodes and no translation keeps a name supply. The store's heap values are immutable and shared by address; a thunk's memo cell is the only mutable state, and the store itself enforces its three-state protocol. Frames carry fresh serials, so a continuation mark over a frame that has since been popped is refused as stale rather than resumed into another continuation.

## References

- Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In _Proceedings of the Fifth ACM SIGPLAN International Conference on Functional Programming (ICFP '00)_, pages 233–243, September 2000. `doi:10.1145/351240.351262` — the command `⟨p | c⟩`, the binders `μα` and `μ̃x`, and the critical pair a cut's polarity resolves.
- Paul Downen and Zena M. Ariola. "A Tutorial on Computational Classical Logic and the Sequent Calculus." _Journal of Functional Programming_ 28 (2018), e3. `doi:10.1017/S0956796818000023` — data and codata as constructor applications and copattern objects, pattern matches and destructor frames, and the polarized cut.
- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." In _Typed Lambda Calculi and Applications (TLCA '99)_, Lecture Notes in Computer Science 1581, pages 228–243, 1999. `doi:10.1007/3-540-48959-2_17` — the value/computation split the IL's two polarities carry, and the thunk as the positive suspension of a computation.
- John Launchbury. "A Natural Semantics for Lazy Evaluation." In _Proceedings of the 20th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '93)_, pages 144–154, 1993. `doi:10.1145/158511.158618` — call-by-need as a heap of updatable suspensions, and the black hole a re-entered suspension shows.
- Peter O'Hearn, John Reynolds and Hongseok Yang. "Local Reasoning about Programs that Alter Data Structures." In _Computer Science Logic (CSL 2001)_, Lecture Notes in Computer Science 2142, pages 1–19, 2001. `doi:10.1007/3-540-44802-0_1` — the heap as a partial commutative monoid under disjoint union, and the frame rule the memo-cell suite states its four conditions in.

## Provided features

- `CommandArena`, `ProducerNode`, `ConsumerNode`, `CommandNode`, `PatternArm`, `CopatternArm`: the IL's three families, minted only over resolving children, refusing with `MintRefusal`. Witnesses: `il::tests::arena_allocates_and_reads_back`, `il::tests::minting_refuses_a_dangling_child`.
- `SequentWatermark` with `CommandArena::watermark` and `CommandArena::truncate_to`: the rollback a refused build takes. Witness: `il::tests::truncation_drops_exactly_the_later_nodes`.
- `ConstructorTag` and `DestructorTag` with their declared `ProducerArity`, `ConsumerArity` and, for a destructor, the polarity it observes. Witnesses: `il::tests::tag_arities_are_stable`, `il::tests::tag_consumer_arities_are_declared`.
- `CovariableIndex`: a covariable is a de Bruijn index, in a space of its own.
- `Store` with `HeapValue`, `HeapValueId` and `CellId`: the heap region of immutable values and nominal memo cells, with `ForceEntry` and `MemoState` the cell protocol, `StoreFault` its refusals. Witnesses: `store::tests::cell_write_back_is_shared_and_nominal`, `tests::csl_fibration::frame_preservation_under_forcing`, `tests::csl_fibration::nominal_identity_freshness_and_alias_coherence`, `tests::csl_fibration::black_hole_discipline_under_reentry`, `tests::csl_fibration::write_back_purity_caches_the_exact_probe_allocation`.
- `Environment`, `ValueScope`, `CovalueScope`: persistent environment chains in the heap region, read innermost first. Witness: `store::tests::environments_bind_innermost_first`.
- `Frame`, `ContinuationMark` and `Store::shrink_to`: the walkable frame region, marks refused once stale, and the decline of every forcing a shrink abandons. Witness: `store::tests::frames_shrink_to_a_mark`.
- `focus_computation`, `focus_value` and `focus_top_value`, recording each created command's `FocusOrigin` in a `Provenance` table: total on closed well-typed core terms, every image well formed and closed, every covariable the innermost one, and a refused translation leaving the arena and the table at their marks. Witnesses: `tests::focus_properties::focusing_is_total_on_generated_computations`, `tests::focus_properties::hand_built_cases_cover_every_former`, `tests::focus_properties::top_level_value_focuses_against_top`, `focus::tests::focusing_mints_no_name`, `focus::tests::a_refused_focusing_leaves_the_arena_at_its_mark`.
- `unfocus_command` and `unfocus_value`: the left inverse of focusing, refusing IL outside its image by name with `UnfocusRefusal` and leaving the core arena at its mark. Witnesses: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`, `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`, `unfocus::tests::an_escaping_covariable_is_refused_and_rolled_back`, `unfocus::tests::a_capture_standing_as_a_value_is_outside_the_image`.
- `check_command` with `CheckRefusal`, `ArityHead` and `FreeSet`: reference integrity, arity from the head, focus, polarity, and the free variables and covariables of a command. Witnesses: `check::tests::terminal_cut_is_wellformed`, `check::tests::scope_tracks_binders`, `check::tests::dangling_reference_is_rejected`, `check::tests::non_value_argument_is_rejected`, `check::tests::polarity_mismatch_is_rejected`, `check::tests::constructor_arity_is_checked`, `check::tests::constructor_consumer_arity_is_checked`, `check::tests::destructor_consumer_arity_is_checked`, `check::tests::consumer_arity_follows_the_head_not_a_constant`, `check::tests::a_head_answered_twice_is_rejected`.
- `render_command`, `render_producer` and `render_consumer`: the IL's notation, binders shown with their indices. Witnesses: `pretty::tests::renders_terminal_cut`, `pretty::tests::renders_lambda_cocase`, `pretty::tests::renders_structural_heads`.
- `Machine::run` with `Definitions`, `Definition`, `StepCount`, `Outcome`, `Stuck` and `MachineFault`: the L machine over the store, halting with a value, stopping stuck by name, or faulting out of steps; transparent constants unfold once per machine, opaque ones are carried as themselves. Witnesses: `machine::tests::ret_is_a_terminal_value`, `machine::tests::bind_threads_a_value`, `machine::tests::force_runs_a_thunk_body`, `machine::tests::case_selects_the_matching_arm`, `machine::tests::application_binds_the_argument`, `machine::tests::a_shared_thunk_is_forced_once`, `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`, `machine::tests::the_step_budget_bounds_a_run`.
- `Machine::read_back` and `Machine::read_back_value` with `ReadbackRefusal`: a terminal as `return v` or the function it is, thunks and functions closed over their captured environments, a suspended capture refused with the core arena at its mark. Witnesses: `machine::tests::a_function_terminal_reads_back_closed_over_its_environment`, `machine::tests::a_thunk_reads_back_closed_over_its_environment`, `machine::tests::a_suspended_capture_has_no_reading`.
- `stats`, `Stats`, `origin_histogram` and `dump`: an arena's population, its commands counted by the core former each came from, and a root's rendering with both. Witness: `inspect::tests::stats_and_dump_report_a_terminal_cut`.

## Expected features

- **Addresses from the same arena or store.** An address is a position in one arena or store; one from another resolves to an unrelated node or to nothing. Lookups fail closed on a dangling address, and nothing checks provenance beyond that.
- **Truncation by the minting party.** `CommandArena::truncate_to` drops nodes, not references to them; the caller that takes a mark is the one that may truncate to it, after dropping every address minted since.
- **Well-typed input to focusing.** Focusing translates the formers it is given and refuses only a dangling id or a full arena; it does not type-check. Totality and closedness of the image are stated for closed terms the core's checker accepts, and an ill-typed term focuses to whatever its formers say.
- **Checked input to the machine.** `Machine::run` expects a command `check_command` accepts closed. On anything else it stops `Stuck` at the first node it cannot step, which is a diagnosis, not a verdict on the program. A machine's store grows across its runs; a caller that needs a bounded heap runs a fresh machine.

## Examples

Mint the command `⟨() |+ ★⟩` and read it back.

```rust
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::ProducerNode;
use gandr_theory_cell_complexes::Polarity;

let mut arena = CommandArena::new();
let unit = arena.mint_producer(ProducerNode::Constructor {
    tag: ConstructorTag::Unit,
    producers: Box::from([]),
    consumers: Box::from([]),
})?;
let top = arena.mint_consumer(ConsumerNode::Top)?;
let cut = arena.mint_cut(Polarity::Positive, unit, top)?;
assert!(matches!(arena.command(cut), Some(CommandNode::Cut { .. })));
# Ok::<(), gandr_core_sequent::MintRefusal>(())
```

Focus `return ()`, render the command, and read it back.

```rust
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::render_command;
use gandr_core_sequent::unfocus_command;
use gandr_core_term::CoreArena;

let mut core = CoreArena::new();
let unit = core.value_unit();
let returned = core.computation_return(unit);

let mut arena = CommandArena::new();
let mut provenance = Provenance::new();
let command = focus_computation(&core, returned, &mut arena, &mut provenance).expect("a closed term focuses");
assert_eq!("⟨() |+ ★⟩", render_command(&arena, command));
assert_eq!(Ok(FreeSet::default()), check_command(&arena, command));

let mut decoded = CoreArena::new();
assert!(unfocus_command(&arena, command, &mut decoded).is_ok());
```

Run the tests:

```sh
cargo nextest run -p gandr-core-sequent
```

## Covariables are indices

A covariable is a `CovariableIndex` counting covariable binders outward, in an index space separate from the producer variables' `(zone, DeBruijnIndex)`. A `μα`, a thunk's body and a copattern arm's consumer arguments bind covariables; a `μ̃x`, a pattern arm's fields and a copattern arm's producer arguments bind producer variables. Nothing mints a name: α-equivalent IL is identical IL, a translation needs no counter threaded through it, and two runs over equal input build identical arenas. The producer index space is the core's own, so a core variable crosses into the IL unchanged.

The alternatives were named covariables drawn from a fresh-name supply, which is what the earlier implementation of this design had — every translation threading a counter and every comparison working modulo renaming — and a counter newtype standing in for a name, which keeps the supply and only types it. The choice reverses if a consumer of the IL needs to address a covariable by identity across terms, which no reader of a command does today.

## Children before parents

Every `mint_*` call checks that each child it is given resolves in the arena before appending, so each node's children were minted strictly before it, across all three families, and the arena is acyclic by construction. A `SequentWatermark` records the three family lengths; truncating to it keeps exactly the nodes minted before it, and since those name only earlier nodes, truncation never leaves a dangling child inside the arena. A build that mints several nodes and then refuses truncates to the mark it took on entry, so a refusal leaves the arena as it found it. The earlier implementation of this design returned an error from a half-built translation with its partial nodes still in the arena.

The alternatives were unchecked minting, which admits a forward reference and with it a cycle every walk would then need a depth limit against, and a staging buffer committed at the end of a build, which copies every node twice. The choice reverses if a measured build shows the per-child check dominating minting.

## Focusing names only what is not a tail

Focusing translates a computation `M` under a continuation `c` into a command, `𝓕⟦M⟧c`, and a value `v` into a producer, `𝓥⟦v⟧`:

```text
𝓥⟦x⟧ = x        𝓥⟦thunk M⟧ = {force(α) ⇒ 𝓕⟦M⟧α}        𝓥⟦()⟧, 𝓥⟦(v, w)⟧, 𝓥⟦inj v⟧, 𝓥⟦lift v⟧ = the constructor

𝓕⟦return v⟧c        = ⟨𝓥⟦v⟧ |+ c⟩
𝓕⟦force v⟧c         = ⟨𝓥⟦v⟧ |+ force(c)⟩
𝓕⟦M v⟧c             = 𝓕⟦M⟧(apply(𝓥⟦v⟧; c))
𝓕⟦λ. M⟧c            = ⟨cocase {apply(x; α) ⇒ 𝓕⟦M⟧α} |− c⟩
𝓕⟦x ← M; N⟧c        = 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧c)                         c a tail
                    = ⟨μα. 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧α) |ε c⟩                otherwise
𝓕⟦case v {l, r}⟧c   = ⟨𝓥⟦v⟧ |+ case {inl(x) ⇒ 𝓕⟦l⟧c | inr(x) ⇒ 𝓕⟦r⟧c}⟩   c a tail
                    = ⟨μα. ⟨𝓥⟦v⟧ |+ case {… 𝓕⟦·⟧α …}⟩ |ε c⟩        otherwise
```

A tail is a covariable or `★`. A bind and a case open a producer binder, and a continuation that is not a tail — a frame, a `μ̃` — carries producers whose indices would have to shift under it; so such a continuation is named once with a `μ`, at the polarity of what it observes, and the binder sees only the tail `α0`. Every continuation that crosses a binder is then a tail, nothing is shifted or copied, every focused covariable is index `0`, and two focusings of one term build identical arenas. A core value is never a `μ`, so every frame argument and constructor field of an image is a value. `Provenance` records, for each command focusing creates, the core former it was created for. A refused translation truncates the arena and the provenance table to the marks it took on entry.

The earlier implementation of this design passed the continuation under the binder unchanged, `𝓕⟦x ← M; N⟧α = 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧α)` for any `α`, which named covariables make sound and indices do not. The alternatives were that rule with a shift of the continuation's producers under every binder, which copies a frame subtree per binder it crosses, and named covariables, which the section above rejects. The cost of the choice is one extra cut and one bound mark for a bind or case that is not in tail position. It reverses if a measured run shows that cut to matter, at which point a shift memoised per frame becomes the cheaper rule.

## Unfocusing is the left inverse

`unfocus_command` and `unfocus_value` read the image of focusing back into a core arena, rule by rule in reverse: a cut against the return point is a `return`, a force frame a `force`, an application frame an application, a copattern object of one `apply` arm a `λ`, a `μ̃` a bind, a match on the two injections a `case`, and a `μ` cut the bind or case it names, under the frame it was named for. The return point is `★` at the root and `α0` under the nearest covariable binder; a covariable reaching past it is a jump the core cannot state and is refused as `UnfocusRefusal::EscapingContinuation`. A `μ` in value position, a match on anything but the two injections and every other node outside the image is refused by name, and a refused reading truncates the core arena to its mark. Over closed well-typed terms `unfocus ∘ focus` is the identity up to the core's structure, which the round-trip properties check node by node across the two arenas.

The walk is a loop over an explicit task stack, and its one implementation serves both the public inverse and the machine's readback, which closes a terminal's free variables by index from its environment. The earlier implementation of this design answered `None` for anything it could not read and recursed over owned terms, substituting a named environment value by value. The alternative was a readback of its own for the machine, which would be a second decoder for the same image to keep in step. The choice reverses if the machine's terminals grow a form focusing never produces.

## The typed-IL check

`check_command` walks a command and every node below it and refuses, by name, an address the arena does not hold; a constructor or destructor whose producer or consumer children contradict the counts its head declares; a match or copattern object answering one head twice; a `μ` standing where only a value may; and a cut whose producer or consumer observes the other polarity. Constructors, literals, thunks, matches and force frames are positive, copattern objects and application frames negative, and variables, constants, `μ`, covariables, `μ̃` and `★` take the cut's polarity. On success it answers the command's free variables and covariables, counted from the command, so a caller asks for a closed command by asking for an empty `FreeSet`.

The arena is acyclic by construction, so the walk is a loop with no depth limit. The earlier implementation of this design recursed with a depth guard against cyclic input, checked a cut's polarity on the producer side alone, and admitted a head answered twice. The alternative was a full two-sided type check, which needs the source types the IL does not carry; the check covers what is decidable from a command alone. The choice reverses if the IL comes to carry types.

## The machine runs over marks, not copies

`Machine::run` is a loop over one control state — run a cut, deliver a value to a consumer, return a value to a mark, pop the top frame — each iteration one transition against the caller's `StepCount`:

```text
run ⟨μα.s |ε c⟩ ρ      load c, bind α to its mark, run s      (not at ε = − against a μ̃)
run ⟨p |ε c⟩ ρ         evaluate p, deliver it to c
deliver v α            return v to α's mark       deliver v ★        return v to the base
deliver v μ̃x.s         run s with x bound to v    deliver v case     run v's arm, fields bound
deliver v D(ā; c)      load c, observe v by D     return v m         shrink to m, pop
```

Loading a consumer pushes the frames it denotes: a chain of destructor frames over a covariable or `★` first shrinks the region to that base, and one over a `μ̃` or a match pushes onto the current top. A covariable binds the mark of the continuation it names, so returning through it is a shrink to that mark, and a mark whose frame has since been popped and replaced is refused as stale by the store. Forcing a thunk follows its cell: a forced cell returns its cached value, an opened one pushes an update frame under the body's return point, a re-entrant one runs the body inline. A `μ` against a `μ̃` at a negative cut is suspended and bound, the call-by-name side of the critical pair; everywhere else the `μ` runs first. Producers evaluate within a transition — a constructor over its evaluated fields, a thunk with a fresh cell, a copattern object or a `μ` closed over the environment — and a constant unfolds its definition once per machine, a cycle among definitions stopping the run as `Stuck::CyclicConstant`.

The earlier implementation of this design kept the same walkable frame stack, but a covariable captured a copy of a slice of it, values were reference-counted trees, and the step budget was one shared constant. Here a covariable is a mark into the one region, values and environments are addresses into the append-only heap, and the budget is the caller's. The alternatives were the copied slices, which cost a copy per capture and give every captured continuation its own frames to keep consistent, and continuations as heap closures, which the section on the two regions rejects. The choice reverses when a multi-shot continuation, which a mark into one region cannot resume twice, enters the language with effects and control.

## Readback refuses rather than approximates

`Machine::read_back` reads a positive terminal as `return v` and a copattern object as the function it is; a literal reads as itself, a constructed value over its fields, an opaque constant as the constant, and a thunk or a function as its suspended command decoded by the unfocusing walk with its captured environment's readbacks substituted. Values are read in increasing address order, since every value the machine allocates names only earlier ones, so the readback is a loop. A value with no core reading — a suspended `μ`, a copattern object standing as a value — is refused by name with the core arena at its mark.

The earlier implementation of this design fell back to a placeholder of the right kind when its readback failed, so a differential could pass on a value it had not read. The alternative was that fallback, rejected because a readback that cannot fail makes a differential that cannot fail. The choice does not reverse.

## The polarity is the cell substrate's

A cut's `ε` is `gandr_theory_cell_complexes::Polarity`, the type a cell pattern's cut carries. A cell elaborated by the rewriting stack and a command focused from a core term then cut at one polarity vocabulary, and reading a cell into a command copies its polarity rather than translating it. The alternative was a polarity of this crate's own with a conversion at the bridge, which is two names for one distinction. The choice reverses only if the core tier is reordered below the theory tier.

## Two regions

The heap region holds what outlives the frame that created it: values, memo cells and environment bindings, all append-only and addressed, so sharing is address sharing and a closure captures its environment by one address. The frame region holds the continuation as frames, in pushing order, each under a fresh `FrameSerial`. A `ContinuationMark` is a height together with the serial of the frame directly below it: binding a covariable binds a mark, and returning through one shrinks the region to it. A mark whose height has since been popped and re-pushed names a different serial and is refused with `StoreFault::StaleMark`. An update frame dropped by a shrink is a forcing abandoned mid-way, and its cell is declined back to unforced, so no black hole outlives the forcing that opened it.

The alternatives were continuations as heap-allocated closures, which makes every frame an allocation and leaves nothing for an effect handler to walk, and a single stack holding values and frames together, which ties a value's lifetime to a frame's. The choice reverses if a measured run shows the serial check on every return to dominate, at which point marks of a well-bracketed fragment can skip it.

## The store owns the cell protocol

A memo cell's only transitions are `Unforced → InProgress` by `Store::begin_force`, `InProgress → Forced` by `Store::write_back` and `InProgress → Unforced` by `Store::decline`; the store refuses any other write with `StoreFault::CellNotInProgress` and leaves the cell as it was. The earlier implementation of this design left legality to the machine's force protocol over a permissive cell. Enforcing it here makes the four conditions of the memo-cell suite properties of the store under any trace rather than only under the traces one machine produces, and the suite generates arbitrary traces accordingly. The alternative was the permissive cell, which is one check cheaper per transition. The choice reverses if a measured run shows the check to matter, which a three-state comparison is unlikely to.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
