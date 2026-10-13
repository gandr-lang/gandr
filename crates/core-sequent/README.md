# gandr-core-sequent

The sequent tier of the core: the command IL a call-by-push-value program is focused into, and the two-region store its abstract machine works over.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `CommandArena` holds the three node families of a polarized sequent calculus — producers, consumers and commands — over the core language's vocabulary: a command `⟨p |ε c⟩` cuts a producer against a consumer at a polarity, constructor and destructor heads (`ConstructorTag`, `DestructorTag`) declare their own arities, and variables and covariables are de Bruijn indices. `focus_computation` and `focus_value` translate a core term into that IL and `unfocus_command` and `unfocus_value` read it back; `check_command` holds a command to the IL's typing discipline. `Store` is the two-region store an environment machine over that IL runs in: an append-only heap of values, memo cells and environment chains, and a walkable region of continuation frames addressed by marks. `Machine` is that environment machine for the pure fragment: it runs a command to a value under a step budget, unfolding constants from `Definitions`, and reads the value back as a core term.

**Why.** A call-by-push-value term has its evaluation order implicit in its syntax; a command makes it explicit as a cut whose two sides say what is sent where. The abstract machine steps that structure directly, cell rules reify into it, and effect handlers walk its frames without inspecting opaque host closures.

**How.** Every node is minted only over children the arena already holds, so the arena is acyclic by construction, and a `SequentWatermark` with `CommandArena::truncate_to` drops exactly what a refused build minted. Binders count outward, producers and covariables in separate index spaces, so equal inputs build identical nodes and no translation keeps a name supply. The store's heap values are immutable and shared by address; a thunk's memo cell is the only mutable state, and the store itself enforces its three-state protocol. Frames carry fresh serials, so a continuation mark over a frame that has since been popped is refused as stale rather than resumed into another continuation.

## Provided features

- `CommandArena`, `ProducerNode`, `ConsumerNode`, `CommandNode`, `PatternArm`, `CopatternArm`: the IL's three families, minted only over resolving children, refusing with `MintRefusal`.
- `SequentWatermark` with `CommandArena::watermark` and `CommandArena::truncate_to`: the rollback a refused build takes.
- `ConstructorTag` and `DestructorTag` with their declared `ProducerArity`, `ConsumerArity` and, for a destructor, the polarity it observes.
- `CovariableIndex`: a covariable is a de Bruijn index, in a space of its own.
- `Store` with `HeapValue`, `HeapValueId` and `CellId`: the heap region of immutable values and nominal memo cells, with `ForceEntry` and `MemoState` the cell protocol, `StoreFault` its refusals.
- `Environment`, `ValueScope`, `CovalueScope`: persistent environment chains in the heap region, read innermost first.
- `Frame`, `ContinuationMark` and `Store::shrink_to`: the walkable frame region, marks refused once stale, and the decline of every forcing a shrink abandons.
- `Store::peak_height`: the highest the frame region has stood since the store was made, the observation that a tail call holds no continuation of its own.
- `focus_computation`, `focus_value` and `focus_top_value`, recording each created command's `FocusOrigin` in a `Provenance` table: total on closed well-typed core terms that hold no code, every image well formed and closed, every covariable the innermost one, a code refused by name, a record focused as the head of its labels and a tuple or record projection as a selection of its field, a split focused as a case on its one tuple pattern, and a refused translation leaving the arena and the table at their marks. A datatype's constructors, its nominal match and the fixpoint focus.
- `unfocus_command` and `unfocus_value`: the left inverse of focusing, refusing IL outside its image by name with `UnfocusRefusal` and leaving the core arena at its mark.
- Native `ListNil` and `ListCons` constructors and a `ListFold` consumer. Folding preserves cell order and outer scope; each branch has its own return covariable, and the cell branch binds head then folded result. The command arena owns imported type annotations, includes them in rollback, and unfocusing closes their ambient variables rather than copying foreign ids.
- `check_command` with `CheckRefusal`, `ArityHead` and `FreeSet`: reference integrity, arity from the head, focus, polarity, and the free variables and covariables of a command.
- `render_command`, `render_producer` and `render_consumer`: the IL's notation, binders shown with their indices.
- `Machine::run` with `Definitions`, `Definition`, `StepCount`, `Outcome`, `Stuck` and `MachineFault`: the L machine over the store, halting with a value, stopping stuck by name, or faulting out of steps; transparent constants unfold once per machine, opaque ones are carried as themselves; a nominal match runs the branch of its value's ordinal over the fields, a selection delivers the field of the tuple or record it meets, and a recursive thunk runs with itself bound.
- `Machine::read_back` and `Machine::read_back_value` with `ReadbackRefusal`: a terminal as `return v` or the function it is, thunks, recursive thunks and functions closed over their captured environments, a record with its labels, a datatype's constructor at the unknown value type, a suspended capture refused with the core arena at its mark.
- `stats`, `Stats`, `origin_histogram` and `dump`: an arena's population, its commands counted by the core former each came from, and a root's rendering with both.
- `reify_command` with `ConstructorResolver` and `ReifyRefusal`: a ground cell pattern reified node for node, a return-side frame as its `μ̃` definiens, a metavariable, an unresolved symbol, an arity mismatch and an operation frame refused with the arena at its mark.

## Expected features

- **Addresses from the same arena or store.** An address is a position in one arena or store; one from another resolves to an unrelated node or to nothing. Lookups fail closed on a dangling address, and nothing checks provenance beyond that.
- **Truncation by the minting party.** `CommandArena::truncate_to` drops nodes, not references to them; the caller that takes a mark is the one that may truncate to it, after dropping every address minted since.
- **Well-typed input to focusing.** Focusing translates the formers it is given and refuses only a dangling id, a code or a full arena; it does not type-check. Totality and closedness of the image are stated for closed terms the core's checker accepts that hold no code, and an ill-typed term focuses to whatever its formers say.
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
    tag: ConstructorTag::Tuple(ProducerArity::ZERO),
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

Set `RUSTFLAGS="--cfg anodized_panic"` on that command to exercise the predicates throughout the dependency graph. Const arity and rendering contracts retain their compile-time calling context.

Checked address allocation and lookup live in a crate-private trait rather than identifier macro templates. The default methods keep each executable contract visible as an ordinary Rust item and specialize for each transparent identifier without allocation. The ceiling and truncation witnesses exercise those methods through the identifiers.

The opaque binding iterator keeps its public signature; the [`Store::bound_values` contract](src/store.rs) records the postcondition-instrumentation limit and the independent sequence witnesses.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Covariables as indices, children before parents | [`il`](src/il.rs) |
| Focusing, records, codes and native universe paths | [`focus`](src/focus.rs) |
| Unfocusing | [`unfocus`](src/unfocus.rs) |
| The typed-IL check | [`check`](src/check.rs) |
| Marks, fixpoints, effects and delimited control | [`machine`](src/machine.rs) |
| Readback | [`readback`](src/readback.rs) |
| The two-region store and the cell protocol | [`store`](src/store.rs) |
| The bridge from cells and its polarity | [`bridge`](src/bridge.rs) |
| The differential against normalisation by evaluation, references | [`src/lib.rs`](src/lib.rs) |

The deferred behavioural floor of the L machine is tracked in [#200](https://github.com/gandr-lang/gandr/issues/200).

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
