# gandr-core-nbe

Normalization by evaluation for the core language: the glued value domain, the per-run arena that owns it, its three policy parameters, the evaluation and readback machines, the search-free steps of conversion, the lazy concurrent conversion machine, and the sharing overlay with its erasure, its measure, its duplication walk under either stance and its evaluator.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The semantic half of the core language. `eval_value` and `eval_computation` evaluate a `gandr-core-term` term to weak head in a `DomainArena`; `readback_value` and `readback_computation` read a domain node back into the core arena; `convert_values` and `convert_computations` run the three conversion steps that need no search, and `decide` runs the search behind them, emitting its winning derivation as a conversion trace. A domain node is glued: it carries what it denotes together with the core term it came from, and a neutral carries its unfolded form beside its neutral form. `SchedulingPolicy`, `DuplicationPolicy` and `GranularityPolicy` are the three parameters the domain and its conversion machine are written against; an `Overlay` holds the sharing syntax a duplication stance is asked over, `erase_value` and its siblings erase it back to the unshared term, and `SharingMeasure::of` measures one root of it. `duplicate_value` and `duplicate_computation` rebuild a root under a `DuplicationPolicy`, `eval_overlay_value` and `eval_overlay_computation` evaluate one through erasure, and `TracedDuplication` runs the spinal stance's shared evaluation, bound to the trace sink its conversions record into. Types are not evaluated. The crate is `no_std` over `core` and `alloc`.

**Why.** A conversion checker compares neutral forms first and unfolds only when they disagree, and an elaborator wants a normal form that keeps the source term wherever nothing reduced. Both need a domain that holds both readings at once, and both run on terms whose depth is whatever an elaborator built, so neither machine may recurse on the host stack.

**How.** Evaluation and readback are machines over an explicit task stack and two result stacks split by polarity, so depth lives on the heap. Evaluation keeps a node's source term exactly when every child came back denoting the corresponding source child, and turns a manifest constant into a neutral carrying its body's content id unforced. Readback chooses a face by mode, goes under a binder by minting a fresh variable at a de Bruijn level and evaluating the closure's body against it, and converts each level back to an index. Both machines draw on one fuel budget, because β and `force` alone suffice to loop. Laziness is a scheduling restriction rather than a representation, so a definitional height is a share of attention, never a gate on which unfoldings are tried.

## Provided features

- **Evaluation.** `eval_value`, `eval_computation`, `eval_value_within` and `eval_comp_within`: weak-head evaluation over an explicit task stack, refusing with `EvalFault`.
- **Readback.** `readback_value` and `readback_computation` under a `ReadbackMode`, refusing with `ReadbackFault`.
- **The glued domain.** `DomainArena` with its id families and watermark; `DomainValue`, `DomainComp`, `Neutral` and the faces they carry; `ValueClosure`, `CompClosure` and the two-zone `Environment`.
- **Policies.** `SchedulingPolicy`, `DuplicationPolicy` and `GranularityPolicy`, with the stances each admits or gates.
- **Definitions.** `Definitions`, `LoweredChain` and `Fuel`: the lowered chain a run unfolds through and the run's budget; `Endpoints` and `Definitions::reading_endpoints`: whether a compound endpoint runs through its definitions or holds at them for the conversion to unfold by a recorded step; `Recursion` and `Definitions::reading_recursion`: whether a readback names a definition's own recursion as the definition.
- **Conversion.** `convert_values` and `convert_computations`, the three search-free steps; `decide`, the lazy concurrent conversion machine, with its trace, its `Guard` read and its process re-sharing through `GoalSupport` and `ResharingMemo`.
- **Sharing.** `Overlay` and `Overlay::validate`; the `erase_*` functions; `SharingMeasure`; `eval_overlay_value` and `eval_overlay_computation`; `duplicate_value` and `duplicate_computation`; `TracedDuplication`.
- **Native formers.** Native lists and their folds, nominal data, records, fixpoints and universe paths through evaluation, readback and conversion.
- **Live evaluation.** `fill_and_resume`, `match_pattern` and `select_arm`: holes as neutrals, resumption after a fill, and three-valued arm selection.
- **Staging.** `stage::normalize`, `stage::power` and `stage::double`: certificate-producing strict staging for the experimental stage universe.
- **Tracing.** The optional `tracing` feature: one span per entry point, owned by the caller's subscriber.

## Expected features

- **The core arena outlives the domain arena.** A domain node names core nodes it does not own, so the caller never truncates the core arena below one, as [`arena`](src/arena.rs) states.
- **Well-scoped input.** Readback splices a source id under open binders on the strength of its term face, which is sound only if that source term is closed. Evaluating a well-scoped term guarantees it.
- **Lowering one body.** The definition chain names a body by its canonical subterm-table entry index, which is arena-independent; `LoweredChain::lower` runs the one pass in admission order and asks the caller, once per distinct index, for that body as a closed core value in the arena the run evaluates against. Reading a table entry as a core term is the caller's, because the caller holds the table. A lowering that is not closed surfaces as `EvalFault::UnboundVariable`, inside `ReadbackFault::Eval`, when the body is forced.
- **A fuel budget.** The caller sizes `Fuel` for the run; exhaustion is `EvalFault::OutOfFuel` or `ReadbackFault::OutOfFuel`, a decline rather than a verdict.
- **A conversion problem's depth.** `Problem::under` names the first intuitionistic binder level neither side mentions, so the machine's fresh variables start past the binders the caller already opened; a side that mentions a level at or past it compares a caller's variable with the machine's. `Problem::values` and `Problem::computations` start at the floor, for closed sides.
- **A step budget.** The caller sizes `StepBudget` in `MachineSettings`, or takes `StepBudget::DEFAULT`; exhaustion is `MachineVerdict::Declined(DeclineReason::Budget)`, a decline rather than a verdict.
- **A memo type, not a memo.** The caller names the memo type `decide` re-shares through — `ResharingMemo` on the engine path, `NullMemo` for the memoless differential — and `decide` builds it empty for the run, because its outcomes are that run's process ids. The memo's entry accounting refusing at its ceiling is `ConversionFault::Memo`.
- **Shares placed where their legs are read.** Erasure copies a leg's indices to every occurrence unshifted, so a free index in a leg names the binder it reaches from the occurrence. A producer that means one binder at every occurrence places the share inside that binder.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.

## Examples

Evaluate a closed pair and read it back without minting a core node:

```rust
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_value;
use gandr_core_nbe::readback_value;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;

fn round_trip() {
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let source = core.value_tuple(&[unit, unit]);

    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let budget = Fuel::from(64_u32);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, budget, source)
        .expect("a closed pair evaluates");

    // Nothing reduced, so the zero-unfold mode answers with the source id.
    let mark = core.watermark();
    let read = readback_value(&mut core, &mut domain, definitions, ReadbackMode::ZeroUnfold, budget, evaluated)
        .expect("an unreduced pair reads back");
    assert_eq!(source, read);
    assert_eq!(mark, core.watermark());
}
```

Run the tests, then again with specifications enforced:

```sh
cargo nextest run -p gandr-core-nbe
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-core-nbe
```

## Where the detail lives

Mechanism, rules, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Provided items in detail, references, optional tracing, what stays in the kernel, specification attributes | [`src/lib.rs`](src/lib.rs) |
| Term and unfolding faces, neutrals and spines | [`domain`](src/domain.rs) |
| The per-run arena | [`arena`](src/arena.rs) |
| Closure spaces | [`closure`](src/closure.rs) |
| Scheduling, duplication and granularity stances | [`policy`](src/policy.rs) |
| Evaluation, lowered definition bodies, native data and records, source sharing | [`eval`](src/eval.rs) |
| Readback modes | [`readback`](src/readback.rs) |
| Conversion steps 1 through 3 | [`conv`](src/conv.rs) |
| The conversion machine, native universe paths, termination | [`machine`](src/machine.rs), [`rules`](src/rules.rs) |
| Codes and static operators | [`code`](src/code.rs) |
| The cached word | [`guard`](src/guard.rs) |
| Process re-sharing | [`resharing`](src/resharing.rs) |
| Derivations and trace pairing | [`derivation`](src/derivation.rs) |
| The sharing overlay, erasure, the measure, duplication and overlay evaluation | [`overlay`](src/overlay.rs), [`measure`](src/measure.rs), [`duplicate`](src/duplicate.rs), [`overlay_eval`](src/overlay_eval.rs) |
| Closed-configuration sharing and the certifying path | [`traced`](src/traced.rs) |
| Live evaluation | [`live`](src/live.rs) |
| Strict stage normalization | [`stage`](src/stage.rs) |
| References | [`src/lib.rs`](src/lib.rs), [`policy`](src/policy.rs), [`closure`](src/closure.rs) |

## References

- `Dybjer-2012-program_testing_meaning_explanations_intuitionistic_type_theory` — background: Peter Dybjer, "Program Testing and the Meaning Explanations of Intuitionistic Type Theory", _Epistemology versus Ontology_, 2012 — a judgement tested by running it on generated input, the reading the spinal stance enters on.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — background: § 6 — a sharing mechanism enters on a property test against its reference and an informal simulation argument.
- `vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa` — background: sharing as descent; the spinal granularity makes the Courant and Leroy row finer along the spinal row.
- `vault:01a178aa-fe00-7121-9fe8-2df35cbb1aeb` — background: a finer sharing installs only behind a replayed trace.
- `vault:01a183de-4ab1-7660-a88a-04b9e8d318e3` — exemplar: the source page of Beniamino Accattoli. "Back to the Future of Lambda: Refreshing the Lambda-Calculus for the 21st Century." Habilitation, Institut Polytechnique de Paris, 2025. `hal:tel-05454767` — § 3.9's practical values, which the environment's value ids keep, and § 4.2's useful sharing, whose compact normal form readback builds.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: a composite evaluates as the fold it realises.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
