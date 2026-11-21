# gandr-core-checker-base

The base of the core checking judgement. It gives one verdict for each name-free declaration of a module, and it classifies each refusal by whose fact it is. The kernel bridge and the top compile over this crate. An edit of the bridge rebuilds neither the base nor a crate that reads only the base.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `check_module` judges name-free `Declaration`s in a `CheckingContext` over a core arena. Its `Verdict` records an admitted data signature, a checked body, a synthesised type, an owed hole, a suspension or a refusal. The ledger collects holes; refusal classification separates malformed source, unimplemented features and engine faults.

**Why.** A frontend needs stable per-declaration verdicts that distinguish what the author owes from what is wrong. The judgement and the module run read the context's private state, so they share one crate.

**How.** One goal-and-frame machine charges each transition to `CheckBudget`, one for a value goal met again; [`src/lib.rs`](src/lib.rs) states its shape and the boundary each module owns. The witnesses of an item are tests of this crate, or tests of a crate over it named with that crate's package. The integration target takes the bridge and the top as dev-dependencies, so a case can judge a module and readmit it. The `fixture` feature opens the test fixtures to the tests of the bridge and the top.

## Provided features

- `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp`, `Synthesised` and `Checked`: the four directed faces.
- Pairs, static lambdas and static applications in the faces, by the rules [`judgement`](src/judgement.rs) tabulates.
- Native list introductions against `List A` and the pure fold, by the rules [`judgement`](src/judgement.rs) states.
- `ConversionCount`: the declared projection of the conversion boundary, returned by every face.
- `form_value_type`, `form_comp_type`, `FormedValueType` and `FormedCompType`: formation as a judgement, and the types the check faces take.
- `type_value`, `type_module`, `Typing`, `Formed`, `Typings` and `Formations`: the typed run, keeping the type of every term it judged, refused ones too, and the level of each type it formed or `Formations` names.
- `classify_value_type`, `classify_comp_type` and `level_of`: the unique classifier of each formed type.
- `CodeDefinitions`, `Certificate`, `Unfolded`, `unfolding::Absent` and `Lift`: static definitions, certified reductions and recorded universe lifts.
- `Declaration`, `DeclarationContent` and `OriginToken`: name-free value/data input.
- `check_declaration`, `check_module`, `Verdict`, `Judged` and `ModuleReport`: one verdict per declaration, retaining accepted value definitions, native data signatures and recorded lifts.
- `Nesting`, `NestedElaboration` and `ModuleReport::nested_elaborations`: each computation written where a value is read, run or suspended by the type expected there, and the body rebuilt with every run bound.
- `Funext`, `Equivalence`, `Reflexivity` and `EndpointRelation`, each with its `ModuleReport` list: function extensionality, `equiv(f, g)`, reflexivity and the path endpoints a type conversion relates, decided by computation with the traces the kernel replays; `ua::derive` and `ModuleReport::natives`: `ua_n` at every certified stratum, and the native paths it and `pathProduct` cross as.
- `CheckingContext::keep_strata_in`, `CheckingContext::level_two` and the store of strata in [`ua`](src/ua.rs): the strata a context holds for its life, recalled from a store the driver implements and replayed before use.
- `CheckRefusal::ComposeUncertified`, `ComposeNotAShape`, `ComposeDoesNotFill` and `compose::chain_budget`: a chain's unbiased composite, its chains under a budget.
- `check_declaration_supported`, `Supported`, `Support`, `Consulted` and `CheckingContext::adopt`: query-specific value/data answers and adoption into the new prefix.
- `CheckingContext`, `CheckBudget`, `CheckingContext::memoise_goals` and `signature_table::Absent`: context, admission tables, allowance, goal memo.
- `ModuleRun`, `Checkpoint`, `CheckingContext::checkpoint` and `CheckingContext::resume`: a module judged in stretches, each continuing the last one's state.
- `Absence`, `ObligationEntry`, `ObligationLedger` and `ObligationCount`: the absence-only ledger.
- `CheckRefusal`, `Mismatch`, `CheckingForm`, `ExpectedShape`, `UnadmittedFormer`, `TermNode`, `TypeNode` and `CoreNode`: named refusals and responsible nodes.
- `StaticArity`, `ArgumentPosition` and family refusals preserve the failing argument or arity.
- `CheckRefusal::classify` assigns producer-failure classes ([`refusal`](src/refusal.rs)).
- `CheckRefusal::compared`, `Compared` and `compared::Absent`: the expected and the found types a refusal sets against each other, as nodes a face spells.
- `Failure`, `Obligation`, `FrameRole`, `FoldPremise`, `Pursuit`, `Stage`, `judged` and `ModuleReport::failures`: what the machine held when it refused, per refused body by position ([`failure`](src/failure.rs)).
- `Retirement`, `Demand`, `Polled` and `Unretired`: a run polled between its steps ([`retire`](src/retire.rs)).
- The hole surface: term holes, marks and the unknown type in the faces; `elaborate_value`, `elaborate_comp`, `Elaboration`, `MarkEntry` and `Direction`; `cover`, `Coverage`, `Exhaustiveness`, `Redundancy` and `CoverageFault`.
- `Verdict::Suspended` and `ModuleReport::suspensions`: a judgement held on an owed code hole ([`elaboration`](src/elaboration.rs)).
- `CheckRefusal::TacticRefused`, `TacticFault`: a splice's tactic run at its goal ([`tactic`](src/tactic.rs)).
- `body::Absent::Discharged` and `CheckRefusal::UndischargedLaw`: a law a model leaves out, discharged by `here` at its left side where its sides convert, and refused naming it where they part ([`discharge`](src/discharge.rs)).
- `stage::compile`, `stage::Program::admit` and `stage::Program::execute`: certified first-order residual readmission for the experimental stage universe.

## Expected features

- **One arena per context.** Every id a declaration carries resolves in the `CoreArena` the `CheckingContext` was built over; an id that does not is refused as a dangling node.
- **One writer per arena.** `CheckingContext::new` holds the arena mutably for the context's life, and the judgement mints into it; a caller reads it through `CheckingContext::arena`.
- **Ascending admission positions.** Declarations are offered in admission order; a position not above every one admitted before it is refused.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Where the detail lives

Mechanism, rules, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Modes, static operators, the dependent arrow and the bind, the linear function, splits, holes in the faces, effects and control, native universe paths, element identity | [`judgement`](src/judgement.rs) |
| Function extensionality, universe equivalence, the product of universe paths, `ua_n`, composites and fillers | [`funext`](src/funext.rs), [`equiv`](src/equiv.rs), [`product`](src/product.rs), [`ua`](src/ua.rs), [`compose`](src/compose.rs), [`fill`](src/fill.rs) |
| Total elaboration and the typed run | [`judgement::elaboration`](src/judgement/elaboration.rs) |
| Records | [`judgement::native`](src/judgement/native.rs) |
| Temporary access | [`access`](src/access.rs), [`judgement::access`](src/judgement/access.rs) |
| The three bridges, consistency, smallness and variance; the fourth, a nested computation run or suspended | [`conversion`](src/conversion.rs), [`nested`](src/nested.rs) |
| Formation, the classifier, universes, quotes and decodes | [`formation`](src/formation.rs) |
| Code unfolding, `El` as unquote, and their certificates | [`code`](src/code.rs) |
| The fragment's type views | [`view`](src/view.rs) |
| The context, resolution by admission position, adoption | [`context`](src/context.rs) |
| Declaration input | [`declaration`](src/declaration.rs) |
| Verdicts, holes at the declaration grain, definitions, refused-body failures | [`module`](src/module.rs) |
| A model's omitted law, discharged | [`discharge`](src/discharge.rs) |
| The machine's failure and its frame roles | [`failure`](src/failure.rs) |
| The ledger | [`ledger`](src/ledger.rs) |
| Refusal classes | [`refusal`](src/refusal.rs) |
| Support | [`support`](src/support.rs) |
| Coverage | [`coverage`](src/coverage.rs) |
| Nominal data | [`former`](src/former.rs) |
| Accessibility, stage typing, derived eliminators, divergence | [`occurrence`](src/occurrence.rs), [`recursion`](src/recursion.rs), [`eliminator`](src/eliminator.rs), [`divergence`](src/divergence.rs) |
| The experimental stage universe | [`stage`](src/stage.rs) |

## References

- `Cockx-2018-elaborating_dependent_copattern_matching` — exemplar: Cockx and Abel, _ICFP_, 2018 — the solution step.
- `vault:01a1b48c-2d17-7fc1-80ce-cb35e5cffd0e` — background: Ljungström and Mörtberg, LICS 2023, `arXiv:2302.00151` — § 2.2's sphere eliminator, in `loops`.
- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: separation at a fork, its halves sharing an interface only to read it.
- `vault:01a12318-1fa4-7ce3-a8cd-541363ad6ed4` — exemplar: a former's rule reads its type at its weak head.
- `vault:01a178aa-a2df-7df1-b34d-3a0211d0b6cb` — exemplar: one transport per solved equation.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — a certified stratum persists in the store.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: § kernel-verdict-reuse — a recalled stratum is believed only once it is replayed.
- `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: line 2 of the performance picture — a value that the contexts of a process share is frozen.
- `vault:01a18572-6e13-7412-bc74-aa6a24d157c4` — exemplar: `t ↑ X`'s square.
- `vault:01a178aa-5f59-7323-a77d-6f8114cedbba` — lineage: § The filler ban — a fill computes to its induction, and nothing adjoins a cell.
- `vault:01a183fc-63df-77a0-9df0-1c3f0b02ddf6` — anchor: Kovács, _POPL_, 2026, `doi:10.1145/3776685` — the signature type of § 2.2.
- `vault:01a1b567-b34b-77a2-9ace-075796f0eb3e` — exemplar: Hancock and Hyvernat, _APAL_, 2006 — a loop that follows its protocol is a demonic iteration.
- `vault:01a178aa-b5ea-75c1-8677-c85c447790b4` — anchor: the ∃! rule — a refusal names the slot or every candidate.
- `Wood-2024-framework_semiringannotated_type_systems` — newest: Wood, PhD thesis, Strathclyde, 2024 — graded access at `{0, 1, ω}`.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
