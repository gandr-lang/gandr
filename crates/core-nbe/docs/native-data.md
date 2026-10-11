# Native data, records and fixpoints

How `gandr-core-nbe` evaluates nominal constructors, cases and records, and the guarded fixpoint `fix x. M`, and how it reads back and compares them. The crate's [README](../README.md) states the rest of the crate; the kernel's [recursive data page](../../kernel-core/docs/recursive-data.md) states the typing and the replay these decisions are certified against.

<!-- toc -->
- [Constructors, cases and records](#constructors-cases-and-records)
- [Two gates unfold a fixpoint](#two-gates-unfold-a-fixpoint)
- [Readback and conversion](#readback-and-conversion)
- [Evaluation does not read the evidence](#evaluation-does-not-read-the-evidence)
- [The fixpoint decision](#the-fixpoint-decision)
- [Witnesses](#witnesses)
<!-- tocstop -->

## Constructors, cases and records

Constructors and records retain ordered lazy field closures in flat arena spans. Projection demands only the selected field; data case selects exactly its tag's branch and supplies only that constructor's fields. A neutral head retains the elimination until unfolding exposes its constructor or record. Readback reconstructs every native child and classifier. Arena truncation restores the field-span watermark as well as the node tables.

The sequent machine's command IL runs native constructors and cases and refuses records by name. The structural index-conversion boundary and deferred readers are in the [checker floor](../../core-checker/README.md#data-and-record-floor).

## Two gates unfold a fixpoint

`fix x. M` evaluates to `DomainComp::Fixpoint`, a computation closure over the fixpoint node itself, and is its own weak head until something observes it. Two gates unfold it once, `M[thunk (fix x. M)/x]`, with the self thunk bound innermost in the closure's environment: an application at a canonical argument, and a bind that runs it. At a neutral argument the application sticks, and the fixpoint waits on the neutral's spine as `Elimination::Fixpoint` until the head unfolds and the application resumes.

## Readback and conversion

Readback opens the self binder and rebuilds the fixpoint with its evidence. Conversion compares two fixpoints, and two stuck fixpoint eliminations, by their bodies under one self variable, whatever their evidence.

## Evaluation does not read the evidence

A partial fixpoint unfolds at the same gates, and a loop is bounded by the fuel every task is charged, not by the claim. Certification is where the claim matters. The kernel replays a structural-descent unfolding at a constructor and declines a partial one, so a decision the machine reached through a partial unfolding is computed but never certified.

## The fixpoint decision

**Choice.** A self-closure unfolded on demand, which keeps the domain arena acyclic and append-only and costs one closure per fixpoint.

**Alternatives.** A cyclic environment that ties the self binder to its own closure, which breaks acyclic minting; and eager unrolling to a depth, which guesses the depth.

**Reversal.** A measured workload whose cost is dominated by re-minting the self thunk at each unfolding, which would cache that thunk on the closure.

## Witnesses

- Native data and records: `eval::tests::native_records_and_cases_compute` distinguishes all five constructor arguments, selected module components and poisoned unselected thunks; `eval::tests::native_cases_reapply_when_head_unfolds` covers delayed elimination; `machine::tests::native_records_cases_and_traces_agree` checks independently replayed native comparisons.
- Fixpoints: `eval::tests::a_fixpoint_unfolds_at_a_constructor_and_sticks_at_a_neutral`, `eval::tests::an_observed_loop_runs_out_of_fuel`, `readback::tests::a_fixpoint_reads_back_with_its_self_binder` and `machine::tests::stuck_fixpoints_compare_by_their_bodies`.
