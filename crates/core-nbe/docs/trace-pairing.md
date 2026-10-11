# Trace pairing witnesses

How `gandr-core-nbe`'s machine tests pair component conversion traces and what the kernel's replay observes of each pairing. The crate's [README](../README.md) states the rest of the crate and lists every feature with its witnesses.

<!-- toc -->
- [Pairing](#pairing)
- [Witnesses](#witnesses)
- [Generator](#generator)
<!-- tocstop -->

## Pairing

The machine’s test consumer replays component traces independently before pairing them. A `Decompose` boundary followed by first-component-first concatenation certifies both alpha-equal and non-alpha-equal value pairs. The alpha-equal pair’s one-decision unit also certifies directly. A negative pair selects one refuted component with `NegativeSubgoal`; wrong selections retain their exact refusal classes and positions. Returner pairing uses the two checked boundaries supplied by `kernel-core::path_universe::Dialogue::pair`. No transitive certificate composition is provided.

| Case | Exact observation |
| ---- | ----------------- |
| Convertible components | Decomposition and concatenation replay `Convertible`; swapping two distinct unfolding traces refuses `Inapplicable { at: 2 }`. |
| Alpha-equal pair | Both `[ComparedShared]` and `[Decompose, ComparedShared, ComparedShared]` replay `Convertible`. |
| Refuted pair | The selected component replays `NotConvertible`; selecting its equal sibling refuses `Contradicted`, and an out-of-range selection refuses `Inapplicable`. |

## Witnesses

Witnesses live in `machine::tests::trace_pairing`: three fixed-seed properties run 256 recipes each over zero to seven left/right pair nestings. Positive recipes vary unfolding side and independent sharing of both components; alpha-equal sides are separately allocated; negative recipes select either component. The existing four-rung ladder generator also supplies all sixteen ordered pairs. Exact unfolding and refusal goldens distinguish constant verdicts, reversed component order, ignored selections, and erased refusal payloads. This is bounded evidence, not a proof for arbitrary terms or traces.

## Generator

The tests reuse workspace `proptest` 1.11, dev-only with defaults disabled and only `std` enabled for the runner and shrinking. QuickCheck would add another runner; manual sampling loses shrinking. Reconsider on an unmaintained release, a high-risk advisory, or a generator requirement it cannot express.
