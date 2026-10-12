# gandr-theory-cell-complexes

The cell-shape substrate of gandr's rewriting stack: flat command patterns, matching, unification and anti-unification over them, the reduction order, the cell-alphabet trait with its sequent inhabitant, the cell store, and the linearity admission.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The vocabulary every rewriting engine above it quantifies over. A command pattern (`CmdPat`) is one cut `⟨p |ε c⟩` of a producer pattern (`ProdPat`) against a consumer pattern (`ConsPat`) at a `Polarity`, with metavariables (`MetaVar`) as holes; a `Pos` addresses a subterm, read by `subterm_at` and replaced by `splice_at`. A substitution (`Subst`) is extended by one-sided matching (`match_cmd`) and two-sided unification (`unify_cmd`), and a family of patterns folds into its least general generalization (`anti_unify_cmd`); `reduction_cmp` orients a pair or reports it unorientable. `CellAlphabet` is the one trait the engines are generic over and `SequentAlphabet` its inhabitant; a `Cell` is an oriented rewrite with metadata derived from its faces, kept in a deduplicating `CellStore`, and `admit_linear_cell` refuses a cell whose left-hand side copies a hole. The crate is `no_std` and depends on `core`, `alloc` and `quenchant-shape`.

**Why.** Completion, firing and normalization over cells all ask the same questions of a term language: does this pattern match here, do these two overlap, which side of this pair is larger, what replaces the subterm at this position. Answering them once, behind one trait, lets each engine be written and tested against any term language that keeps the trait's laws, and keeps the sequent command language — the first language the engines run on — out of the engines' code.

**How.** Patterns are flat node tables, so every walk over one is a loop and a pattern of any depth is matched, ordered and dropped on a small stack. Matching and unification run explicit worklists over borrowed subtrees and copy bindings into the substitution only when the whole walk succeeds. The reduction order lays both commands out as one node table each and fills the lexicographic path order's relation bottom-up, pair by pair. Absence and refusal are values: a lookup that can miss returns `Maybe` with a named reason, a refused operation returns `Result` with a typed refusal.

## Provided features

- `CmdPat`, `ProdPat`, `ConsPat`, `MetaVar`, `Sym`, `HoleName`, `Cat` and the borrowed views `ProdRef`, `ConsRef`, `ProdView`, `ConsView`, `ProdArgs`, `OpArgs`: the pattern language over flat tables, with sizes, groundness and metavariables in a fixed order, none of it recursive.
- `Pos`, `Node`, `NodeRef`, `subterm_at`, `splice_at`, `splice_cmd`, `SpliceRefusal`: positions as child-index paths, reading and splicing at them, and a splice of the wrong category refused by name.
- `Subst`, `match_cmd`, `unify_cmd`, `BindingRefusal`: an ordered substitution, one-sided matching and most-general unification with the occurs check, both transactional, and `Subst::restricted`, a substitution cut down to named metavariables.
- `anti_unify_cmd`, `Generalization`, `GeneralizationPoint`, `GeneralizationArm`, `anti_unification::Absent`: the least general generalization of a family of command-pattern tuples, with one point per distinct disagreement and one arm per member at each, and its three refusals by name.
- `reduction_cmp`, `path_order_cmp`: the guarded size comparison with the path order deciding ties, and the path order alone.
- `CellAlphabet`, `SeamRole`, `PositionOrder`, `path_order`, `ConvexityDischarge`, `CommandSpliceRefusal`: the 24-method alphabet interface and the shared path order on child-index positions.
- `SequentAlphabet`, `Orientation`, `CellProvenance`, `EtaKind`, `CellMeta`, `CellVarMeta`, `CellVariance`, `CellContractumUse`, `StepGrowth`, `frame_defining_cell`: the sequent inhabitant, its tags, its derived per-hole metadata and the η-polarity discipline.
- `Cell`, `CellStore`, `CellId`: cells with derived metadata, deduplicated on structure, addressed in insertion order.
- `admit_linear_cell`, `copied_hole`, `NonLinearPattern`: the left-linearity admission and its alphabet-neutral copy search.
- `Polarity` and the boundary wrappers (`PatternSize`, `PositionStep`, `SubstitutionDecision`, `CellInvertibility`, …): the cut's orientation and every count and verdict a signature here crosses.

## Expected features

- **An alphabet keeping the inhabitant laws.** An engine generic over `CellAlphabet` trusts four laws no type can state: substituting a match into its pattern reproduces the matched term; a successful match binds every metavariable the pattern names; reading at a position and splicing there agree, both ways; each member of a family is its generalization with its own arm applied at every point. An inhabitant also supplies a reduction order that is well-founded and stable under substitution, a deterministic renaming apart, and a convexity answer it can justify. The inhabitant suite of `gandr-theory-cell-complexes-tools` runs the four laws over an inhabitant through the trait alone.
- **Small faces.** Cell metadata derivation is quadratic in a face's occurrence count, and the store's deduplication is a linear scan; both are sized for rule sets, not for term-sized faces.

## Examples

Match the successor rule's left-hand side against a configuration and reproduce it.

```rust
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::match_cmd;

fn example() {
    // ⟨Succ(m) | add(n; α)⟩
    let lhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [ProdPat::meta("m")]),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
    );
    // ⟨Succ(Zero) | add(Zero; ★)⟩
    let zero = || ProdPat::ctor("Zero", []);
    let target = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [zero()]),
        ConsPat::op("add", [zero()], ConsPat::top()),
    );
    let mut subst = Subst::new();
    assert!(bool::from(match_cmd(&lhs, &target, &mut subst)));
    assert_eq!(target, subst.apply_cmd(&lhs));
}
```

Admit a rule cell and store it.

```rust
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::admit_linear_cell;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    // ⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩
    let lhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [ProdPat::meta("m")]),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
    );
    let rhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("m"),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::frame("Succ", ConsPat::meta("alpha"))),
    );
    let cell: Cell = Cell::new(lhs, rhs, Orientation::PolarityDerived, CellProvenance::SurfaceRule);
    admit_linear_cell(&cell)?;
    let mut store = CellStore::new();
    let id = store.insert(cell.clone());
    assert_eq!(id, store.insert(cell));
    Ok(())
}
```

Nontrivial operations carry executable `#[spec]` predicates and `# Adequacy` hypotheses with crate-local witnesses. The witnesses cover category boundaries, empty inputs, transactional refusals, substitution cycles, splice growth and shrinkage, metadata joins, and ordering obstructions. Run them normally and with predicate enforcement:

```sh
cargo nextest run -p gandr-theory-cell-complexes
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-cell-complexes
```

Const-compatible predicates check node-count arithmetic, polarity, variance and η requirements without removing compile-time availability. Items that cannot be instrumented without changing their interface state an `executable: none` reason beside the specification: abstract alphabet declarations, opaque iterator or strategy returns, and consumed one-shot paths. Renaming checks colliding images against the captured reserved-name set even though its input iterator is consumed. Formatting and the assertion-driven depth witness expose no readable result state for an exit predicate. These items retain explicit adequacy witnesses rather than weakening their contracts to satisfy instrumentation.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Polarity | [`polarity`](src/polarity.rs) |
| Pattern representation | [`pattern`](src/pattern.rs) |
| Matching, unification and renaming apart | [`subst`](src/subst.rs), [`sequent`](src/sequent.rs) |
| Anti-unification | [`generalize`](src/generalize.rs) |
| The reduction order | [`order`](src/order.rs) |
| The cell alphabet, its convexity warrant and its second inhabitant | [`alphabet`](src/alphabet.rs) |
| Cells and the store | [`cell`](src/cell.rs) |
| Linearity admission | [`linearity`](src/linearity.rs) |
| Boundary wrappers | [`boundary`](src/boundary.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
