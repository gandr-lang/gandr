# gandr-theory-computads

The elaborator seam of the cell-rewriting stack: a levitated description's rules elaborated into command cells at the declaration's polarity through one admission seam, and a two-redex circuit rule instantiated where the identification of its two sequentializations is decidable, with the convexity re-check supplied by the caller.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `elaborate_data_desc` reads a whole description into one sequent cell store: a frame-defining cell per constructor, a cell per admitted rule face and circuit rule, and the η cells the declaration licenses, every one cut at the declaration's polarity, with every declined member reported beside the store (`DescElaboration`). `elaborate_rule` is the face-to-cell step on its own. `instantiate_two_redex_rule` applies a two-redex circuit rule at a peak and earns, or refuses, the identification of its two sequentializations; `ConvexitySupply` is the point where a caller hands it the convexity re-check a store without a discharge is owed. `instantiate_cell` instantiates one stored cell under a substitution into the same store.

**Why.** A description states rules and the engines rewrite cells. Something has to decide which of a description's rules a cell store can hold, refuse the rest with a reason a reader can act on, and fix the cut each cell fires at; that is this crate, and it is the one place those decisions are made. A circuit rule whose body holds two redexes denotes a horizontal composite only where its two sequentializations are shift-equal, which is a question about two cells at two positions of one term, so it is asked at an application rather than at the declaration.

**How.** Face elaboration is the sequent-machine flattening: an operation application cuts its first argument against the operation's frame, and a constructor wrapping an operation becomes a return-side frame on the continuation. Every walk is a loop or an explicit stack, so no term's depth reaches the call stack. Cells enter the store through one seam that refuses a copied hole, then a hole worn at both polarities. Instantiation reads its positions from the body's occurrence record, asks the shift guard, asks the caller's supply point where the store withholds its convexity discharge, fires both orders, and replays the witness before handing it back. Refusal is data: every decline is a typed value carried to the caller.

## Provided features

- `elaborate_data_desc`, `elaborate_theory_desc`, `DescReading`, `DescElaboration`, `OpFrame`, `OpElaborateError`, `CircuitElaboration`: a whole description into one store under its reading — a family's generative one or a presentation's shape one — the operation gate first, every decline reported; a many-out operation's frame carries one return continuation per output port.
- `elaborate_rule`, `ElaborateError`: one face into one cell at the declaration's polarity; a results tuple leaves by one delivery frame, and a result count other than the output count is refused.
- `PresentedRules`, `presented_reading`, `TermAlphabet`, `Term`, `face_cell`: a presented type's constructor-headed rules, and a presentation's laws that apply an operation where an argument stands, with the operation rules beside them, read over first-order terms where every subterm is a position, so a rule fires below the root and two rules overlap inside a left-hand side.
- Every cell a declaration contributes — frame, rule, circuit and η — cuts at the polarity its η law requires, and a `codata` declaration's η critical pair joins.
- The admission seam's two refusals, `ElaborateError::NonLinear` and `ElaborateError::MixedPolarity` with `MixedPolarityHole`, distinct in variant and diagnostic, the copy decided first.
- `EtaElaboration`, `EtaElaborateError`: the η cells a declaration licenses, at its polarity, or the missing half of the licence.
- Circuit rules through the same seam, declined first when their body denotes no single composite.
- `instantiate_two_redex_rule`, `RewriteBinding`, `CircuitShift`, `CircuitShiftObstruction`: the earned identification and its refusals.
- `ConvexitySupply`, `ConvexityGrant`: the caller's re-check, asked exactly when the store withholds its discharge and the first two conjuncts hold.
- `instantiate_cell`, `CellInstantiationError`: one stored cell under a substitution, into the same store.
- The reduction order over the cells a real description elaborates: the equal-size face pairs it orients, and the fusion cell completion derives.

## Expected features

- **A checked description.** Whether a face's symbols belong to the declaration, and whether an arity's maps compose, are the description table's own checks (`check_desc`); elaboration decides only what the cell layer must, and a caller wanting both verdicts runs both passes.
- **A diagram reading for the supply point.** The convexity re-check is the caller's. A caller with no re-check passes a supply point that refuses, and a store that withholds its discharge then refuses every pair rather than assuming the conjunct.
- **Stores sized for declarations.** A store's insertion scans the store, and the shift guard builds its overlap support per question; both are sized for the cells one declaration contributes.

## Examples

Elaborate a description and read what was admitted and what was declined.

```rust
use gandr_theory_computads::EtaElaboration;
use gandr_theory_computads::elaborate_data_desc;
use gandr_theory_levitation::TheoryDesc;

fn example<G>(desc: &TheoryDesc<G>) {
    let elaborated = elaborate_data_desc(desc);
    for (index, refusal) in &elaborated.declined_faces {
        let _ = (index, refusal);
    }
    if let EtaElaboration::Declined(reason) = &elaborated.eta {
        let _message = reason.to_string();
    }
    let _cells = elaborated.store.len();
}
```

Instantiate a two-redex circuit rule over a store that discharges its convexity conjunct, with a supply point that refuses whatever it is asked.

```rust
use core::convert::Infallible;

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_computads::ConvexitySupply;
use gandr_theory_computads::RewriteBinding;
use gandr_theory_computads::instantiate_two_redex_rule;
use gandr_theory_levitation::CircuitRule;

struct NoRecheck;

impl<A: CellAlphabet> ConvexitySupply<A> for NoRecheck {
    type Warrant = Infallible;
    type Refusal = ();

    fn recheck(
        &self,
        _store: &CellStore<A>,
        _peak: &A::Cmd,
        _first: &CellApp<A>,
        _second: &CellApp<A>,
    ) -> Result<Infallible, ()> {
        Err(())
    }
}

fn example<A: CellAlphabet>(store: &CellStore<A>, rule: &CircuitRule, peak: &A::Cmd, f: CellId, g: CellId) {
    let bindings = [RewriteBinding::new("p", f), RewriteBinding::new("q", g)];
    match instantiate_two_redex_rule(store, rule, &bindings, peak, &NoRecheck) {
        Ok(shift) => assert!(bool::from(shift.witness.replay(store))),
        Err(refusal) => drop(refusal),
    }
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-computads
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The supported fragment, the declaration's polarity, the admission seam, the operation gate, a presented type's rules, η cells, circuit rules and reports | [`elaborate`](src/elaborate.rs) |
| The term alphabet: why a second alphabet, its positions, order and renaming | [`term`](src/term.rs) |
| Instantiation and the convexity supply point | [`instantiate`](src/instantiate.rs) |
| Boundary wrappers | [`boundary`](src/boundary.rs) |
| The closed tier, specification evidence, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
