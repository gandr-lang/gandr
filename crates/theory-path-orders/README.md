# gandr-theory-path-orders

Path orders over the terms of second-order algebraic theories, each returning evidence a checker replays.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The data a path order reads, as traits a caller implements over its own terms — `Term` for a side's positioned nodes, `Valued` for which of the left side's variables are values, `Precedence` for each symbol's place and status — and each ordering as an algorithm module generic over them. `lpo` is the lexicographic path order with lexicographic or multiset status, read at an instantiated variable as the computability path order reads a variable applied to terms. Every ordering returns one evidence type: a derivation whose steps name the clause that orients each pair of subterms it uses, which a checker replays without search. The crate is `no_std` over `core` and `alloc` and depends on no other workspace crate.

**Why.** A rewriting system's rules are decided terminating where they are written, where they are admitted and where they are completed: the front end orients a description's faces, the kernel orients an operation's rules and a theory's rules before it decides their critical pairs, and the cell layer breaks the size ties of the reduction its completion orients critical pairs by. One order, read by each over its own terms with its own precedence as data, keeps those decisions one decision; evidence the kernel replays keeps its trust independent of the search that found the orientation.

**How.** A side is read in the second-order reading of a term: each node a signature symbol applied to arguments, a rule variable bare or instantiated at arguments, an abstraction of one name, or a bound occurrence, and every node's arguments at positions past its own. A comparison fills one table over every pair of subterm positions from the last positions up, so no comparison recurses. Each cell records whether the pair is equal and, when the left is above, the first clause that orients it: an argument of the left equal to or above the right (subterm); a left symbol placed above the right's (precedence); one head with the first differing argument pair ordered, or the arguments ordered as multisets (status); or an instantiation of a variable an argument of the left holds, bare or under abstractions read up to η. Every clause but the subterm one needs each argument of the right covered: the left is above it, one of the left's own arguments is equal to or above it, or it is a variable the left values. A variable or an instantiation on the left stands above nothing. `orient` collects the steps the root cell relies on; `check` re-derives each step's clause from the steps its premises name.

## References

- Sam Kamin and Jean-Jacques Lévy. "Two Generalizations of the Recursive Path Ordering." Unpublished note, Department of Computer Science, University of Illinois, 1980 — the lexicographic path order.
- Nachum Dershowitz and Zohar Manna. "Proving Termination with Multiset Orderings." _Communications of the ACM_ 22(8), pages 465–476, 1979. `doi:10.1145/359138.359142` — the multiset extension the multiset status compares arguments by.
- Nachum Dershowitz. "Orderings for Term-Rewriting Systems." _Theoretical Computer Science_ 17(3), pages 279–301, 1982. `doi:10.1016/0304-3975(82)90026-3` — the recursive path order and the subterm property every clause rests on.
- Jean-Pierre Jouannaud and Albert Rubio. "The Higher-Order Recursive Path Ordering." In _Proceedings of the 14th Annual IEEE Symposium on Logic in Computer Science (LICS 1999)_, pages 402–411, 1999. `doi:10.1109/LICS.1999.782635` — the order on a variable applied to terms.
- Frédéric Blanqui, Jean-Pierre Jouannaud, and Albert Rubio. "The Computability Path Ordering." _Logical Methods in Computer Science_ 11(4:3), pages 1–45, 2015. `doi:10.2168/LMCS-11(4:3)2015` — the clauses the evidence names (Fb⊳, Fb>, Fb= at either status, Fb@), the cover premise, and the statuses.
- Johannes Niederhauser and Aart Middeldorp. "The Computability Path Order for Beta-Eta-Normal Higher-Order Rewriting." Preprint, 2025. `arXiv:2505.20121` — nonversatile terms: a variable or an instantiation on the left stands above nothing, and sides are read βη-normal.
- Liye Guo and Cynthia Kop. "Higher-Order LCTRSs and Their Termination." In _Programming Languages and Systems (ESOP 2024)_, pages 331–357, 2024. `doi:10.1007/978-3-031-57267-8_13`; preprint `arXiv:2307.13519` — a value needs no cover.
- Ambrus Kaposi and Szumi Xie. "Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics." In _9th International Conference on Formal Structures for Computation and Deduction (FSCD 2024)_, Leibniz International Proceedings in Informatics 299, pages 10:1–10:24, 2024. `doi:10.4230/LIPIcs.FSCD.2024.10` — the second-order reading of a term the five formers follow.

## Provided features

- `Term`, `Former`, `Node`: a side as positioned nodes, each a symbol applied to arguments, a variable, a variable instantiated at arguments, an abstraction, or a bound occurrence.
- `Valued`, `Valuation`: whether a left side's variable is a value, which needs no cover.
- `Precedence`, `Place`, `Rank`, `Status`: the precedence as data — each symbol ground or at a rank, at lexicographic or multiset status; two symbols are equivalent exactly when they are one symbol.
- `Evidence`, `Derivation`, `Step`, `Clause`, `Cover`, `Relation`, `Argument`, `CoverIndex`: the evidence every ordering returns, one step per subterm pair it uses, each naming its clause and the covers its premises rely on.
- `lpo::orient`, `lpo::check`: the lexicographic path order with status and its checker, over `lpo::Buffers` a caller reuses across comparisons; `lpo::Orientation`, `lpo::Replay` and `lpo::Refusal` their results.

## Expected features

- **The traits over the caller's terms.** A caller implements `Term` for each side and `Valued` for left sides, with every node's arguments at positions past its own: pre-order and breadth-first numberings both qualify. It implements `Precedence` over its symbol type.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation; `lpo::orient` then replays every derivation it returns. The enforcing test lane sets it.

## Examples

Orient a rule and replay the evidence, as the kernel does:

```rust
use gandr_theory_path_orders::Evidence;
use gandr_theory_path_orders::Precedence;
use gandr_theory_path_orders::Term;
use gandr_theory_path_orders::Valued;
use gandr_theory_path_orders::lpo;
use gandr_theory_path_orders::lpo::Buffers;
use gandr_theory_path_orders::lpo::Orientation;
use gandr_theory_path_orders::lpo::Replay;

fn oriented<L, R, P>(left: &L, right: &R, precedence: &P, buffers: &mut Buffers) -> bool
where
    L: Valued,
    R: Term<Symbol = L::Symbol, Variable = L::Variable, Bound = L::Bound>,
    P: Precedence<Symbol = L::Symbol>,
{
    match lpo::orient(left, right, precedence, buffers) {
        Orientation::Oriented(Evidence::Path(derivation)) => {
            lpo::check(left, right, precedence, &derivation, buffers) == Replay::Holds
        },
        Orientation::Unoriented => false,
    }
}
```

Run the tests, then the enforcing twin with every specification checked:

```sh
cargo nextest run -p gandr-theory-path-orders
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-path-orders
```

## Where the detail lives

| Module | States |
| ------ | ------ |
| `term` | the term view, the five formers, the position contract |
| `precedence` | places, ranks, statuses, symbol equivalence |
| `evidence` | the derivation, its steps, clauses and covers |
| `lpo` | the order's clauses in the order they are tried, the table fill, the derivation's extraction and its replay |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
