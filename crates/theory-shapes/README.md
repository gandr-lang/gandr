# gandr-theory-shapes

A finite face calculus with checkable entailment evidence and an endpoint-only affine bridge interval. This leaf crate is a statement of a shape parameter, not a new type former or an embedding into a logical framework.

## The shape parameter `ft`

| Part | Presentation |
| ---- | ------------ |
| Pseudotypes | Finite outer carriers `Finite(m)` and the bridge interval `Bridge` (𝔹). |
| Finite data | Decidable subsets of a carrier, included subsets with explicit complements, meets, unions, and outer union squares. |
| Bridge terms | A coordinate or one of the constants 0 and 1. |
| Bridge substitutions | A target coordinate receives an endpoint or a source coordinate. Each source coordinate occurs at most once. Exchange and weakening are allowed; contraction is not. |
| Atomic faces | Endpoint observations `i = 0`, `i = 1`, and finite membership `x ∈ S`. |
| Face formers | `⊤`, `⊥`, binary conjunction, and binary disjunction. |
| Axioms | Bounded distributive lattice laws; disjoint bridge endpoints; finite membership with its actual subset interpretation. |
| Absent operations | No bridge diagonal, `i = j`, reversal, or connections. Endpoint coverage is not an axiom. |

A bridge context is a tensor of coordinates, not their categorical product. For example, a map from one coordinate to two with images `(i,i)` is refused. The map `(0,0)` is allowed: constants are not resources. Composition preserves the partial-injection condition because each of its two component maps uses each source coordinate at most once. Repetition within a proposition such as `(i = 0) ∧ (i = 0)` is idempotence of faces, not a shape substitution.

A finite subshape is presented by a membership table over a shared ambient carrier. A cofibration records `S ⊆ T` and the complement `T \ S`. Given two subsets, `UnionSquare` partitions the ambient into intersection, left-only, right-only, and neither. Their union is the outer pushout over the intersection: agreeing maps from the two subsets determine the unique map on the union by these blocks. These are finite outer types, not colimits in a graphical site. The Rust data records that presentation; it does not implement arbitrary type-valued pushout elimination or a proof assistant's cofibrancy theorem.

The choice of a separate crate keeps finite shape data and the oracle below signature descriptions and kernel clients. Neither depends on the other's implementation. The only dependency is the workspace's specification attribute. The alternative was to place these definitions inside signature levitation; reverse this choice only if the shape language becomes intrinsically dependent on the signature representation rather than a parameter of it.

## Models and evidence

For endpoint-only observations a bridge coordinate has three cases: 0, 1, and generic. Generic means a fresh coordinate, **not a third constant of 𝔹**. Every observation assignment is realized by an affine substitution: choose distinct fresh coordinates for its generic entries. Every affine substitution produces one such observation assignment. A finite coordinate instead ranges over its actual points. An empty finite factor makes the whole observation context empty.

Entailment means implication at every observation assignment. This is complete for the stated face algebra: the free bounded distributive lattice on endpoint atoms quotiented by endpoint disjointness, together with the finite membership equations. In particular, the generic assignment refutes `⊤ ⊢ (i=0) ∨ (i=1)`. This finite observation semantics does not identify the interval with a discrete three-point shape.

Formulas are flat, topologically ordered DAGs. Construction rejects forward or cyclic references; problem construction checks atom scopes and sorts. Evaluation, search, replay, and destruction do not recurse through formula syntax.

`oracle::decide` produces either:

- `Holds(Derivation)`: a preorder rule tree. A leaf certifies that the premise is forced false or the conclusion is forced true. A split exhausts all cases of one previously unassigned coordinate. A split on an empty carrier has no children and proves vacuous entailment.
- `Refuted(Countermodel)`: a total, well-sorted assignment on which the premise holds and the conclusion fails.

Both evidence formats are untrusted public data. Their validators check them against the original query without invoking the search. Replay checks branch arity, leaf conditions, freshness of splits, and exact consumption of the rule stream. Countermodel validation checks scope, sorts, bounds, totality, and both truth values. Replay and search share the formula evaluator; the agreement suite uses a separately written Boolean evaluator and independently enumerated domains to check that semantic boundary too. This is executable evidence, not a machine-checked metatheorem of the Rust implementation.

## Complexity

Let `n` be the context size, `s` the total formula representation size including membership tables, and `d_i` the observation-domain cardinalities (3 for bridges). Exhaustive search takes at most `O((s+n)(n+1) ∏ max(1,d_i))` time, `O(s+n)` traversal storage, and storage for the accumulated proof prefix. That prefix is returned on success and discarded on refutation; it can be exponentially large in either outcome. Only coordinates appearing in atom nodes are split; unrelated coordinates are filled directly in countermodels. Replay is linear in the proof size times formula-evaluation cost, with a linear working stack. Validating a countermodel is polynomial in the input size.

Atomic-to-atomic queries mention at most two coordinates, so this implementation is polynomial for that fragment. Pure conjunctions also admit a polynomial per-coordinate intersection algorithm; that specialized algorithm is not claimed for the general search implemented here.

**General entailment is coNP-complete even without diagonals or `i = j`.** A nonentailment assignment is a polynomial certificate. For hardness, translate a Boolean CNF `C` into endpoint formulas, sending a positive literal to `i = 1` and a negative literal to `i = 0`. Conjoin the coverage assumptions `∧ᵢ ((i = 0) ∨ (i = 1))`. The resulting face entails `⊥` exactly when `C` is unsatisfiable. The coverage assumptions exclude generic observations; they are not added as global axioms. Thus deleting shape diagonals and variable equality does not lower this composite language below the coNP bar identified by Rose–Licata, unless P = NP. Positive derivations can be exponentially large.

That bar is a property of the composite language, not a cost the kernel pays. gandr's transport is replay — structural recursion over a trace — and consults no entailment procedure; the questions a checker asks at a boundary mention one face or a conjunction of faces, the polynomial fragments above, and over finite carriers alone entailment is set inclusion. The composite oracle exists so that any formula a client does write receives evidence either way; the boundary-parity family in the measurements is the worst case of that service, not a workload the kernel generates.

Run the reproducible measurement command:

```sh
mise exec -- cargo run --release -p gandr-theory-shapes --example measure
```

It reports the median of five decisions after one warmup. Construction, replay, and proof destruction are outside the timed region; every result is replayed. The growing-syntax family proves full endpoint coverage implies the even-or-odd parity partition, whose shared-DAG syntax is linear in the number of dimensions. The atomic family varies the ambient context while mentioning only its last coordinate. These are measurements of this search strategy, not lower-bound proofs for all possible algorithms or stable performance thresholds.

The agreement suite exhausts all atom pairs and all one-connective formulas against atoms in both directions, then checks 256 deterministic generated DAG pairs per context (32 additional binary nodes per formula). Contexts contain up to four bridge coordinates and one finite carrier of size 0–4, or two finite carriers independently of size 0–4; every subset is included. The largest observation product has 324 assignments. It also checks forged evidence, malformed inputs, deep formulas, all finite subset pairs up to four points, finite union mediators into a two-point target up to three points, and small affine maps and composition up to three coordinates. No claim is made to exhaust all unbounded formulas or all products of arbitrarily many finite carriers.

## Glue and the framework boundary

Given `Γ ⊢ A : U`, a face `φ`, and `Γ,φ ⊢ T : U` and `f : T → A`, the intended rule forms `Γ ⊢ Glue[φ ↦ (T,f)] A : U` without requiring `φ` globally. It restricts judgmentally to `T` under `φ`, and its `unglue` map restricts to `f`. For the empty face, Glue is `A`. Here `f` must be the forward half of a checked `Path_U(T,A)` equivalence certificate, including its inverse and inverse laws. This uses the equivalence-input reading associated with CCHM fibrancy; the FaceTT abstract also summarizes ParamDTT's arbitrary-function Glue for relatedness. The certificate requirement intentionally excludes an arbitrary uncertified map. Given such an equivalence `A₀ ≃ A₁`, take constant base `A₁` and glue `A₀` at `i=0`; restriction at the two endpoints gives `A₀` and `A₁`. This specifies a bridge family, not Kan fibrancy, univalence, or an implemented type former.

**A structural ToS⁺/SOGAT framework with representable `π⁺` sorts does not natively provide this affine sort.** For an ordinary representable constant sort `B`, context comprehension and substitution already admit the map `(x,x)` from `Γ,x:B` to `Γ,x:B,y:B`. There need not be a named diagonal operation in the signature. Making `B` nonrepresentable removes its binder; it does not give an affine binder. Removing equality faces has no effect on this structural fact.

A structural metatheory can encode affine contexts and their maps as data. That is distinct from making its own substitution affine. An extension-type unit therefore needs either explicit indexed affine-context/substitution semantics and their binding laws, or a framework with a separate affine context discipline. In either case substitution action on faces, restriction, and Glue coherence remain obligations before these rules can become a kernel feature.

The FaceTT slides include shape equality and cartesian arities. This crate is a FaceTT-style parameter presentation with a separately stated affine base; it is not evidence that the published parameter mechanism already admits that base.

## Sources

- Schönlank, Nuyts, Devriese, [Towards FaceTT: a generalization of intensional type systems with glue](https://types2026.cse.chalmers.se/abstracts/42.pdf), TYPES 2026; [slides](https://types2026.cse.chalmers.se/slides/42.pdf).
- Rose, Licata, [Complexity of Cubical Cofibration Logics I: coNP-Complete Examples](https://doi.org/10.4230/LIPIcs.TYPES.2024.9), 2025.
- Kaposi, Xie, [Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics](https://doi.org/10.4230/LIPIcs.FSCD.2024.10), especially the scope statement and Definition 13, 2024.
- Cohen, Coquand, Huber, Mörtberg, [Cubical Type Theory: a constructive interpretation of the univalence axiom](https://doi.org/10.4230/LIPIcs.TYPES.2015.5), 2018, §6.
