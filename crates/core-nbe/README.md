# gandr-core-nbe

The glued value domain with both faces and both closure spaces, the per-run arena that owns them, the two policy parameters the domain is written against, and the two machines over an explicit task stack: evaluation to weak head, and readback back into the core term arena.

It holds the domain's **shape** — what a glued value is, what a closure is, and what the two policy parameters decide — the machine that evaluates a core term to weak head over it, and the machine that reads a weak head back by choosing among the faces that evaluation filled. It is `no_std` over `core` and `alloc`.

## Plan-milestone mapping

This crate answers the **value-domain milestone** of the ratified normalizer-and-elaborator plan where that milestone speaks about the domain. Its clauses map onto the modules:

| plan clause | where it lives |
| ----------- | -------------- |
| the glued domain naming the term face and the unfolding face | `src/domain.rs` |
| both closure spaces, named before either is exercised | `src/closure.rs` |
| the per-run arena, constructor-only minting, wholesale truncation | `src/arena.rs` |
| module forms enter as neutrals and cost nothing | `src/domain.rs`, `NeutralHead::Module` |
| the scheduling-policy parameter, uniform-fair default | `src/policy.rs` |
| the duplication-policy parameter, conservative stance, finer stance gated | `src/policy.rs` |
| evaluation to weak head | `src/eval.rs` |
| readback, choosing a face, with a zero-unfold mode | `src/readback.rs` |

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

## What it provides

- **The glued domain in both faces.** The **term face** caches the core term a domain node came from and holds it exactly while nothing inside reduced, so an unreduced subterm reads back as an id rather than a rebuild; where something reduced, the face says so, because a stale source id is a wrong readback rather than a slow one. The **unfolding face** holds a neutral's neutral form beside a lazily forced unfolded form, and forcing adds the second reading without replacing the first.
- **One neutral family, separated by its spine.** The term vocabulary has no value eliminator, so a neutral in value position carries an empty spine and one in computation position carries the applications, binds and cases that could not fire. The condition is enforced by the arena constructor rather than left to a convention. Module forms are rigid heads: no eliminator is written for them and no arm replaces one by a representation.
- **Both closure spaces over one environment.** A value body and a computation body are both suspendable, and entering a closure is one operation, so both spaces are named even though only the computation space has producers at today's vocabulary. The environment mirrors the typing context's two zones, which is forced rather than preferred: an occurrence names a zone, and a single-stack environment could not answer a linear one.
- **The per-run arena**: six typed id families, constructor-only minting — a child id is below its parent's within its family, and across families acyclicity rests on the minting order rather than on the id ordering — and truncation to a watermark, which at the floor is the run's whole teardown, six flat vector drops in any order.
- **The two policy parameters**, with the properties that make them parameters rather than switches.
- **Evaluation to weak head as a machine**: a task stack and two result stacks rather than two mutually recursive functions, so the depth lives on the heap. It populates the term face by a check rather than a convention — a composite keeps its source exactly when every child came back denoting the corresponding source child — and it populates the unfolding face from the definition chain read through the scope's transparency, expanding nothing. It carries a fuel budget, because β and `force` alone suffice to loop.
- **Readback as the same machine shape**, over the domain rather than over the syntax, and the consumer the two faces were populated for. It **chooses** a face: in `ReadbackMode::ZeroUnfold` a node whose term face names its source hands that id back and mints nothing, and no unfolding is forced, so a neutral's body is still unforced when the readback returns; in `ReadbackMode::Unfolding` every node is rebuilt and an unfolding already forced is spent. Going under a binder mints a fresh variable at a de Bruijn **level**, evaluates the closure's body against it out of the same fuel budget, and converts the level back to the index the syntax counts in — with both subtractions checked and a level outside the open binders refused by name.

## The honest cost

A glued node names core-language nodes it does not own: the source term its term face caches, the literal payload it points at, and the body every closure suspends. Those ids resolve in the `CoreArena` the run is evaluating, and the domain arena has no way to check one.

The precondition every constructor inherits is one sentence: **the core arena outlives the domain arena and is not truncated below any node the domain holds.** The mitigation is the run discipline rather than a check — one domain arena per evaluation run, over one core arena, torn down together.

Readback inherits a second sentence of the same kind, and it is what makes the source-face short circuit sound: **every term face the readback reaches names a closed core value.** Evaluating well-scoped terms produces exactly that — a bound occurrence resolves out of the environment and costs its parent the face, and a closure that kept the face captured nothing — so splicing a source id under any number of open binders denotes what it always denoted. The condition is not free: `thunk (λ. return x₁)` read in the empty environment keeps its face even though its unevaluated body has a loose index, because a suspended body is never evaluated and so is never scope-checked. Checking closedness at the short circuit is the whole traversal the short circuit exists to avoid, so the run discipline carries it, as it carries the cross-arena ids.

## The two parameters, and the properties that bind them

**Scheduling: a share never forecloses a proof.** A definitional height is a prior about which side is cheaper to unfold. As a gate on which reductions are attempted it can foreclose the short proof; as a share it changes only how fast each process runs. The module enforces that rather than describing it: every stance gives every height a **strictly positive** share, so no stance can starve a process to a standstill and thereby gate what it was only meant to weight. The uniform-fair stance is the default and the height-weighted stance sits behind it. The non-uniform-share bound that motivates the parameter remains its source's conjecture, which is why it motivates rather than commits.

**Duplication: the finer stance is representable and refused.** The erase-and-clone stance is the baseline and the unshared reference every later stance replays against. The spinal stance is part of the parameter's shape — a parameter that could not express it would fix nothing — and it is refused at installation while the conversion trace that would certify it by replay is absent. The results that would certify it are stated over simply-typed systems that type no fragment of this language, so the refusal is the trace-before-strategy ordering made mechanical rather than a note in a design document.

## The contract attributes

The `# Specification` prose stays the statement of record, and fifty of the crate's fifty-two blocks now carry a `#[spec(...)]` whose clauses state exactly what that prose states. `SchedulingPolicy::share` mirrors the one clause that is both cheap and load-bearing: the share is strictly positive. That is the whole non-foreclosure property, and it is an assertion rather than a returned refusal, so a stance that answered zero would abort at its first call rather than pass a review.

Each remaining prose-only block names its boundary in `provides`: an assembly frame pops its operands in the same step that pushes its result, so no relation between a step's entry and exit stack lengths states that the result reached the stack of its own polarity. Both machines' `step` dispatchers hold that shape. Where a clause covers part of a prose line — a graph judgement over a produced term, a law relating several calls, or an owned entry snapshot the pinned expansion would evaluate even in a non-enforcing build — the block's `provides` line names the residue and the witnesses that carry it. No prose line was weakened to fit a clause, and the crate defines no `const fn`, so the `E0015` exception has no site here.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## Not provided

No lowering of a definition body. The chain names a body by its canonical subterm-table entry index, which is arena-independent by construction; turning one into nodes of a particular core arena is a pass this crate does not carry. The consequence is stated rather than hidden: `ReadbackMode::Unfolding` refuses an `Unfolding::Unforced` body with `ReadbackFault::UnloweredBody`, naming the entry index, instead of quietly answering the neutral form under a mode that promised to unfold it. A caller that has forced the body itself gets the unfolded reading.

No canonical no-unfold readback. The two modes are the two the design needs now — retain the source face and force nothing, or rebuild and spend what has been forced. "Rebuild but force nothing", which a conversion comparing normal forms would want, is one arm away and is not written until that consumer exists.

No preservation of source sharing, in either machine. A core term is a DAG and the evaluator walks it as a tree, so a node reached twice is evaluated twice; readback mints a fresh core node per rebuilt domain node, so a domain value reachable by two paths is read back twice. That cost is what the duplication parameter and the memo seam exist to remove, and removing it here with a cache keyed on the source node would put a sharing decision inside the walk rather than behind the parameter that owns it. The fuel budget is what bounds the expansion in the meantime.

No type evaluation. Types are never forced into redexes, so only the two evaluation families carry domain entries.

No sharing overlay. Its place is beneath the duplication parameter named here, which is the order that keeps the parameter honest: an overlay asks the policy rather than deciding for itself.

No conversion machine. It is its own milestone and it stands on the trace vocabulary as well as on the readback here.

## Using it

`cargo test -p gandr-core-nbe --all-targets` runs the suite. Beyond the unit suites it carries four integration witnesses:

- the **teardown** witness — a chain made deep in every family that owns heap data, released in both orders inside a deliberately small stack, observed through a weak handle so the claim is that the arena is flat rather than that the symptom was ordered away;
- the **deep evaluation** and **deep readback** witnesses — chains of both polarities evaluated and read back inside a deliberately small stack, so the claim is that each machine's depth lives on the heap rather than that the case happened to fit;
- the **pinned-term** witness — terms evaluated, read back, and compared structurally against expected terms written out by hand, so the oracle is external to the machine rather than another run of it.

```rust
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_value;
use gandr_core_nbe::readback_value;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionalEnvironment;

fn example() {
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let source = core.value_pair(unit, unit);

    let chain = DefinitionChain::new();
    let environment = DefinitionalEnvironment::new();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let budget = Fuel::from(64_u32);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, budget, source)
        .expect("a closed pair evaluates");

    // Nothing reduced, so the retaining mode answers with the source id and
    // mints no core node at all.
    let mark = core.watermark();
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        budget,
        evaluated,
    )
    .expect("an unreduced pair reads back");
    assert_eq!(source, read);
    assert_eq!(mark, core.watermark());
}
```

## Theoretical ideas relied on

Normalization by evaluation with a glued domain, in which a value carries both what it denotes and how it was written, so readback can return the source term where nothing reduced; the reading of laziness as a **scheduling** restriction rather than a representation, which is what lets a definitional height be a share instead of a thunk policy; and the sharing ladder, on which the erase-and-clone baseline and the spinal stance are two rungs of one axis rather than two designs.

## Primary references

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — laziness recovered by scheduling rather than by representation, and the non-uniform-share conjecture the scheduling parameter is motivated by and not committed to.
- Nathanaëlle Courant. _Towards an Efficient and Formally-Verified Convertibility Checker_. PhD thesis, Université Paris Cité, 2024. HAL `tel-04884688`, chapter 12 — the complexity analysis whose exponent is the size of the smallest proof, which is the axis a duplication stance moves.
- Thibaut Balabonski. "Weak Optimality, and the Meaning of Sharing." _ICFP 2013_, pages 263–274. `doi:10.1145/2500365.2500606` — spinal and ordinary full laziness are both β-optimal for weak reduction, so the finer stance pays only under strong reduction. This is why the duplication parameter stays measurable rather than being a design-time commitment.
- Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_. Semantics Structures in Computation 2, Springer, 2003. `isbn:978-1-4020-1730-8` — the polarity split the domain's two halves follow. Locator unverified: the ISBN identifies a printing and has not been checked against a title page.

## License

Apache-2.0 WITH LLVM-exception.
