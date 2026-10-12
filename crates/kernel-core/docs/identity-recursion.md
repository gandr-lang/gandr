# Identity and bridge recursion

How `gandr-kernel-core` interprets a closed code vocabulary as identity or bridge relations, computes their fibres, and admits function identity. The crate's [README](../README.md) states the rest of the crate.

<!-- toc -->
- [The relation fold](#the-relation-fold)
- [Function identity and funext](#function-identity-and-funext)
- [Native fibres and admission](#native-fibres-and-admission)
<!-- tocstop -->

## The relation fold

The `identity_recursion` module folds a closed code vocabulary with `Mode::Identity` or `Mode::Bridge`. Identity also reaches the level-zero value universe, including occurrences beneath the admitted formers. It is an in-memory rule language beside `path_universe`, not persisted element-identity syntax. Endpoints are ordinary typed values in an open context; unsupported codes are refused before interpretation.

`Interpretation::path` consumes an ordinary native `ValueId`, synthesizes it through the declaration checker’s closed-value boundary and decodes the checked `PathUniverse` classifier. Native typing failures retain `KernelError` inside `RelationError::Typing`; endpoint failures retain `PathError`. No auxiliary path arena or formation cache participates.

| Code | Relation clause | Identity structure |
| ---- | --------------- | ------------------ |
| Unit | Unit fibre at every pair of indices. | Unit witness; reflexive transport returns its input. |
| Base | Discrete relation: identical indices give Unit; distinct canonical literals give Empty; unresolved neutral equality remains a relation. | Reflexivity is constructive; distinct variables are not assumed unequal. |
| Sum | Matching injections recurse on their payloads; different injections give Empty. An unknown injection remains suspended. | Payload reflexivity and transport use the matching branch. |
| Product | Component relations paired, including projections of neutral indices. | Componentwise reflexivity and composition; neither coordinate is dropped. |
| Thunk `U (A → F B)` | Suspended product `Π a₀ a₁. Rel(A,a₀,a₁) → Rel(B,force f a₀,force g a₁)`, with the same mode on both premises. | Higher-evaluation reflexivity and pointwise introduction; application transport replays both returners. |
| List A | Lazy constructor relation; each Cons applies the already-folded element clause and delays its tail. | A complete finite observation records Unit or a distinguishing Empty fibre, depth and instruction count. |
| Value universe at level zero | Identity only: native `PathUniverse` of the two indexed codes. | Native path reflexivity and certified translator replay. |
| `PathUniverse` | Identity only: the higher record of two native certificates. | Pointwise forward/backward fields and both round-trip coherence obligations, observed separately. |
| Abstract | Named interface obstruction, even for the same nominal atom. | Its declaration supplies a kind, not relation, reflexivity, transport and coherence fields. |
| Codes | Identity consumes existing `Path_U` formation; bridges are checked indexed families over two element types. | Existing certified-equivalence and transport semantics are reused, not redefined. |

**Base choice.** These built-in scalar codes are discrete; their canonical data has decidable equality. This is not a nominal-identifier test for sealed values. A different base interpretation needs an explicit relation interface. A sealed Abstract likewise needs a supplied relation, reflexivity, transport and coherence structure, with any bridge interpretation supplied separately. Looking through the seal or treating its name as equality evidence is not an alternative.

`Relation::constant` and `Relation::cases` construct heterogeneous indexed bridge families. The distinguishing witness is `Br_U Unit Bool` with fibre Unit at `((), inl ())` and Empty at `((), inr ())`. These direct first-order families require neither equality on arbitrary elements nor an equivalence. An arbitrary span needs endpoint fibres and reindexing laws before it can supply such a family. The implementation does not establish the full model laws of [Internal Parametricity, without an Interval](https://doi.org/10.1145/3632920). Bridge mode shares the code clauses but grants no automatic reflexivity or identity transport.

Identity evidence checks against its computed fibre. `reflexivity` constructs the diagonal; `compose` transports in the first-order identity fibre, pairing both product components. `transport` accepts native representable level-zero motives and reduces structural reflexivity to the exact input. An unresolved non-reflexive transport retains its endpoints, proof, motive and input as a neutral operation, not a fabricated target value. Suspended sum reflexivity is a structural diagonal program. This relation module does not provide J, arbitrary dependent motives, a general fibrancy theorem or an unrestricted universe hierarchy.

**Universe boundary.** The clause at a quoted `U₀` lowers to the existing native `Path_U`, subject to that former’s closed first-order endpoint stratum. It never interprets two code values as discrete syntax equality. Its diagonal is `PathRefl`; arbitrary evidence is checked as a native path, and code transport uses `path_universe::replay_transport`. Equal endpoint codes do not make a negation certificate reflexive: generic dependent transport stays neutral unless its proof is structural reflexivity. Generic first-order composition refuses code-level certificate composition with `CertificateOperationRequired` rather than replacing the composite by reflexivity. Explicit native certificates remain usable as evidence.

At a quoted `PathUniverse`, the same fold yields a certificate fibre. `Fibers::certificate` reuses `higher_field::unfold`, exposing the four existing obligations without deciding them. Lowering this record to a native first-order type returns `HigherFieldRequired`. This is the stopping point, not a claim of infinite coherence. Nested universe bridges, higher universe levels and an extensional conversion rule are not introduced.

**Universe choice.** Reusing the native former keeps path checking and replay authoritative; a second equivalence arena or discrete comparison would erase the certified map. **Reversal.** A broader native endpoint stratum or a checked certificate-composition language can expand the clause without changing its interpretation.

## Function identity and funext

At a thunk code, the fold records argument and result relations without comparing functions. `apply_related` checks two independently supplied arguments and their relation evidence. It crosses each `U` seam with `force`, applies the function, and relates the values returned through `F`. A variable or stuck application retains a function fibre and both application computations. It never becomes Empty because evaluation is stuck.

`HigherEvaluation` is an untrusted introduction: each component contains two claimed returned values, their `core-nbe` dialogues, and an inhabitant of the computed output relation. The kernel constructs every replay claim itself. Open component telescopes close under lambdas before replay. `function_reflexivity` replays the same function on related inputs; ordinary structural `reflexivity` requires this higher introduction at function fibres. `funext` stores raw evidence in `Identity`, and every consuming operation checks it again. Native conversion gains no function-extensionality rule.

Universal introductions cover closed functions with first-order arguments and native-representable output fibres. Coverage uses Unit, matching Sum injections, Product combinations and fresh rigid Base variables; the relation premise identifies each discrete Base pair, without sampling literals. Higher-order argument coverage and higher-order output evidence remain suspended; their quantified function fibres still form. The admitted function code is the non-dependent arrow `U (A → F B)`; dependent arrows, universe and recursive codes are outside this clause.

`transport_application` instantiates a checked function identity at an argument diagonal and computes the related returned values. Other native motives retain `Transport::Neutral`, including non-reflexive function identities. The Bool witnesses compute `not ∘ not = id` at both constructors and reject `not = id` with the failing component. Double negation uses the annotation-free, case-inlined term with its return/bind seam; the independent engine checks the direct composition too.

**Higher-evaluation cost.** Each Boolean introduction has two components and four application replays. Coverage and each replay have separate finite allowances; implicit beta steps consume replay budget even when they emit no decision. Product coverage can grow multiplicatively, so these bounds do not establish a global work theorem. Traces move into identity evidence; only a retained neutral transport clones that evidence to own its suspended computation.

**Function choice.** A lazy related-input product preserves the observational definition, including distinct related Unit arguments. Native function conversion would impose a stronger equality test; finite literal sampling would not establish the universal premise. Replaying ordinary CBPV evaluation reuses the existing trusted machine. **Reversal.** Higher-order introductions require a quantified evidence language that checks relation assumptions and nested function evidence; complete dependent funext additionally requires its substitution and fibrancy laws.

## Native fibres and admission

Computed fibres lower to the native unit (the empty product), the empty sum, binary products and universe-path types. The empty sum forms at level zero and has no constructor; its elimination is a case of no branches, which checks against any expected computation type when its scrutinee is a `Sum([])` and has no beta rule. A case of no branches has nothing to synthesize a type from, so synthesis refuses it as `EmptyCase`. The empty sum is an output fibre here, not an additional input code in the fold’s closed vocabulary. As an ordinary native leaf it remains a legitimate bounded-alias target. The fold reads the unit and binary sums and products; a product or sum of another arity is refused as an unsupported type until the fold is n-ary.

The arena handles remain scoped to their original nodes; callers must not truncate and reuse those nodes. Code folding, fibre evaluation and proof construction preserve DAG sharing with call-local tables. Those tables grant no admission capability or conversion authority. Declaration admission includes the native empty sum, finite Lists with nil, cons and pure fold, and universe paths; no receipt admits element-relation, higher-field or function-identity programs or guarded list inhabitants.

**Choice.** One code fold produces relation combinators; a shared evaluator computes both modes, while only identity carries reflexivity and transport. Separate per-mode recursions would duplicate the former clauses. Native identity syntax would couple the rule language to persistent declarations before its dependent substitution laws are checked. **Reversal.** Integrating element identity requires native syntax, scoped dependent motives and checked reduction/substitution laws; accepting Abstract requires its missing interface, not a default relation.

**Mutation scope.** The witnesses in `identity_recursion::tests` and `identity_recursion::function::tests` distinguish wrong sum branches, dropped product coordinates, negative equality on neutrals, forged identity evidence, incorrect universe classifiers, seal inspection and a malformed elimination of the empty sum. Function-specific boundaries include omitted or extra coverage, reused component dialogues, forged returned values, unchecked argument relations, bridge transport and application-motive action. No mutation score is claimed.
