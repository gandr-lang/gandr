# gandr-theory-levitation

The first-order code universe of gandr's levitated descriptions: codes, the declaration table they populate, rule faces, circuit rules and their elaboration, multi-output arities, the generic programs driven by a description, and the host-side well-formedness pass.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The closed tier](#the-closed-tier)
- [Single-substitution signatures](#single-substitution-signatures)
  - [Simply-sorted evaluation and readback](#simply-sorted-evaluation-and-readback)
- [Decoding into core types](#decoding-into-core-types)
- [Flat representation](#flat-representation)
- [Code equality](#code-equality)
- [Circuit rules](#circuit-rules)
- [Boundary wrappers](#boundary-wrappers)
- [The integration suites](#the-integration-suites)
- [Consumers](#consumers)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** Datatypes as descriptions. A `Code<G>` is one constructor's payload in the first-order fragment `{1, var, ×, +}` with two leaf decorations: a field over a symbolic value type (`ValueTypeRef`, `PrimTy`) carrying a grade `G` and an attribute Σ (`Attrs`), and an atom-abstraction (`AtomSort`). A `SignDesc<G>` is the declaration table of one signature: its minted identity (`NominalId`), its sort set (`SortDesc`), graded parameters (`ParamDesc<G>`), constructors (`CtorDesc<G>`, the σ tag over codes), operations with multi-output arities (`OperDesc`, `BridgeArity`), rewrite faces over free terms (`RuleFace`, `FreeTerm`) and circuit rules (`CircuitRule`) whose boundary pair is derived from a wiring (`derive_boundaries`) and whose filler elaborates to a whiskered composite (`elaborate_body`). The generic programs `generic_eq`, `serialize_value` and `serialize_desc` read any description, declared or retrofitted (`bool_desc`, `option_desc`, `list_desc`, `pair_desc`, `sum_desc`); `check_desc` is the well-formedness pass; `TypedRuleFace` refines a face with a pattern context decoded by a caller-supplied decoder. The crate is `no_std` and depends on `core`, `alloc` and `quenchant-shape`.

**Why.** When a datatype's description is a first-class value, a generic operation over datatypes is an ordinary program over descriptions: structural equality, a canonical wire encoding and an inspectable rendering are written once and cover builtins and declared data alike, and the cell layer above reads one table for every declaration. The fragment is first-order so that code equality is decidable, which content addressing and the matching-modulo engines key on; a levitated universe is also an inductive object a program can recurse over, which an open universe is not.

**How.** Every recursive datum — a code, a value-type reference, a free term, a payload — is one flat table in reverse pre-order with its root apart, each subtree a contiguous range carrying its node count; a borrowed node (`CodeNode`, `TermNode`, `PayloadNode`, `ValueTypeNode`) answers a view (`CodeView`, `TermView`, `PayloadView`, `ValueTypeView`) whose children are an iterator, so every walk is a loop and nothing recurses on the host stack. Circuit-rule derivation unfolds a wiring with an explicit stack, refusing a cycle and bounding the unfolded size by an explicit `CircuitNodeBudget`. Absence is a value: a lookup that can miss returns `Maybe` with a named reason, and a refusal is a typed error.

## References

- James Chapman, Pierre-Évariste Dagand, Conor McBride, and Peter Morris. "The Gentle Art of Levitation." In _Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10)_, pages 3–14, September 2010. `doi:10.1145/1863543.1863547` — the universe of datatype descriptions as an inductive object, generic programs driven by a description, and the staging that keeps the meta-theory functions host-side until each moves deliberately.
- Nicola Gambino and Joachim Kock. "Polynomial Functors and Polynomial Monads." _Mathematical Proceedings of the Cambridge Philosophical Society_ 154, 1 (2013), pages 153–192. `arXiv:0906.4931` — the presentation of a polynomial by finite sets and maps, `Σ_t ∘ Π_π ∘ Δ_s`, which `BridgeArity` stores as the bridge diagram `A ←s— J —π→ I —t→ B`.
- Hayato Nasu. _Logical Aspects of Virtual Double Categories_. Preprint, January 2025. `arXiv:2501.17869` — the split cartesian fibrant virtual double category (Definition 3.2.6) and its splitness lemma (Lemma 3.2.8), whose laws the dictionary suite checks on this crate's structures, and protype isomorphisms (§ 3.2.3), the shape of the certificate suite's value translators.
- Ambrus Kaposi and Szumi Xie. "Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics." FSCD 2024. `doi:10.4230/LIPIcs.FSCD.2024.10` — second-order signatures and first-order semantics; §7 gives the eight dependent single-substitution laws.

## Provided features

- `Code`, `CodeNode`, `CodeView`, `CodeArgs`, `ValueTypeRef`, `ValueTypeNode`, `ValueTypeView`, `ValueTypeArgs`, `PrimTy`, `primitive_label`, `Attr`, `Attrs`, `AtomSort`, `Name`: the first-order code universe with decidable equality and hashing, recursion and fragment predicates, and right-nested products. Witnesses: `code::tests::product_of_folds_right_nested_with_unit_and_singleton_bases`, `code::tests::decidable_equality_distinguishes_every_variant`, `code::tests::code_is_usable_as_a_hash_map_key`, `code::tests::recursion_and_fragment_predicates_hold`, `code::tests::primitive_labels_round_trip`, `code::tests::attribute_membership_scans_markers`.
- `SignDesc`, `CtorDesc`, `ParamDesc`, `OperDesc`, `SortDesc`, `SortIndex`, `NominalId`, `DeclPolarity`, `SurfaceSpan`: the declaration table, its sort-indexed constructors and the constructor layer read as single-output arities. Witnesses: `wellformed::tests::the_sorting_discipline_indexes_the_description`, `wellformed::tests::the_constructor_layer_agrees_with_the_bridge_shape`.
- `BridgeArity`, `SortRef`: multi-output arities as bridge diagrams. Witnesses: `arity::tests::single_output_builds_a_composing_arity`, `wellformed::tests::a_non_composing_arity_is_declined`.
- `FreeTerm`, `TermNode`, `TermView`, `TermArgs`, `RuleFace`, `RuleVarMeta`, `Variance`, `derive_cell_var_meta`: open terms over a signature, rewrite faces, and per-variable metadata derived from a face's left-hand side. Witnesses: `rule::tests::free_variables_are_collected_in_order_with_repeats`, `wellformed::tests::cell_var_meta_derivation_reads_variance_and_linearity`, `tests::vdc_dictionary::law3_restriction::variance_metadata_is_invariant_under_face_action`.
- `CircuitRule`, `CircuitBody`, `CircuitNode`, `CircuitFrame`, `CircuitRedex`, `FrameHead`, `DerivedBoundaries`, `BoundaryReading`, `CircuitDerivationError`, `derive_boundaries`, `derive_boundaries_within`, `derive_boundary`, `derive_boundary_within`: circuit rules and the derivation of their boundary pair from a wiring. Witnesses: `circuit::tests::the_congruence_wiring_derives_its_boundary_pair`, `circuit::tests::a_reconvergent_wire_is_unfolded_at_each_consumption`, `circuit::tests::a_wiring_that_closes_a_cycle_derives_nothing`, `circuit::tests::a_doubling_body_declines_on_the_node_budget`.
- `RewritePort`, `PortFace`, `InterfacePair`, `PortInstantiationError`, `WhiskeredCell`, `Whisker`, `ActiveCell`, `active_position`, `RedexOccurrence`, `CircuitElaborationError`, `elaborate_body`, `redex_occurrences`: rewrite-sorted ports, their instantiation at a redex line, and a block's elaboration to the boundary language's whiskered composite. Witnesses: `elaborate::tests::instantiating_a_port_unifies_the_source_and_binds_the_target`, `elaborate::tests::an_instantiation_that_does_not_unify_declines`, `elaborate::tests::a_single_redex_block_elaborates_to_a_whiskered_cell`, `elaborate::tests::a_redex_under_two_frames_whiskers_outermost_first`, `elaborate::tests::two_disjoint_redexes_decline_with_incomparable_positions`, `elaborate::tests::a_reconvergent_redex_is_two_occurrences_of_one_rewrite`.
- `DescValue`, `Payload`, `PayloadNode`, `PayloadView`, `PayloadArgs`, `Side`, `generic_eq`, `serialize_value`, `serialize_desc`: values of a description and the generic programs over them. Witnesses: `generic::tests::generic_eq_is_description_driven_structural`, `generic::tests::generic_eq_recurses_through_var`, `generic::tests::serialization_is_deterministic_and_agrees_with_equality`, `generic::tests::desc_inspection_renders_the_structure`, `tests::code_iso::transport::generic_eq_agrees_across_every_iso`, `tests::code_iso::transport::serialize_value_is_natural_up_to_re_encoding`.
- `bool_desc`, `option_desc`, `list_desc`, `pair_desc`, `sum_desc`: the primitive formers retrofitted as descriptions. Witnesses: `builtin::tests::every_retrofit_is_well_formed`, `builtin::tests::generic_programs_cover_builtins_uniformly`, `builtin::tests::list_is_recursive`.
- `check_desc`, `WfDiagnostic`, `WfKind`, `diagnostic_span`, `RESERVED_DERIVED_MARKERS`: the well-formedness pass over a whole declaration table. Witnesses: `wellformed::tests::a_clean_description_passes`, `wellformed::tests::an_out_of_signature_cell_is_declined`, `wellformed::tests::a_fresh_right_hand_side_variable_is_declined`, `wellformed::tests::a_boundary_mismatched_circuit_rule_is_declined`, `wellformed::tests::a_redex_applying_an_undeclared_port_is_declined`, `wellformed::tests::declaring_derived_metadata_is_declined`.
- `PatternContext`, `TypedRuleFace`, `pattern_variable`: a face refined with a context decoded by the caller's decoder. Witnesses: `typed_rule::tests::signature_context_decodes_field_codes`, `typed_rule::tests::typed_face_context_totality_tracks_declared_variables`, `typed_rule::tests::signature_context_propagates_decode_failure`.
- The boundary wrappers (`NameRef`, `ConstructorTag`, `NominalSerial`, `CircuitNodeBudget`, `GenericEquality`, `SerializedValueBytes`, `LeafBytes`, …): every count, verdict, text and byte string a signature here crosses. Witness: `tests::workspace::the_crate_depends_on_no_other_workspace_crate`.

## Expected features

- **A grade vocabulary.** A field's grade is the type parameter `G` of `Code`, `CtorDesc`, `ParamDesc` and `SignDesc`; the consumer that owns grades supplies it. The generic programs and `check_desc` never inspect it.
- **A decoder.** `PatternContext::from_field_codes` takes the function that decodes a field code into the consumer's type universe, and propagates its refusal.

## Examples

Compare and encode two values of the retrofitted `Boolean`, which carries no field, so any grade type serves.

```rust
use gandr_theory_levitation::ConstructorTag;
use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::Payload;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::bool_desc;
use gandr_theory_levitation::check_desc;
use gandr_theory_levitation::generic_eq;
use gandr_theory_levitation::serialize_value;

let boolean: SignDesc<()> = bool_desc();
assert!(check_desc(&boolean).is_empty());
let false_value = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
let true_value = DescValue::new(ConstructorTag::from(1_usize), Payload::unit());
assert!(!bool::from(generic_eq(&boolean, &false_value, &true_value)));
assert_ne!(
    serialize_value(&boolean, &false_value),
    serialize_value(&boolean, &true_value)
);
```

Derive the boundary pair of the congruence rule `cong2`, whose two redexes sit under one `add` frame.

```rust
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitDerivationError;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::CircuitRedex;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::derive_boundaries;

fn example() -> Result<(), CircuitDerivationError> {
    // node : p(x) ==> (x2); node : q(y) ==> (y2); node : add(x2, y2) --> (z);
    let body = CircuitBody::new(
        [
            CircuitNode::Redex(CircuitRedex::new("p", FreeTerm::var("x"), FreeTerm::var("x2"), "x2")),
            CircuitNode::Redex(CircuitRedex::new("q", FreeTerm::var("y"), FreeTerm::var("y2"), "y2")),
            CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("add".into()),
                [FreeTerm::var("x2"), FreeTerm::var("y2")],
                "z",
            )),
        ],
        "z",
    );
    let derived = derive_boundaries(&body)?;
    assert_eq!(derived.source, FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("y")]));
    assert_eq!(derived.target, FreeTerm::op("add", [FreeTerm::var("x2"), FreeTerm::var("y2")]));
    Ok(())
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-levitation
```

## The closed tier

The crate has no dependency on another workspace crate. The field leaf is the one place a core notion meets the code universe: it carries a grade `G` supplied by its consumer, while its value type stays this crate's symbolic `ValueTypeRef`. Generic programs, arity naming and rendering read that description. The crate is `no_std`.

- **Alternatives.** Depending on the core term crate for its grade and value types puts a core edge under a theory crate, inverting the layering, and lets a dependent reach that crate through re-exported wrappers. A whole-leaf parameter `Field(L)` would lose `PrimTy` and the symbolic value type that operation arities, the inspection rendering and the leaf-shift certificate read. A trait declared here and implemented in the core tier is an abstraction with one implementation.
- **Reversal.** A reordering of the categories that puts the core tier below the theory tier returns the field leaf to the core's own grade and value types.

## Single-substitution signatures

A `SortDesc` is ordinary or representable. A `SortRef` carries its index arguments and a flat, outermost-first `pi_plus` telescope. `check_desc` rejects a binding domain that is undeclared or not representable. This is restricted object-language binding, not the atom abstraction `Code::Bind`.

`first_order` folds sort, operation and equation declarations once into a single-substitution presentation. It adds contexts and a pointed substitution graph, substitution actions, and extension, weakening, newest-variable, single-substitution and lifting operations for representable families. Operation naturality lifts substitution under every binder. It adds no substitution identity, composition or empty substitution. Constructor payloads, circuit rules, external parameters, reserved `$` names and non-product arities are refused. Index expressions must already be well-typed; the description checker is not a dependent type checker. Equation notation leaves context and index parameters implicit, while operation telescopes display them. Existing equation faces retain their implicit source context; this is not an elaborator for arbitrary second-order equations.

The generation witness derives the unindexed lambda binding signature from the paper's Definition 4 and §§6–7. The four index laws are vacuous for `Tm : Type+`; four term laws and naturality for `lam` and `app` remain. A separate indexed `Ty/Tm` fixture checks all eight printed laws. The paper does not print an SSC table for pure lambda calculus; source beta equations are not part of this binding-signature experiment.

### Simply-sorted evaluation and readback

`SimplySorted::new` adds admission beside `check_desc`, sharing the operation-signature validator with `first_order`. Every sort must be unindexed; `AdmissionError::TermDependentSort` retains the rejected sort's name. Index arguments on simple sort occurrences and binding result ports are also refused. Any finite number of sorts, operations, arguments and representable binder domains is supported, including ordinary result sorts and empty signatures.

`BindingTerm` is the free finite binding carrier derived from those declarations. `SimplySorted::evaluate` interprets it in an identity environment; `evaluate_in` accepts a sorted environment of arbitrary term images. One implementation handles every admitted signature. Operations retain argument bodies and captured environments as flat, defunctionalized closures. Readback opens each closure under its declared telescope, reflecting fresh levels. Levels preserve captured values under weakening; environment extension appends the newest image. Readback is always uncached and releases its temporary arena entries after each call.

`BindingJudgement` and `FirstOrderJudgement` retain ambient context order and result sort. Their equality is canonical structural equality **at a fixed signature**, independent of allocation IDs. `to_first_order` and `from_first_order` identify binding trees with typed canonical `q`/`p` representatives of the generated SSC presentation. Environments use a chosen empty/extension isomorphism: a flat arena entry dereferences to a prefix/value pair. This is not raw-handle identity or definitional equality of representations. Semantic equality is observed by typed, uncached readback.

| Witness | Scope |
| ------- | ----- |
| `tests::glf::model::three_signatures` | LC; value/computation sorts with an argument-local binder; two representable sorts with unequal mixed telescopes. Independent first-order and binding goldens, both composites, 256 generated cases per signature, open contexts and repeated uncached readback. |
| `tests::glf::model::substitution_laws` | Single-substitution cancellation, newest-variable laws, weakening/lifting commutation and a nonidentity environment under mixed binders. Re-evaluation of a substituted semantic value checks the other identification direction. |
| `tests::glf::model::admission` | Named dependent-sort refusal and admitted/refused signature boundaries. |
| `tests::glf::model::typing_boundaries` | Sort, scope, arity and environment refusals; canonical first-order admission; typing-sensitive equality. |
| `tests::glf::model::deep_uncached_binders` | An open variable beneath 4,096 binders, without recursive traversal or ownership. |

The first-order view is the signature-generated presentation, not an adapter to the fixed core calculus. The construction covers the free binding syntax of simply-sorted signatures. Source equations are not oriented or normalized; arbitrary explicit-substitution expressions are outside the canonical identification maps. Term-dependent telescopes, second-order equation elaboration, a surface `sign` route, stage universes and extension types are outside this result. Finite witnesses support the identification; they do not prove a general equivalence of models.

- **Choice.** Flat syntax trees and persistent flat environments keep ownership and traversal nonrecursive, share captured prefixes and avoid per-signature code. Operation lookup scans the signature; variable lookup follows its environment prefix. No new dependency or quotation cache is required.
- **Alternatives.** Host closures obscure captured data and lifetime boundaries; boxed syntax recurses on destruction. Per-signature core adapters establish only their selected interpretations. Atom abstraction describes nominal binding, not representable context extension. The generic binding treatment follows [Allais, Atkey, Chapman, McBride and McKinna, *A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs* (2021)](https://arxiv.org/abs/2001.11001).
- **Reversal.** A dependent telescope requires typed index semantics before admission expands. Measured lookup cost can justify compiled operation indices or indexed environments without changing typed structural equality. General equation normalization needs a separately justified reduction or certificate interpretation.

## Decoding into core types

Decoding is the large elimination from a code over the first-order fragment into the core value-type universe: `1` to the unit type, a product to a pair, a sum to a coproduct, a field to its value type with its grade and attributes erased, and a recursive occurrence at the description's own sort to the carrier of the type being defined; a whole description decodes to the coproduct over its constructors. Its target is a core type, so it lives with the consumer that owns that universe — the core side of the surface's description route, which lowers `data`, `codata` and `sign` declarations into this table, checks them with `check_desc`, and decodes them. This crate provides the seam: `PatternContext::from_field_codes` and `TypedRuleFace` take the decoded type as their parameter and the decoder as an argument.

## Flat representation

No datum here owns its way back to itself. A code, a value-type reference, a free term and a payload are each one flat table: the nodes below the root in reverse pre-order, then the root, every node carrying its subtree's node count, so a child is found by skipping its elder siblings and a subtree is one contiguous slice. Equality and hashing are derived over the table, and the layout is canonical, so they are structural. Building an application concatenates its arguments' tables. A whiskered composite is a list of whiskers outermost first around its active cell.

- **Alternatives.** Boxed children are recursive owned pointers, which the workspace denies: a deep term overflows the stack on drop. One arena shared by every description couples a value to the arena's lifetime and gives equal values one identity before anything sanctions it.
- **Reversal.** A measured cost from copying tables when building applications moves the representation to a shared arena, with the identity question answered first.

## Code equality

The fragment is first-order so that code equality is decidable, and `Code` derives total structural equality and hashing over its flat table. Two descriptions with equal tables are the same description; a grammar change admitting a higher-order code would break that, which is why the exclusion is a fragment boundary rather than a deferral. Content addressing is a consumer's map keyed on `Code`: the crate ships no interner, because a map over the derived `Eq` and `Hash` is all one needs (`code::tests::code_is_usable_as_a_hash_map_key`).

Code equality is not the identity of a translation between descriptions. Two auto-isomorphisms of `Boolean`, the identity and negation, have equal boundary codes and different behaviour; the certificate suite keeps that apart (see [The integration suites](#the-integration-suites)).

## Circuit rules

A circuit rule's boundary pair is derived, never written: the source is the wiring with every redex replaced by its source, the target with every redex replaced by its target. The declared sphere stays the declaration's, and `check_desc` compares the derived pair against it, so a mis-glued boundary is refused at the declaration table. Derivation unfolds each port once per consumption, so a reconvergent wire is copied into each reading; the unfolded size is bounded by `CircuitNodeBudget` (default 4,096 nodes per reading), and a wiring that closes a cycle is refused by the port that closes it. `derive_boundaries_within` and `derive_boundary_within` take an explicit budget.

A rewrite-sorted port binds the interface pair a hole carries; instantiating it at a redex line unifies its source with the line's input wiring and binds its target. A block with one redex elaborates to that redex inside its frames, outermost first; a block with none is the identity rewrite at the term it builds; a block with two incomparable redexes is declined, and `redex_occurrences` reports the positions so the cell layer can ask the interchange question at an application.

## Boundary wrappers

Every count, index, verdict, text and byte string a signature here crosses is a transparent wrapper of this crate's own (`ConstructorTag`, `NominalSerial`, `SurfaceByteOffset`, `MonomialCount`, `TermPositionIndex`, `PortArgumentCount`, `CircuitNodeBudget`, `GenericEquality`, `RecursiveStatus`, `ContextTotality`, `DiagnosticMessage`, `SerializedDescText`, `SerializedValueBytes`, `LeafBytes`, …), converting with `From` both ways, and `NameRef` is the borrowed name. A consumer keeps its own budgets and verdicts; a wrapper two crates exchange by value lives in the lower one, which is this crate for every wrapper listed.

## The integration suites

Two suites check the crate against the laws its consumers rely on, with the machinery the crate leaves to them supplied as test support.

- **Certificates** (`tests::code_iso`). A certificate is a pair of value translators between two monomorphic descriptions, judged by replaying its round trips against `generic_eq`; its identity is replay-equivalence, the shape of a protype isomorphism. Identity, inverse and composition form a groupoid up to replay, and `generic_eq`, `serialize_value` and a content-addressed code table transport across every certificate. Two guards stand: negation and the identity share their boundary codes yet replay differently, so the identity of certificates is never code equality; and over a one-constructor description with an unbounded `Integer` leaf, the successor shift is a valid certificate distinct from the only structural one, so a completeness claim about certificates ranges over translators uniform in leaf contents.
- **The virtual double category dictionary** (`tests::vdc_dictionary`). Objects are tuples of real descriptions, tight arrows renamings of real symbols checked against their real codes and arities, and restriction recomputes real faces. The tight category holds strictly; cell composition and the cartesian structure hold up to replay; restriction holds in the split form by construction, with the face action split on `RuleFace` itself; units hold β on `refl`, and path induction declines on a non-empty path, which locates an obligation on a cell store: instances closed under path action. The matcher, substitution, rewriter and signature morphism the suite uses are test support; the crate ships none of them (`tests::vdc_dictionary::law3_restriction::matching_and_substitution_are_supplied_test_side`, `tests::vdc_dictionary::law1_tight::check_morphism_accepts_a_role_matched_renaming`).

Executable specifications check structural relationships, ordering and multiplicity, variable provenance, budget refusal and encoding layout. Each nontrivial item's `# Adequacy` names the observations, defect classes, evidence rung and boundary its witnesses establish. Contracts also cover the certificate and dictionary harnesses: their composition, substitution and refusal paths must not silently weaken the laws they test. Const extent arithmetic checks its primitive fields directly, with constant-evaluation and runtime boundary witnesses. Opaque-iterator items document the instrumentation boundary; formatting documents its write-only sink. A predicate over an observable projection does not claim the unobservable remainder of a contract.

Test prose names items plainly: the suites carry no intra-doc links, which rustdoc does not check in a test target.

## Consumers

The cell layer reads the declaration table, its operations' arities, its rule faces and its circuit rules: it elaborates a description into cells and instantiates circuit rules at an application, through `SignDesc`, `OperDesc`, `BridgeArity`, `DeclPolarity`, `RuleFace`, `FreeTerm`, `CircuitRule`, `CircuitBody`, `WhiskeredCell`, `RedexOccurrence`, `elaborate_body`, `redex_occurrences` and `derive_boundaries`. The surface's description route lowers declarations into the table, runs `check_desc`, and decodes codes into core types on its core side.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
