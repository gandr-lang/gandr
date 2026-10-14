# gandr-theory-levitation

The first-order code universe of gandr's levitated descriptions: codes, the declaration table they populate, rule faces, circuit rules and their elaboration, multi-output arities, the generic programs driven by a description, and the host-side well-formedness pass.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** Datatypes as descriptions. A `Code<G>` is one constructor's payload in the first-order fragment `{1, var, ×, +}` with two leaf decorations: a field over a symbolic value type (`ValueTypeRef`, `PrimTy`) carrying a grade `G` and an attribute Σ (`Attrs`), and an atom-abstraction (`AtomSort`). A `SignDesc<G>` is the declaration table of one signature: its minted identity (`NominalId`), its sort set (`SortDesc`), graded parameters (`ParamDesc<G>`), constructors (`CtorDesc<G>`, the σ tag over codes), operations with multi-output arities (`OperDesc`, `BridgeArity`), rewrite faces over free terms (`RuleFace`, `FreeTerm`) and circuit rules (`CircuitRule`) whose boundary pair is derived from a wiring (`derive_boundaries`) and whose filler elaborates to a whiskered composite (`elaborate_body`). The generic programs `generic_eq`, `serialize_value` and `serialize_desc` read any description, declared or retrofitted (`bool_desc`, `option_desc`, `list_desc`, `pair_desc`, `sum_desc`); `check_desc` is the well-formedness pass; `TypedRuleFace` refines a face with a pattern context decoded by a caller-supplied decoder. The crate is `no_std` and depends on `core`, `alloc` and `quenchant-shape`.

**Why.** When a datatype's description is a first-class value, a generic operation over datatypes is an ordinary program over descriptions: structural equality, a canonical wire encoding and an inspectable rendering are written once and cover builtins and declared data alike, and the cell layer above reads one table for every declaration. The fragment is first-order so that code equality is decidable, which content addressing and the matching-modulo engines key on; a levitated universe is also an inductive object a program can recurse over, which an open universe is not.

**How.** Every recursive datum — a code, a value-type reference, a free term, a payload — is one flat table in reverse pre-order with its root apart, each subtree a contiguous range carrying its node count; a borrowed node (`CodeNode`, `TermNode`, `PayloadNode`, `ValueTypeNode`) answers a view (`CodeView`, `TermView`, `PayloadView`, `ValueTypeView`) whose children are an iterator, so every walk is a loop and nothing recurses on the host stack. Circuit-rule derivation unfolds a wiring with an explicit stack, refusing a cycle and bounding the unfolded size by an explicit `CircuitNodeBudget`. Absence is a value: a lookup that can miss returns `Maybe` with a named reason, and a refusal is a typed error.

## Provided features

- `Code`, `CodeNode`, `CodeView`, `CodeArgs`, `ValueTypeRef`, `ValueTypeNode`, `ValueTypeView`, `ValueTypeArgs`, `PrimTy`, `primitive_label`, `Attr`, `Attrs`, `AtomSort`, `Name`: the first-order code universe with decidable equality and hashing, recursion and fragment predicates, and right-nested products.
- `SignDesc`, `CtorDesc`, `ParamDesc`, `OperDesc`, `SortDesc`, `SortIndex`, `NominalId`, `DeclPolarity`, `SurfaceSpan`: the declaration table, its sort-indexed constructors and the constructor layer read as single-output arities.
- `BridgeArity`, `SortRef`: multi-output arities as bridge diagrams.
- `FreeTerm`, `TermNode`, `TermView`, `TermArgs`, `RuleFace`, `RuleVarMeta`, `Variance`, `derive_cell_var_meta`: open terms over a signature, with a results tuple at the right-hand root of a many-output operation's rule, rewrite faces, and per-variable metadata derived from a face's left-hand side.
- `CircuitRule`, `CircuitBody`, `CircuitNode`, `CircuitFrame`, `CircuitRedex`, `FrameHead`, `DerivedBoundaries`, `BoundaryReading`, `CircuitDerivationError`, `derive_boundaries`, `derive_boundaries_within`, `derive_boundary`, `derive_boundary_within`: circuit rules and the derivation of their boundary pair from a wiring, a body read out at several roots deriving a results tuple of one boundary per root.
- `RewritePort`, `PortFace`, `InterfacePair`, `PortInstantiationError`, `WhiskeredCell`, `Whisker`, `WhiskerHead`, `ActiveCell`, `active_position`, `RedexOccurrence`, `CircuitElaborationError`, `elaborate_body`, `redex_occurrences`: rewrite-sorted ports, their instantiation at a redex line, and a block's elaboration to the boundary language's whiskered composite.
- `DescValue`, `Payload`, `PayloadNode`, `PayloadView`, `PayloadArgs`, `Side`, `generic_eq`, `serialize_value`, `serialize_desc`: values of a description and the generic programs over them.
- `bool_desc`, `option_desc`, `list_desc`, `pair_desc`, `sum_desc`: the primitive formers retrofitted as descriptions.
- `sig_desc`, `SIG_CONSTRUCTORS`, `SigValue`, `SigParts`, `SigSort`, `SigOperation`, `SigPort`, `SigRule`, `SigFault`: `Sig`, the datatype whose values are presentations, a presentation's value, and its canonical bytes as the presentation's one identity.
- `check_desc`, `WfDiagnostic`, `WfKind`, `diagnostic_span`, `RESERVED_DERIVED_MARKERS`: the well-formedness pass over a whole declaration table.
- `PatternContext`, `TypedRuleFace`, `pattern_variable`: a face refined with a context decoded by the caller's decoder.
- The boundary wrappers (`NameRef`, `ConstructorTag`, `NominalSerial`, `CircuitNodeBudget`, `GenericEquality`, `SerializedValueBytes`, `LeafBytes`, …): every count, verdict, text and byte string a signature here crosses.

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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The closed tier, the integration suites, consumers, references | [`src/lib.rs`](src/lib.rs) |
| Decoding into core types | [`typed_rule`](src/typed_rule.rs) |
| Flat representation | [`tree`](src/tree.rs) |
| Code equality | [`code`](src/code.rs) |
| Circuit rules and their derived boundaries | [`circuit`](src/circuit.rs) |
| Elaborating a circuit block | [`elaborate`](src/elaborate.rs) |
| The presentation code `Sig` and what waits on the fragment | [`sig`](src/sig.rs) |
| Boundary wrappers | [`boundary`](src/boundary.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
