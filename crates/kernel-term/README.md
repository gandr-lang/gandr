# gandr-kernel-term

The kernel's term arena and sharing format: a flat, id-addressed arena, the unified subterm-table encoding over it, canonical decode, and the decode-time budgets that bound the work a small artifact can cost.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Canonical form by re-encoding](#canonical-form-by-re-encoding)
- [Amplification budgets](#amplification-budgets)
- [Admission watermark](#admission-watermark)
- [Rejection vocabulary](#rejection-vocabulary)
- [Structured names](#structured-names)
- [Universe families and quotes](#universe-families-and-quotes)
- [Static operators](#static-operators)
- [Tag numbering and versioning](#tag-numbering-and-versioning)
- [Sharing and compression](#sharing-and-compression)
- [Specification attributes](#specification-attributes)
- [Experimental stage syntax](#experimental-stage-syntax)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `TermArena` holds the kernel's terms and types in four typed id families: values, computations, value types and computation types. `encode` writes an arena and a sequence of marked declarations as one canonical artifact; `decode` reads an artifact back into a fresh arena, refusing anything malformed, non-canonical or over budget with a typed `DecodeError`. The crate holds representation and bytes only: the checker, conversion, the environment and the admission choke point live in `gandr-kernel-core` and consume this vocabulary. It is `no_std` over `core` and `alloc` and depends on `gandr-kernel-strata` alone among workspace crates.

**Why.** A kernel that checks large proofs needs shared subterms to stay shared from the bytes to the checker, or every reference to a shared subterm costs its full size again. Retaining that sharing is also an attack surface: a small artifact can name a DAG whose tree-expanded size is astronomical, so a reader must bound expanded work before anything downstream sees the artifact, without trusting the writer.

**How.** Four decisions interlock. The representation is an arena of `Copy` ids, so a graph of shared ids is representable at all and teardown is a flat vector drop rather than a recursion over term depth. The format is one per-artifact tagged subterm table over all four families in a single index space, maximally shared under structural equality, declaration-segmented, with children referenced only by strictly earlier index in post-order first-completion order. Decode retains sharing, which the arena makes possible: a table entry is an arena id, and decode is arena construction. Because decode retains sharing, a single forward scan over memoized saturating sizes bounds the expanded work before any consumer runs. Owned trees would foreclose the format, which is why the four are decided together.

## References

- Simon L. Peyton Jones. _The Implementation of Functional Programming Languages_. Prentice Hall, 1987. `isbn:978-0134533339` — the graph representation and maximal sharing this format's stored plane realizes statically.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4 builds the hash-consed subterm DAG as a pre-pass; this format hands a consumer that DAG already built, so transcription is a pass over a table.

## Provided features

- **A flat arena in four typed id families** (`ValueId`, `ComputationId`, `ValueTypeId`, `CompTypeId`) where a node's children are `Copy` ids. Constructors require children already allocated in the same arena; same-family children precede their parent while the family length fits `u32`. Lookup checks the family index, not arena provenance. Truncation permits index reuse, and minting saturates the returned index at the `u32` ceiling. Derived equality, hashing and debug output are shallow.
- **The admission watermark** (`ArenaWatermark`): a snapshot of the four family lengths, truncation back to one, and the clamp a rollback needs when staging order differs from admission order. `DeclarationBuilder` ties content minting to it.
- **The unified subterm table**: `encode` and `decode` over `EncodedArtifact` and `ArtifactImage`, with `DecodedArtifact` holding the arena and its `MarkedDeclaration` sequence. Polarity is recoverable from the tag alone, so a child slot's requirement is a table lookup.
- **The segment layout** (`SegmentLayout`, `ByteOffset`): where a decode found the header's end and each declaration segment's end, so a consumer storing the segments apart takes the boundaries from the reader rather than from the writer.
- **Structured names** (`StructuredName`, `NameSegment`): each declaration's name record, a list of segments that `Declaration::named` attaches and the format carries, described in [Structured names](#structured-names).
- **Canonical form enforced by re-encoding**, described in [Canonical form by re-encoding](#canonical-form-by-re-encoding).
- **The amplification defence**: `MAX_TABLE_ENTRIES`, `MAX_EXPANDED_TERM_WORK`, `MAX_ARTIFACT_EXPANDED_WORK` and `MAX_DECODED_LEVEL_OFFSET`, enforced during decode, and `DecodeMetrics`, the deterministic measurements the same scan yields for a caller to record.
- **The node-tag table** (`NODE_TAG_TABLE`): a const protocol input with one row per frozen tag, giving its child arity, its token bound and its two storage-boundary verdicts. A differential pins its arities against the arena's own child relation.

## Expected features

- **Admission by the consumer.** Decoding checks format, canonicality and budgets, never typing. A decoded declaration is trusted only after an admission choke point (`gandr-kernel-core`) re-checks it.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

Consumers reach the crate through the kernel; a direct round trip builds a declaration, encodes it and decodes it.

```rust
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;

fn example() {
    let mut arena = TermArena::new();
    let declared = arena.value_type_unit();
    let unit = arena.value_unit();
    let body = arena.value_pair(unit, unit);
    let builder = DeclarationBuilder::new(&mut arena);
    let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
    let sequence = [MarkedDeclaration::new(AdmissionMark::Checked, declaration)];

    let bytes = encode(&arena, &sequence);
    let artifact = decode(bytes.as_image()).expect("the artifact is canonical");
    assert_eq!(1, artifact.declarations().len());
}
```

`tests/sharing_format.rs` carries the rejection suite: the sharing round trip with sharing asserted at the shared nodes, sharing determinism over two differently shared equal inputs, the canonical-form refusals, the amplification goldens, the boundary goldens derived from the constants, and the version refusal. `tests/adversarial_depth.rs` decodes and drops the deepest artifact the kernel round-trips inside a small-stack thread. Run them, then the enforcing twin:

```sh
cargo nextest run -p gandr-kernel-term
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-term
```

## Canonical form by re-encoding

The encoder is untrusted and feeds no judgement. The reader enforces canonical form by re-encoding the whole decoded artifact and comparing bytes, and the maximal-sharing encoder is the re-encoder. One mechanism therefore catches a redundant duplicate entry, a mis-ordered table and a dead entry. The re-encoder is itself sharing-aware; a tree-walking re-encoder would turn the canonical check into an amplification vector.

Canonical bytes are a function of the declarations' abstract content, never of how they were built or decoded, so two differently shared equal inputs encode identically.

## Amplification budgets

Each budget bounds one axis and is enforced where it is cheapest:

| budget | axis | enforced |
| ------ | ---- | -------- |
| `MAX_TABLE_ENTRIES` | distinct graph nodes | as entries accrue |
| `MAX_EXPANDED_TERM_WORK` | tree work per declaration root | on the forward scan |
| `MAX_ARTIFACT_EXPANDED_WORK` | tree work over the whole artifact | on the same scan, one extra accumulator |
| `MAX_DECODED_LEVEL_OFFSET` | a level atom's successor offset | at the level decoder, per atom |

An entry's expanded size is one plus the saturating sum of its children's. Children are strictly earlier, so one forward scan computes every size in linear time. The artifact-total cap exists because many small declaration segments referencing one near-cap root pass the per-declaration cap individually while forcing many times its work together.

The budgets bound work without touching the checker, so they stay outside the trusted base, and they are reader acceptance policy only: they change neither the wire format nor canonicality. The constants are set against the deepest artifact the kernel itself round-trips, the adversarial-depth witness, and clear it with headroom while refusing an obvious billion-laughs artifact by orders of magnitude.

## Admission watermark

A choke point takes an `ArenaWatermark` before staging a declaration and truncates after the verdict, on rejection and on success alike. `DeclarationBuilder` records its own mark and truncates each family to `min(current_len, content_start)` when abandoned. Its mutable arena borrow also permits shrinking and reminting below that mark: abandonment preserves those leading nodes rather than restoring an earlier snapshot. A `Declaration` carries no watermark: decode builds one table for the whole artifact, so a decoded declaration has no meaningful content-start mark.

The mark stores lengths rather than copied nodes, keeping truncation allocation-free. Snapshot restoration would require retaining overwritten content; revisit that choice only if staging must restore arbitrary edits rather than discard an appended suffix. `TermArena::truncate_to` with a stale watermark past a family's end leaves that family unchanged.

## Rejection vocabulary

A decode failure is a format failure and never a typing failure. `DecodeError` is a rejection triple — truncation, an unknown tag at a named `TagSite`, a violated structural invariant at a named `MalformedSite` — plus two by-name refusals for the reserved parts of the format and a version refusal that names the version it met.

`ReservedKind` names the declaration kinds a module layer would export (`ModuleSig`, `ModuleDef`, `FunctorDef`); they are reserved together so graduating one into the kernel never renumbers a shipped format, and a live kind such as the abstract type has no variant. `ReservedSlot` names the slots and sections that must be empty, and the minted-atom table, the one live member, refused when the declarations decoded beside it refute it.

## Structured names

**Choice.** A declaration carries a `StructuredName`: a list of `NameSegment`s, outermost first, written in the segment's name record as a count and then each segment's length-prefixed UTF-8. A segment never holds `.`. `NameSegment::from_text` is the only constructor and refuses the separator, so the encoder's input cannot carry one and the encoder stays total; the decoder rebuilds every segment through the same constructor and refuses a dotted or non-UTF-8 segment as `MalformedSite::NameSegment`. A finisher builds an unnamed declaration, and a producer names it afterwards with `Declaration::named`, so no finisher's signature changed. The name is identity for a reader and is never read by a check: a reference is a `ConstantIndex`, the admission position of what it names, so renaming a sequence leaves every content root and the arena unchanged.

**Alternatives.** One dotted string per declaration would make the namespace's spelling the exported identity, and two different segment lists would collide on one string. Keeping the record reserved and naming declarations in a side table would leave an artifact unreadable without that table. A fallible `encode` refusing the separator would make every caller handle a refusal its input type can rule out.

**Reversal.** If a renamed module must export a byte-identical artifact, the names move to a side table and the record is pinned empty again. If a segment needs to carry `.` — a foreign namespace whose names hold it — the segment gains an escape in its text field, which changes the field's shape and bumps `FORMAT_VERSION`. The record itself is framed in every declaration segment and an unnamed declaration writes a zero count, so naming declarations changes no byte of an unnamed sequence's artifact.

## Universe families and quotes

**Choice.** Universes come in two families, one per ground sort: `ValueType::Universe { sort, level }` with `GroundSort::Value` classifies value types at `level` and with `GroundSort::Computation` classifies computation types at `level`. Both are value types one level up — a code is a value whatever family it decodes into. A code is a quote, `Value::Quote` of a value type or `Value::QuoteComputation` of a computation type, and a type is read off a code by the decoding former of its family, `ValueType::Element` or `CompType::Element`.

**Decode on mint.** `TermArena::value_type_element` over a value quote returns the quoted type and mints nothing, and `comp_type_element` does the same over a computation quote. The decoding rule `El ⌜A⌝ = A` therefore fires at the one place a decode is made, so no arena holds the redex, and no artifact either: a table writing a decode over a quote reads back as the quoted type, and the re-encoding check refuses it as non-canonical. A decode across the families — a computation decode of a value quote — is minted as written, for the checker to refuse as a type mismatch. The alternative, a decode node the checker reduces, would put a redex in front of every conversion and every walk; the reversal condition is a decoding rule that needs a context to fire, which a constructor cannot see.

**Alternatives.** One universe over both sorts was rejected because a value type and a computation type are different kinds of thing in call-by-push-value, and a single universe would need a sort test at every decode. A sort parameter on the universe is the surface's business: no sort parameter reaches this crate, so `GroundSort` has exactly the two ground sorts.

## Static operators

**Choice.** A type operator is classified by `ValueType::StaticPi { domain, codomain }` and eliminated by `Value::StaticApplication(head, argument)`. The static Pi is non-dependent: its codomain stands in the ambient context and the former binds nothing. The kernel has no static lambda. An operator's body is an elaborator-side definition; what reaches an admitted declaration is its static normal form, where every application of a defined operator has been reduced away and a remaining static application is neutral — headed by a variable or an opaque constant. A δβ-step a certificate replays hands the kernel the operator's body with its binders stripped (see the conversion replay in `gandr-kernel-core`), so no node in this arena ever binds a static parameter.

**Alternatives.** A static lambda former would make every static redex a kernel concern: the checker would owe a β-rule at values, conversion would owe it too, and the trusted base would grow by a reduction the elaborator already performs and certifies. A dependent static Pi was not needed: no former indexed by a code is applied to a static argument at this vocabulary.

**Reversal.** A static lambda former arrives when a declaration must carry an operator itself rather than its instances — an operator exported across a module boundary whose instances the importer forms.

## Tag numbering and versioning

The tag space is one disjoint enumeration over four families. The allocation and reservation table in [`tags`](src/tags.rs) is authoritative; `NODE_TAG_TABLE` supplies the assigned formers and their arities. Empty, absurd and native paths have distinct bytes. Higher fields and function identity remain in-memory rule languages, with reserved ranges and no wire nodes.

The original `0x00–0x1F` meanings are frozen, including static operators at `0x1E–0x1F`. The extension and reservation table covers the remaining bytes:

| Byte or range | Meaning | Artifact reader |
| ------------- | ------- | --------------- |
| `0x00–0x1F` | Original formers in `NODE_TAG_TABLE` | Admitted, unchanged |
| `0x20` | Reserved value sharing | Refused |
| `0x21` | Reserved computation sharing | Refused |
| `0x22` | Reserved value-type sharing | Refused |
| `0x23` | Reserved computation-type sharing | Refused |
| `0x24–0x27` | Held weakening slots | Refused |
| `0x28` | Empty value type, no children | Admitted |
| `0x29` | Absurd computation, one value child | Admitted |
| `0x2A` | `Path_U`, two value-code children | Admitted |
| `0x2B` | Path reflexivity, one code child | Admitted |
| `0x2C` | Equivalence, evidence and three children | Admitted |
| `0x2D` | Product path, two path children | Admitted |
| `0x2E` | Transport, path and input children | Admitted |
| `0x2F` | Unassigned | Refused |
| `0x30–0x37` | Higher-field reservation | Refused |
| `0x38–0x47` | Funext reservation | Refused |
| `0x48–0x4F` | `Flow_U` reservation | Refused |
| `0x50` | List code, one element-type child | Admitted |
| `0x51` | Reserved List inhabitant | Refused |
| `0x52` | Session code, inline finite graph and one payload-type child | Admitted |
| `0x53–0x59` | Inline send, receive, select, offer, end, Mu and Var opcodes | Graph fields only; refused as native node tags |
| `0x5A` | Session Path evidence, classifier and payload-proof children | Admitted |
| `0x5B–0xFF` | Unassigned | Refused |

The admitted domain is sparse: the greatest assigned native byte is `0x5A`, not a promise to accept every smaller byte. Boundary witnesses admit session tags, refuse inline opcodes as native nodes, and retain the frozen block. Empty is a zero-child leaf and may be a bounded-alias target; no reservation becomes an alias target by being below the maximum.

The sharing block is reserved: `NODE_SHARE_VALUE`, `NODE_SHARE_COMPUTATION`, `NODE_SHARE_VALUE_TYPE` and `NODE_SHARE_COMP_TYPE` name its per-family bytes, and no entry carries one. A reader meeting one of its bytes refuses it by name at the node site, exactly as it refuses any other unassigned byte. Reserving the block keeps the core vocabulary from growing into it: the core resumes above `SHARING_BLOCK_LAST`, and the block stays contiguous, so a sharing former's family is a subtraction.

Assigning an unassigned tag or kind byte, or filling a reserved slot that is framed from the start, holds `FORMAT_VERSION`: the reader is a closed-vocabulary parser, so an unknown byte is a named refusal rather than a mis-parse. Reassigning a byte or changing a field's shape, order or width bumps it, because an older reader would otherwise parse successfully and wrongly.

`PathUniverse` has two value-code children; reflexivity has one code, product paths have two paths, and transport has a path and input value. `PathEquiv` carries inline portable evidence followed by its classifier, forward map and backward map children. Evidence is source then target: a dialogue count, then each dialogue's decision count and unsigned decision words. Unknown words and oversized negative-premise positions are malformed; decoding never certifies a round trip.

The portable decision alphabet comes from `kernel-conversion-trace`; unit anchors carry no arena identity. Reusing that vocabulary avoids a second replay protocol. The sharing-format witness preserves all decisions, empty dialogues and direction boundaries against independent bytes, and rejects malformed words and truncated prefixes. **Reversal:** introduce a new framing version if the alphabet needs payloads that cannot be encoded without changing existing word meanings.

The List code (`NODE_VT_LIST`, `0x50`) has one value-type child, its element code. It represents the strictly positive fixed point `μX. Unit + A × X` without a back edge in the type arena. Its finite code round-trips through the ordinary sharing format. `NODE_LIST_VALUE_RESERVED` (`0x51`) remains unassigned: guarded list inhabitants are in-memory kernel observations, not persisted term values.

Session codes use `NODE_VT_SESSION` (`0x52`). Their inline graph stores a root, node count, and finite nodes tagged send `0x53`, receive `0x54`, select `0x55`, offer `0x56`, end `0x57`, binder `0x58` and variable `0x59`. Graph integers are canonical unsigned varints. A label is its byte count followed by its exact UTF-8 bytes, each encoded as an unsigned varint. Choice maps are in label order. The graph's only native child is a right-associated payload-type product ending in Unit; payload slots index its fields. Internal recursion references finite graph positions, never a native type-arena back edge.

`NODE_V_SESSION_PATH` (`0x5A`) has two native children: its `Path_U` classifier and a Unit-terminated product of native payload-path values. Inline evidence is a sorted set of source/target state pairs followed by ordered source/target payload-slot obligations. Decoding rejects unknown opcodes, malformed UTF-8, duplicate labels or relation pairs, truncation and noncanonical encodings. Counts consume input before growing allocations; exhausted input is `Truncated`, while the ordinary table and expanded-work budgets retain their typed refusals. Contractivity, scope, relation coverage and payload typing belong to kernel formation. All relation data participates in canonical bytes even when conversion erases derivation pairs.

**Choice.** Inline finite graph data with one native payload-code child preserves the format's fixed child arities and ordinary content sharing without recursive Rust ownership. Separate native constructors would spread finite graph framing across seven additional native cases; a second opaque payload-identity scheme would bypass universe formation. **Reversal.** A distinct protocol universe or a persisted endpoint-value language requires its own formation and elimination rules. These tags encode protocol types and identity evidence, not live channels.

## Sharing and compression

Arena allocation does not intern nodes. Encoding does: child-first entry bytes are content keys shared across declaration segments, so separately allocated equal subgraphs can become one wire entry. Decoding preserves the sharing of the accepted canonical table in an owned, flat arena. Equal ids identify one node; distinct ids do not establish semantic inequality. This format interning is not an evaluation memo or a proof of typing or admission.

Compression is a storage and transport concern. The canonical bytes are the bytes, and no codec sits inside a reader whose rejection vocabulary has to stay clean. The bytes are declaration-segmented and self-delimiting.

## Specification attributes

Clause-bearing items carry executable `#[spec(...)]` predicates or a local `executable: none` explanation, with `# Adequacy` linking their evidence. Checks observe decimal normalization, arena prefix frames, declaration lifecycle and metadata, exact wire fields, borrowed cursor ranges, typed refusals and budget precedence. Const predicates compare inner ordinals without adding a second identity vocabulary. A predicate checks its stated projection on an executed call; it does not turn a transported producer claim into admission evidence.

Encoding requires live, acyclic reachable graphs and an interner used with the unchanged arena it addresses. Enforced predicates reject stale roots. Treating a missing computation or computation type as a unit is not a valid alternative: those families have no unit former. A fallible recovery API would be a separate design, not a fabricated wire fallback. Arena ids carry neither provenance nor a reuse generation; a coincident ordinal alone cannot establish origin.

Literal byte fixtures independently pin every former, payload and child position. Decoder witnesses vary every tag byte, proper prefixes, reference order and polarity, normalization residues and the arithmetic ceilings. Local normalization is not canonical-wire acceptance: decoding also compares the whole artifact with its re-encoding. That agreement check is not an independent format oracle. Budget witnesses use explicit expansion and widened arithmetic; the integration diamond model saturates the final tree size, including the exact `u64::MAX` boundary, rather than saturating a power before subtraction.

The deep-graph witness walks 100,000 thunk-over-returner links to unit and drops the sole decoded owner on a 256 KiB stack. An entry count alone cannot prove depth. This is evidence for that shape and stack bound, not all graph shapes or allocation failures. Formatter effects, non-callable data and policy constants, the consuming builder-discard boundary and an opaque test strategy state their unobservable obligations and witnesses at their definitions.

## Experimental stage syntax

`stage::Arena` is a separate, append-only rule-language arena for
[hypothesis-indexed staging](../kernel-core/README.md#experimental-stage-universe).
It holds indexed classifiers, terms and untrusted conversion certificates. Both classifiers and terms are interned by exact syntactic equality after child-liveness checks. Within one arena, equal term ids mean equal constructors, payloads, classifiers and children; ids from different arenas are not comparable. Cloning preserves the complete namespace. This is syntax identity, not conversion authority. De Bruijn substitution uses an explicit worklist and raises replacements under binders; its unchanged-constructor fast path avoids an unnecessary lookup. There is no staging wire format and no allocated wire tag.

Each family interns through an open-addressed, linearly probed table kept at most half full. A slot holds a descriptor's dense position and a 32-bit hash of it; the dense vector owns the descriptors, so a probe confirms every hash match by comparing the descriptor itself, and a collision costs a comparison, never an identity. The hash is an unkeyed fold of the descriptor's derived `Hash`, a function of the descriptor alone. A coordinate is the descriptor's allocation position; the table only finds it. A clone copies each family's descriptor and slot vectors with no per-entry allocation. Positions are 32 bits wide, so allocating past `u32::MAX` descriptors of one family refuses with `Overflow`.

**Choice.** A hand-written table on `core` and `alloc` keeps the trusted base free of non-kernel dependencies, and finds a descriptor in expected constant time where an ordered map compares descriptors along a logarithmic path and allocates per entry when cloned. **Alternatives.** An ordered map (`BTreeMap`) needs no hash premise and bounds every lookup logarithmically; `hashbrown`'s table would replace this one at the cost of a dependency in the trusted base. **Reversal.** The hash is fixed and public, so a producer that chooses colliding descriptors can lengthen probe sequences toward linear time, though it cannot merge two descriptors. A deployment that admits adversarial certificates under a latency bound takes a hash keyed per arena, or the ordered map back.

`Arena::find` answers the same exact lookup without interning: `Maybe::Present(id)` exactly when `alloc` would return the existing `id`, otherwise `interned::Absent::Uninterned`. A reader that must not extend an arena compares against it this way, as a [guarded-admission](../kernel-core/docs/admission.md) row does over a shared binding. The absence type is quenchant-shape's, the workspace's absence vocabulary; it adds no allocation and no `std` dependency to this `no_std` crate.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
