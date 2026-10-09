# gandr-surface-syntax

The concrete syntax tree of the gandr surface language: a molded node vocabulary, byte spans, and a flat level-order arena whose every node carries an arena position and a content digest.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Molded labels](#molded-labels)
- [Layout in the tree](#layout-in-the-tree)
- [Arena position and content digest](#arena-position-and-content-digest)
- [Digest preimage](#digest-preimage)
- [Level-order layout](#level-order-layout)
- [Builder identity](#builder-identity)
- [Source text and fragments](#source-text-and-fragments)
- [Grammar references](#grammar-references)
- [Specification attributes](#specification-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The tree a surface parser produces. `NodeLabel` is what a node is: a completed form or a written tile, each named by its `MoldId`; grout the parser inserted where the source left a term or a closer unwritten; layout; or the root. `ByteSpan` is a half-open byte range of a `SourceText`; `SyntaxTree` is a flat arena laid out in level order, whose node carries its label, its span, its children as a contiguous range of arena positions, and a `NodeDigest`, and which records the `GrammarFingerprint` its mold ids index. `TreeBuilder` stages nodes bottom-up as a parser completes them and finishes them into the arena. `MoldId`, `GroutSort`, `GroutShape`, `GrammarFingerprint` and `ClosingClass` are the references into a grammar's tables that a grammar and a parser exchange. The crate holds representation only: it lexes and parses nothing, and reads a source only to answer what a span covers. It is `no_std` over `core` and `alloc`, and its one runtime dependency is BLAKE3.

**Why.** A consumer that dispatches on forms needs the tree to name them; the grammar already names every form by the molds of its tiles, so the node carries a mold and the grammar resolves it. A re-renderer needs every byte back, so layout and inserted material are nodes. A position resolves fast inside one tree but moves with every edit earlier in the file; a consumer whose side table outlives one parse needs an identity that depends on content alone, and that a reformat leaves alone.

**How.** Children as a contiguous range force level order, which puts every parent before its children: a walk in ascending position order needs no stack, and a cycle is unrepresentable rather than checked for. The digest is computed at staging over the significant children's digests rather than their positions, so it survives the layout, every edit elsewhere in the file, and every change of layout inside the node. A staged identity carries the identity of the builder that minted it. Every refusal is a `SyntaxError` naming the offset or staged node it rejected; nothing panics, indexes, or repairs.

## References

- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves and Zooko Wilcox-O'Hearn. "BLAKE3: one function, fast everywhere." Specification, 9 January 2020. <https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf> — the hash whose extendable output is a node digest.
- David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (2025). <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — molds, grout and the material a tree records.

## Provided features

- `NodeLabel`, `LabelTag`, `CarriesText` and `Significance`: the molded node vocabulary, each label with a pinned digest tag, whether it draws text from the source, and whether a parent's digest folds it. Witnesses: `label::tests::every_digest_tag_is_pinned`, `label::tests::only_layout_is_insignificant`.
- `SyntaxTree`, `Node` and `NodeIndex`: the level-order arena with checked lookups, `children`, `positions`, `fragment` and the recorded `grammar`.
- `TreeBuilder` and `StagedId`: bottom-up staging under a grammar fingerprint and the layout `TreeBuilder::finish` produces.
- `NodeDigest` and `NODE_DIGEST_LEN`: the 32-byte content identity, rendered as lowercase hexadecimal.
- `SourceText`, `SourceFragment`, `ByteSpan`, `ByteOffset` and `ByteLength`: byte-addressed source positions.
- `SyntaxError`: every refusal, with the offset, span or staged node it names.
- `MoldId`, `GroutSort`, `GroutShape`, `GrammarFingerprint`, `ClosingClass` and `DelimSpelling`: the references a grammar and a parser exchange — a mold's position in its grammar's table, the sort a hole stands for, the sides a piece of grout faces, the fingerprint naming the table, and the bracket family a delimiter opens or closes. Witnesses: `mold::tests::openers_and_closers_pair_by_family`, `mold::tests::a_host_index_past_the_id_width_is_refused`.

## Expected features

- **Atomic compare-exchange.** Builder identities come from a process-wide atomic counter, so the crate requires `target_has_atomic = "ptr"`. Every hosted target and every embedded target with a compare-exchange instruction qualifies; building for a load/store-only core fails with an explanatory `compile_error!`.
- **A grammar that resolves molds.** A `MoldId` means something only under the grammar whose fingerprint the tree records. The consumer reads the form a node realises from that grammar (in this workspace, `gandr-surface-grammar`'s `Pbg::named_kind`), and compares fingerprints before it reads.
- **Distinct declarations.** A digest is a content identity, not an occurrence identity: two declarations with identical content have one digest. A consumer keying a table on digests owes the argument that its keys are distinct; in the surface language a declaration's digest folds its name, so a module that refuses a name bound twice supplies it.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.

## Examples

Stage bottom-up, finish into the arena, then walk it in ascending position order:

```rust
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxError;
use gandr_surface_syntax::TreeBuilder;

fn example() -> Result<(), SyntaxError> {
    // The mold ids index the table the fingerprint names; these are
    // illustrative, where a parser reads them from its grammar.
    let source = SourceText::from("f x");
    let mut builder = TreeBuilder::new(source, GrammarFingerprint::from(7_u64))?;

    // `?` is a statement, never a subexpression: every fallible step is
    // bound with `let` before the name is used.
    let at = |start: usize, end: usize| {
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
    };
    let word = NodeLabel::Tile(MoldId::from(4_u32));
    let head_span = at(0, 1)?;
    let head = builder.node(word, head_span, &[])?;
    let gap = at(1, 2)?;
    let space = builder.node(NodeLabel::Space, gap, &[])?;
    let argument_span = at(2, 3)?;
    let argument = builder.node(word, argument_span, &[])?;
    let whole = at(0, 3)?;
    let application =
        builder.node(NodeLabel::Meld(MoldId::from(4_u32)), whole, &[head, space, argument])?;
    let root = builder.node(NodeLabel::Wald, whole, &[application])?;
    let tree = builder.finish(root)?;

    // A fragment is not a source: it says what a node covers, never what an
    // offset means.
    assert_eq!(tree.fragment(tree.root()), Some(SourceFragment::from("f x")));

    // Level order: every child sits strictly above its parent.
    for parent in tree.positions() {
        for child in tree.children(parent) {
            assert!(usize::from(child) > usize::from(parent));
        }
    }
    Ok(())
}
```

The same example is the doctest on `TreeBuilder`. Run the tests, the doctests, and the tests with specifications enforced:

```sh
cargo nextest run -p gandr-surface-syntax
cargo test -p gandr-surface-syntax --doc
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-surface-syntax
```

## Molded labels

A node carries its kind, and the kind is a mold. A `NodeLabel::Tile` is a written tile and a `NodeLabel::Meld` a completed form, each named by a `MoldId` — a form by the mold of the tile that opened it, the operator of a one-tile operator form, or its first tile otherwise. The grammar that numbered the molds resolves an id, as a total function over its mold table, to the rule the mold belongs to and the rule's named kind, so a lowering dispatches on kinds and has nothing to adapt. The forms the language admits are the grammar's to state, once; the tree names no form of its own.

The alternative was a closed `NodeKind` enum in this crate, one variant per surface form, which a parser fills by mapping each completed form to a variant. It names forms without a grammar in hand, but restates the grammar's forms in a second place and needs a read adapter from molds to variants that grows with the grammar; a parser-owned second tree beside this one was the other alternative, and it would give every consumer two identities to reconcile. Reversal: if a consumer needs a form vocabulary the grammar's named kinds do not supply, a closed kind returns as that read adapter over the molded tree, and its cost — thousands of lines for this grammar's surface — is what this choice avoids.

## Layout in the tree

Every token the source wrote is a node, layout included, so the leaves read in source order reproduce the source byte for byte; grout the parser inserted covers no bytes, and grout standing over a token no grammar label molds covers exactly that token's. Every leaf label carries its own text into its digest — a tile, grout, a minted close and layout — so two unmolded tokens of different spellings are two identities; a form and the root carry only their children's. A parent's digest folds a child only when the child's label is significant, and `NodeLabel::Space` is the one label that is not, so reformatting a declaration leaves its digest and every ancestor's unchanged while the layout stays in the tree for a re-renderer. A missing closer is a `NodeLabel::GhostClose` naming its family, so a consumer can pair it against a closer written later; a missing closer of no single family is postfix grout.

## Arena position and content digest

`NodeIndex` addresses a node inside one tree and nowhere else: it is an offset into that tree's node vector, and the next parse of an edited source lays the same declaration out elsewhere. `NodeDigest` addresses a node across trees, runs and processes: it is a function of the node's label, its own text when its label carries text, and its significant children's digests, so the same declaration parsed from two files on two machines carries one identity. A side table keyed by position is invalidated by an edit anywhere earlier in the file; one keyed by digest only by an edit to the thing it is about. A diagnostic that carries both resolves fast in the tree in hand and survives it.

## Digest preimage

The preimage is the domain string `gandr.surface-syntax.node.v2`, the label's pinned tag, the label's payload (a mold id as four little-endian bytes; a grout's sort as two and its shape as one; a minted close's sort as two and its family as one), the significant child count, the node's own text when its label is a leaf label, and the significant children's digests in order. Spans, child positions and layout children are excluded, so moving or reformatting text leaves its digest unchanged. Every variable-width field is preceded by its length at a fixed width, so `ab` beside `c` and `a` beside `bc` hash differently. The version suffix belongs to the domain: a change to the layout changes every node's identity, and two layouts never compare equal. The pinned form is asserted against an external BLAKE3 golden rather than a value this crate produced.

## Level-order layout

A node names its children as a contiguous range of strictly higher arena positions: two fields per node and no second vector. A post-order arena, which a bottom-up builder produces naturally, cannot give a node's children a contiguous range, because the second child's subtree sits between the first child and the second; level order can. The root is position zero, every child sits above its parent, so an ascending scan visits parents first and an index comparison decides ancestry direction.

## Builder identity

A parser mints bottom-up and the arena is laid out top-down, so a `StagedId` and a `NodeIndex` are different types: they are different permutations of the same nodes, and a `StagedId` stops at `TreeBuilder::finish`. A `StagedId` carries the process-unique identity of its builder, and every entry point checks it before the position, so a handle offered to another builder is refused with `SyntaxError::UnknownStagedNode` rather than resolving against whatever that builder staged at the same position. The identity counter refuses to wrap, with `SyntaxError::BuilderIdExhausted`, and `TreeBuilder` is not `Clone`, because either would restore the aliasing the identity removes. A staged node accepts one parent; a second is refused with `SyntaxError::ChildAlreadyAttached`.

## Source text and fragments

A position is a byte offset, the unit the lexer has and an edit is expressed in; a diagnostic renderer converts to lines once, at display. `ByteSpan::new` refuses an inverted pair, and reading a span against a source refuses an endpoint past the end or inside a character. `SourceText` is the offset frame a span is measured against; `SourceFragment` is the bytes one span covers, with no frame of its own. A fragment has no `end` and no `fragment` and cannot seed a `TreeBuilder`, because each would reinterpret absolute offsets against a string that starts elsewhere; the type split makes each a compile error rather than a wrong answer.

## Grammar references

The grammar owns its mold table; this crate defines only the references into it, below both the grammar and the parser that name them, so the grammar depends on no parser and the tree on no grammar. A `MoldId` is a 32-bit position in the table of the grammar a `GrammarFingerprint` names, and means nothing under another: a tree records its fingerprint, and a consumer holding ids from two grammars compares fingerprints, never ids. A `GroutSort` is a sort tag, decoded by the grammar that assigned it; a `GroutShape` says which sides a piece of grout faces, convex for a missing term and postfix for a missing closer. `ClosingClass` has three families — parentheses, brackets and braces, the record opener `#{` among the braces — and a closer answers its own family only.

## Specification attributes

Each nontrivial item's `# Specification` is paired with `# Adequacy`: the input boundaries, observable results, fault classes and same-crate witnesses. Executable `#[spec(...)]` clauses cover source slicing and refusal precedence, delimiter recognition, checked identifiers, builder transitions and arena walks. Enforcement captures scalar pre-state where an operation consumes or mutates its inputs; it does not copy the staging arena or repeat hashing.

Constant functions use direct const-compatible predicates. The node constructor checks every offered part; layout adoption checks source, grammar and child-range geometry. Exact preservation of the moved node vector remains covered by witnesses because const specifications do not capture pre-state. Formatters expose a write-only sink; hashing's provenance and cross-call identity laws need independent witnesses rather than a repeated hash; type-level obligations are witnessed at construction and observation boundaries. These items state their remaining non-executable reasons. Run the suite both normally and with `--cfg anodized_panic` using the commands above.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
