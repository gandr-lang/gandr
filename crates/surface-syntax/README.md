# gandr-surface-syntax

The concrete syntax tree of the gandr surface language: a molded node vocabulary, byte spans, and a flat level-order arena whose every node carries an arena position and, inside a top-level form, a cross-tree key.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The tree a surface parser produces. `NodeLabel` is what a node is: a completed form or a written tile, each named by its `MoldId`; grout the parser inserted where the source left a term or a closer unwritten; layout; or the root. `ByteSpan` is a half-open byte range of a `SourceText`; `SyntaxTree` is a flat arena laid out in level order, whose node carries its label, its span, and its children as a contiguous range of arena positions, which records the `GrammarFingerprint` its mold ids index, and which digests each top-level form once and keys every node inside one by that `NodeDigest` and a rank. `TreeBuilder` stages nodes bottom-up as a parser completes them and finishes them into the arena. `MoldId`, `GroutSort`, `GroutShape`, `GrammarFingerprint` and `ClosingClass` are the references into a grammar's tables that a grammar and a parser exchange. The crate holds representation only: it lexes and parses nothing, and reads a source only to answer what a span covers. It is `no_std` over `core` and `alloc`, and its one runtime dependency is BLAKE3.

**Why.** A consumer that dispatches on forms needs the tree to name them; the grammar already names every form by the molds of its tiles, so the node carries a mold and the grammar resolves it. A re-renderer needs every byte back, so layout and inserted material are nodes. A position resolves fast inside one tree but moves with every edit earlier in the file; a consumer whose side table outlives one parse needs an identity that depends on content alone, and that a reformat leaves alone.

**How.** Children as a contiguous range force level order, which puts every parent before its children: a walk in ascending position order needs no stack, and a cycle is unrepresentable rather than checked for. A form's digest is one hash over its significant nodes in preorder, taken as the builder lays the tree out, rather than over positions, so it survives the layout, every edit elsewhere in the file, and every change of layout inside the form. A staged identity carries the identity of the builder that minted it. Every refusal is a `SyntaxError` naming the offset or staged node it rejected; nothing panics, indexes, or repairs.

## Provided features

- `NodeLabel`, `LabelTag`, `CarriesText` and `Significance`: the molded node vocabulary, each label with a pinned digest tag, whether it draws text from the source, and whether a form's digest reads it. Witnesses: `label::tests::every_digest_tag_is_pinned`, `label::tests::only_layout_is_insignificant`.
- `SyntaxTree`, `Node` and `NodeIndex`: the level-order arena with checked lookups, `children`, `positions`, `fragment` and the recorded `grammar`.
- `TreeBuilder` and `StagedId`: bottom-up staging under a grammar fingerprint and the layout `TreeBuilder::finish` produces, which digests each top-level form and the tree. Witnesses: `build::tests::two_builds_of_one_source_agree_digest_by_digest`, `build::tests::an_edit_reaches_its_form_and_the_tree`.
- `NodeDigest` and `NODE_DIGEST_LEN`: the 32-byte content identity of a form or a tree, rendered as lowercase hexadecimal. Witnesses: `digest::tests::a_pinned_form_digest_is_stable`, `digest::tests::a_digest_renders_lowercase_hexadecimal`.
- `NodeKey`, `FormRank`, `SyntaxTree::key`, `SyntaxTree::forms` and `SyntaxTree::digest`: a significant node's cross-tree key — its top-level form's digest and its preorder rank in that form — the forms, and the whole tree's digest. Witnesses: `build::tests::keys_rank_a_forms_nodes_in_preorder`, `build::tests::keys_survive_layout_and_another_forms_edit`.
- `SyntaxTree::joined` and `SyntaxTree::roots`: one tree laid after another as a forest over their joined text, one root per tree, keys and digests the second tree's own. Witnesses: `build::tests::a_join_lays_the_second_tree_after_the_first`, `build::tests::a_join_refuses_a_text_or_a_grammar_of_its_own`.
- `SourceText`, `SourceFragment`, `ByteSpan`, `ByteOffset` and `ByteLength`: byte-addressed source positions.
- `SyntaxError`: every refusal, with the offset, span or staged node it names.
- `MoldId`, `GroutSort`, `GroutShape`, `GrammarFingerprint`, `ClosingClass` and `DelimSpelling`: the references a grammar and a parser exchange — a mold's position in its grammar's table, the sort a hole stands for, the sides a piece of grout faces, the fingerprint naming the table, and the bracket family a delimiter opens or closes. Witnesses: `mold::tests::openers_and_closers_pair_by_family`, `mold::tests::a_host_index_past_the_id_width_is_refused`.

## Expected features

- **Atomic compare-exchange.** Builder identities come from a process-wide atomic counter, so the crate requires `target_has_atomic = "ptr"`. Every hosted target and every embedded target with a compare-exchange instruction qualifies; building for a load/store-only core fails with an explanatory `compile_error!`.
- **A grammar that resolves molds.** A `MoldId` means something only under the grammar whose fingerprint the tree records. The consumer reads the form a node realises from that grammar (in this workspace, `gandr-surface-grammar`'s `Pbg::named_kind`), and compares fingerprints before it reads.
- **Distinct declarations.** A digest is a content identity, not an occurrence identity: two top-level forms with identical content have one digest, and so equal keys at equal ranks. A consumer keying a table on keys owes the argument that its keys are distinct; in the surface language a declaration's form folds its name, so a module that refuses a name bound twice supplies it. Two nodes in one form always have distinct keys.
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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Molded labels, layout in the tree | [`label`](src/label.rs) |
| The digest preimage | [`digest`](src/digest.rs) |
| Node keys | [`key`](src/key.rs) |
| Level-order layout | [`tree`](src/tree.rs) |
| Builder identity | [`build`](src/build.rs) |
| Source text and fragments | [`span`](src/span.rs) |
| Grammar references | [`mold`](src/mold.rs) |
| Specification attributes, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
