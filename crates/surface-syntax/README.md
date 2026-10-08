# gandr-surface-syntax

The concrete syntax tree of the gandr surface: the closed token vocabulary, the closed node vocabulary, a flat node arena whose children are a contiguous range of arena positions, byte spans, and the two identities every node carries.

It holds **representation only** — no lexer, no parser, no lowering. Nothing here reads a source except to answer what a span covers. It is `no_std` over `core` and `alloc`, and its one runtime dependency is BLAKE3, which computes the content identity.

## Pipeline role

This crate supplies the concrete syntax tree for the minimal parse-and-check slice. It has no in-workspace dependency; its planned consumers are `gandr-surface-parser` and `gandr-surface-lowering`.

| unit clause | where it lives |
| ----------- | -------------- |
| the token vocabulary | `src/token.rs` |
| the closed node-kind enum | `src/kind.rs` |
| byte spans | `src/span.rs` |
| the content-derived identity | `src/digest.rs` |
| the flat arena, children as a range | `src/tree.rs` |
| staging and the level-order layout | `src/build.rs` |
| the typed refusal vocabulary | `src/error.rs` |

## The two identities, and the distinction is load-bearing

A node carries an **arena position** and a **content digest**, and they answer different questions.

`NodeIndex` addresses a node inside one tree and nowhere else. It is an offset into that tree's node vector, and the next parse of an edited source lays the same declaration out at a different offset.

`NodeDigest` addresses a node across trees, runs and processes. It is a function of the node's kind, its own source text when its kind carries text, and its children's digests — of nothing else. Spans are not hashed and neither are child positions, so the same declaration parsed from two files, in two processes, on two machines carries one identity.

Diagnostics and the origin table carry both: the position resolves fast inside the tree in hand, the digest survives the tree. A side table keyed by position is invalidated by an edit anywhere earlier in the file; a side table keyed by digest is invalidated only by an edit to the thing it is about. That is why the attribute side table and any later checkpoint key on the digest alone.

The digest preimage is domain-separated and every variable-width field is preceded by its length at a fixed width, so two sibling texts cannot run together into a third reading. Its pinned form is asserted against an external BLAKE3 golden rather than against a value this crate produced.

## What it provides

- `TokenKind`, twenty-one lexeme classes with their fixed spellings, and `Token`, one spanned lexeme. No trivia class and no end marker: whitespace is skipped by the lexer, and the stream ends by exhaustion, so a tree can re-render a stream equal to the lexer's own.
- `NodeKind`, eighteen forms with a pinned per-kind digest tag. The node carries its kind, so the lowering above dispatches on forms directly and the read adapter that a form-name-free tree would need never exists.
- `SyntaxTree`, the arena: nodes in level order, root at position zero, each node's children a contiguous range of strictly higher positions. A walk in ascending position order visits every parent before any of its children with no stack, and a cycle is unrepresentable rather than checked for.
- `TreeBuilder` and `StagedId`, the bottom-up staging a parser mints into, and the level-order layout it finishes to. Staged identities and arena positions are different types because they are different permutations of the same nodes, and a `StagedId` names the builder that minted it, so a handle offered to a different builder is refused rather than resolving against whatever that builder staged at the same position.
- `SourceText` and `SourceFragment`, kept apart on purpose. `SourceText` is the offset frame a `ByteSpan` is measured against; a `SourceFragment` is the bytes one span covers and carries no frame of its own, so it has no `end`, no `fragment`, and cannot be handed to a `TreeBuilder` as a source. Each of those would reinterpret absolute offsets against a string starting somewhere else, and each is a compile error rather than a wrong answer.
- `ByteSpan` over `ByteOffset`, half-open, minted only through a check that refuses an inverted pair, and read against a source through a check that refuses an out-of-range endpoint or one inside a character.
- Totality. Every refusal is a `SyntaxError` value naming the exact offset or staged node it rejected; nothing panics, indexes, or repairs.

## Two shape decisions worth stating

**Punctuation is implied; grouping is not.** A token whose presence the parent's kind determines — a signature's colon and semicolon, a lambda's dot — is recovered from the kind rather than stored. A grouping is different: `(x)` and `x` differ in the token stream and in nothing else, so `NodeKind::Grouped` is a node, which is what lets a re-render reproduce the lexer's own stream exactly rather than a re-parenthesized variant of it.

**An attribute block is the module's child, not the declaration's.** Attaching, editing or removing an attribute therefore leaves the decorated declaration's digest unchanged — which is the property the attribute side table, keyed by that digest, depends on.

## The contract attributes

The `# Specification` prose stays the statement of record; a combined `#[spec(...)]` attribute mirrors it where the whole clause is a predicate over one call. Five items carry one:

- `SourceText::fragment` and `SyntaxTree::fragment` — the returned fragment is exactly the byte range the span names, so a body that clamped an endpoint, reordered a pair, or read a different range fails rather than answering plausibly;
- `ByteSpan::join` — the result's endpoints are the lower start and the higher end, which is the whole selection rather than only the ordering it implies;
- `SyntaxTree::node` — the one checked lookup the other reads are built on, stated against the layout's own slot;
- `TreeBuilder::resolve` — the stamp-and-range check stated as an equivalence, so a resolution admitting a foreign stamp or an out-of-range position fails at the one place both are decided.

Thirteen prose-only blocks name their boundary in `provides`. Six are `const fn` items — `NodeKind::tag`, `NodeKind::carries_text`, `TokenKind::spelling`, `ByteSpan::new`, `ByteSpan::length` and `SyntaxTree::from_layout` — which keep their const API without the attribute, because the pinned `anodized` expansion calls a non-const evaluator (`E0015`). The other seven are a law over several calls (`digest_of`'s agreement on equal triples), a claim over a counter's whole issuance history (`BuilderIdCounter::allocate`), a rendering claim about the two implementations beside a type (`NodeDigest`), a property holding only under a precondition the item adopts without checking, where asserting it would turn a documented wrong walk into a panic (`SyntaxTree::children`), the process-wide freshness a new builder's identity carries (`TreeBuilder::new`), a digest fold over the child list one call consumed beside an exactly-one-parent claim over the whole edge list (`TreeBuilder::node`), and a comparison against the staged side the call consumes (`TreeBuilder::finish`).

Existing adequacy hypotheses and witnesses are unchanged; a runtime clause establishes no adequacy claim. `anodized` supplies core-only specification helpers with default features disabled, and the enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph.

## Not provided

- Lexing and parsing. The vocabulary lives here so the producer and a re-renderer can be compared against a table neither of them owns.
- Trivia retention, error recovery, and partial trees. The slice's parser refuses at the first fault with one span; total marking and the completion ladder arrive with an editor face that needs every error from one pass.
- Interning, incremental re-parse, and edit application. The digest is the identity such a layer would key on, and it is here; the layer is not.

## Using it

Stage bottom-up, finish into the arena, then walk it in ascending position order.

This example is the doctest on `TreeBuilder`, so it is compiled and run by `cargo test` rather than copied here to rot.

```rust
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeKind;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxError;
use gandr_surface_syntax::TreeBuilder;

fn example() -> Result<(), SyntaxError> {
    let source = SourceText::from("def f = x ;");
    let mut builder = TreeBuilder::new(source)?;

    // `?` is a statement, never a subexpression: every fallible step is
    // bound with `let` before the name is used.
    let at = |start: usize, end: usize| {
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
    };
    let name_span = at(4, 5)?;
    let name = builder.node(NodeKind::Name, name_span, &[])?;
    let body_span = at(8, 9)?;
    let body = builder.node(NodeKind::Name, body_span, &[])?;
    let whole = at(0, 11)?;
    let definition = builder.node(NodeKind::Definition, whole, &[name, body])?;
    let module = builder.node(NodeKind::Module, whole, &[definition])?;
    let tree = builder.finish(module)?;

    // A fragment is not a source: it says what a node covers, never what an
    // offset means.
    assert_eq!(tree.fragment(tree.root()), Some(SourceFragment::from("def f = x ;")));

    // Level order: every child sits strictly above its parent.
    for parent in tree.positions() {
        for child in tree.children(parent) {
            assert!(usize::from(child) > usize::from(parent));
        }
    }
    Ok(())
}
```

## Ideas relied on

Flat id-addressed arenas in place of pointer-linked recursive data; level-order layout as the enabling condition for children-as-an-index-range; content addressing with domain separation and length-prefixed preimages; the separation of a positional identity from a content identity, which is what lets a side table survive an edit elsewhere in the file.

## License

Apache-2.0 WITH LLVM-exception.
