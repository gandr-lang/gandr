# gandr-surface-syntax

The concrete syntax tree of the gandr surface language: closed token and node vocabularies, byte spans, and a flat level-order arena whose every node carries an arena position and a content digest.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Arena position and content digest](#arena-position-and-content-digest)
- [Digest preimage](#digest-preimage)
- [Level-order layout](#level-order-layout)
- [Builder identity](#builder-identity)
- [Source text and fragments](#source-text-and-fragments)
- [Punctuation and grouping](#punctuation-and-grouping)
- [Attribute placement](#attribute-placement)
- [Grammar references](#grammar-references)
- [Specification attributes](#specification-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The tree a surface parser produces. `TokenKind` and `NodeKind` are the closed lexical and node vocabularies; `ByteSpan` is a half-open byte range of a `SourceText`; `SyntaxTree` is a flat arena laid out in level order, whose node carries its kind, its span, its children as a contiguous range of arena positions, and a `NodeDigest`. `TreeBuilder` stages nodes bottom-up as a parser completes them and finishes them into the arena. `MoldId`, `GroutSort`, `GrammarFingerprint` and `ClosingClass` are the references into a grammar's tables that a grammar and a parser exchange. The crate holds representation only: it lexes and parses nothing, and reads a source only to answer what a span covers. It is `no_std` over `core` and `alloc`, and its one runtime dependency is BLAKE3.

**Why.** A lexer and a re-renderer compare token streams, so the vocabulary they compare against lives beside the tree rather than inside either. A consumer that dispatches on forms needs the tree to name them, so each node carries its kind. A position resolves fast inside one tree but moves with every edit earlier in the file; a consumer whose side table outlives one parse needs an identity that depends on content alone.

**How.** Children as a contiguous range force level order, which puts every parent before its children: a walk in ascending position order needs no stack, and a cycle is unrepresentable rather than checked for. The digest is computed at staging over the children's digests rather than their positions, so it survives the layout and every edit elsewhere in the file. A staged identity carries the identity of the builder that minted it. Every refusal is a `SyntaxError` naming the offset or staged node it rejected; nothing panics, indexes, or repairs.

## References

- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves and Zooko Wilcox-O'Hearn. "BLAKE3: one function, fast everywhere." Specification, 9 January 2020. <https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf> — the hash whose extendable output is a node digest.

## Provided features

- `TokenKind`, `TokenSpelling` and `Token`: the closed lexeme classes, their fixed spellings, and one spanned lexeme.
- `NodeKind`, `KindTag` and `CarriesText`: the closed node forms, each with a pinned digest tag and whether it draws text from the source.
- `SyntaxTree`, `Node` and `NodeIndex`: the level-order arena with checked lookups, `children`, `positions` and `fragment`.
- `TreeBuilder` and `StagedId`: bottom-up staging and the layout `TreeBuilder::finish` produces.
- `NodeDigest` and `NODE_DIGEST_LEN`: the 32-byte content identity, rendered as lowercase hexadecimal.
- `SourceText`, `SourceFragment`, `ByteSpan`, `ByteOffset` and `ByteLength`: byte-addressed source positions.
- `SyntaxError`: every refusal, with the offset, span or staged node it names.
- `MoldId`, `GroutSort`, `GrammarFingerprint`, `ClosingClass` and `DelimSpelling`: the references a grammar and a parser exchange — a mold's position in its grammar's table, the sort a hole stands for, the fingerprint naming the table, and the bracket family a delimiter opens or closes. Witnesses: `mold::tests::openers_and_closers_pair_by_family`, `mold::tests::a_host_index_past_the_id_width_is_refused`.

## Expected features

- **Atomic compare-exchange.** Builder identities come from a process-wide atomic counter, so the crate requires `target_has_atomic = "ptr"`. Every hosted target and every embedded target with a compare-exchange instruction qualifies; building for a load/store-only core fails with an explanatory `compile_error!`.
- **Distinct declarations.** A digest is a content identity, not an occurrence identity: two declarations with identical content have one digest. A consumer keying a table on digests owes the argument that its keys are distinct; in the surface language a declaration's digest folds its name, so a module that refuses a name bound twice supplies it.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.

## Examples

Stage bottom-up, finish into the arena, then walk it in ascending position order:

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

The same example is the doctest on `TreeBuilder`. Run the tests, the doctests, and the tests with specifications enforced:

```sh
cargo nextest run -p gandr-surface-syntax
cargo test -p gandr-surface-syntax --doc
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-surface-syntax
```

## Arena position and content digest

`NodeIndex` addresses a node inside one tree and nowhere else: it is an offset into that tree's node vector, and the next parse of an edited source lays the same declaration out elsewhere. `NodeDigest` addresses a node across trees, runs and processes: it is a function of the node's kind, its own text when its kind carries text, and its children's digests, so the same declaration parsed from two files on two machines carries one identity. A side table keyed by position is invalidated by an edit anywhere earlier in the file; one keyed by digest only by an edit to the thing it is about. A diagnostic that carries both resolves fast in the tree in hand and survives it.

## Digest preimage

The preimage is the domain string `gandr.surface-syntax.node.v1`, the kind's pinned tag, the child count, the node's own text when its kind carries text, and the children's digests in order. Spans and child positions are excluded, so moving text leaves its digest unchanged. Every variable-width field is preceded by its length at a fixed width, so `ab` beside `c` and `a` beside `bc` hash differently. The version suffix belongs to the domain: a change to the layout changes every node's identity, and two layouts never compare equal. The pinned form is asserted against an external BLAKE3 golden rather than a value this crate produced.

## Level-order layout

A node names its children as a contiguous range of strictly higher arena positions: two fields per node and no second vector. A post-order arena, which a bottom-up builder produces naturally, cannot give a node's children a contiguous range, because the second child's subtree sits between the first child and the second; level order can. The root is position zero, every child sits above its parent, so an ascending scan visits parents first and an index comparison decides ancestry direction.

## Builder identity

A parser mints bottom-up and the arena is laid out top-down, so a `StagedId` and a `NodeIndex` are different types: they are different permutations of the same nodes, and a `StagedId` stops at `TreeBuilder::finish`. A `StagedId` carries the process-unique identity of its builder, and every entry point checks it before the position, so a handle offered to another builder is refused with `SyntaxError::UnknownStagedNode` rather than resolving against whatever that builder staged at the same position. The identity counter refuses to wrap, with `SyntaxError::BuilderIdExhausted`, and `TreeBuilder` is not `Clone`, because either would restore the aliasing the identity removes. A staged node accepts one parent; a second is refused with `SyntaxError::ChildAlreadyAttached`.

## Source text and fragments

A position is a byte offset, the unit the lexer has and an edit is expressed in; a diagnostic renderer converts to lines once, at display. `ByteSpan::new` refuses an inverted pair, and reading a span against a source refuses an endpoint past the end or inside a character. `SourceText` is the offset frame a span is measured against; `SourceFragment` is the bytes one span covers, with no frame of its own. A fragment has no `end` and no `fragment` and cannot seed a `TreeBuilder`, because each would reinterpret absolute offsets against a string that starts elsewhere; the type split makes each a compile error rather than a wrong answer.

## Punctuation and grouping

The token vocabulary has no trivia class and no end marker: the lexer skips whitespace and the stream ends by exhaustion, so a tree re-renders a stream equal to the lexer's own. A token whose presence the parent's kind determines, such as a signature's colon or a lambda's dot, is recovered from the kind rather than stored. A grouping is a node, `NodeKind::Grouped`, because `(x)` and `x` differ in the token stream and nowhere else. An identifier is `NodeKind::Name` wherever it appears; its parent's kind and its position decide the sort it is read at.

## Attribute placement

An attribute block is a child of the module, in source order, never of the declaration it decorates. Attaching, editing or removing an attribute therefore leaves the declaration's digest unchanged, which is the key a side table of attributes files the declaration under.

## Grammar references

The grammar owns its mold table; this crate defines only the references into it, below both the grammar and the parser that name them, so the grammar depends on no parser and the tree on no grammar. A `MoldId` is a 32-bit position in the table of the grammar a `GrammarFingerprint` names, and means nothing under another: a consumer holding ids from two grammars compares fingerprints, never ids. A `GroutSort` is a sort tag, decoded by the grammar that assigned it. `ClosingClass` has three families — parentheses, brackets and braces, the record opener `#{` among the braces — and a closer answers its own family only.

## Specification attributes

Each item's `# Specification` prose is the statement of record; a `#[spec(...)]` attribute states a clause verbatim where the whole clause is a predicate over one call, such as `SourceText::fragment` returning exactly the range the span names. The `const fn` items — `NodeKind::tag`, `NodeKind::carries_text`, `TokenKind::spelling`, `ByteSpan::new`, `ByteSpan::length` and `SyntaxTree::from_layout` — keep their `const` API and stay prose, because the `anodized` expansion calls a non-`const` evaluator (`E0015`). A clause that relates several calls, a counter's whole issuance history, or a precondition the item adopts without checking stays prose and names its boundary in `provides`.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
