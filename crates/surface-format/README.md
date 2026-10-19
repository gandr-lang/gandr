# gandr-surface-format

The source formatter: a parsed gandr source laid out at a page width through `gandr-surface-layout`, every token and comment kept and the meaning checked unchanged.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The tree, never the core](#the-tree-never-the-core)
- [What moves and what does not](#what-moves-and-what-does-not)
- [Groups are brackets](#groups-are-brackets)
- [Copied as written](#copied-as-written)
- [The meaning is checked, not assumed](#the-meaning-is-checked-not-assumed)
- [Not yet laid out](#not-yet-laid-out)
- [License](#license)

## Synopsis

**What.** `format` takes the grammar, a `ParseResult` and `FormatOptions` (the page width, 100 columns by default) and returns `Formatted`: the text, and one `Piece` per top-level form saying where the form was in the source, where it landed in the text and whether it was laid out or copied as written. The crate uses `core` and `alloc` under `no_std`.

**Why.** `gandr fmt` and the language server's formatting requests need one layout of a source, the same from either, that never changes what the source means.

**How.** The tree is read once into its leaves in offset order, each beside the top-level form it belongs to. Each top-level form is laid out on its own: its brackets nest as groups, a group stays on one line when it fits and otherwise puts each item on a line of its own, and the layout engine picks among those choices by least overflow, then fewest lines. The forms are joined one per line, and the result is parsed again and compared with the source.

## References

- Sorawee Porncharoenwase, Justin Pombrio, and Emina Torlak. "A Pretty Expressive Printer." _Proceedings of the ACM on Programming Languages_ 7, OOPSLA2, October 2023. [doi:10.1145/3622837](https://doi.org/10.1145/3622837), [arXiv:2310.01530](https://arxiv.org/abs/2310.01530) — the cost order the layouts are chosen under.
- Philip Wadler. "A Prettier Printer." In Jeremy Gibbons and Oege de Moor (editors), _The Fun of Programming_, Palgrave Macmillan, 2003. [prettier.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf) — a group that is flat only when everything inside it is.
- The Go authors. [gofmt](https://pkg.go.dev/cmd/gofmt) — a formatter that keeps the line breaks an author wrote between statements and changes only the layout around them.

## Provided features

- `format`: a parsed source formatted at a page width. Witnesses: `tests::format::sweeps::every_source_keeps_its_meaning_and_formats_once`, `tests::format::top_level_forms_and_comments_keep_their_lines`, `tests::format::a_repaired_form_is_copied_as_written`, `tests::format::the_source_line_ending_is_kept`, `tests::format::pieces_place_each_top_level_form`.
- The layout of a form. Witnesses: `tests::format::a_long_declaration_breaks_its_parameters_before_its_type`, `tests::format::a_block_breaks_one_item_per_line_when_it_does_not_fit`, `tests::format::attributes_and_documentation_keep_their_lines`, `tests::format::a_continuation_line_indents_under_its_statement`, `tests::format::strings_shell_blocks_and_holes_are_copied_as_written`.
- `Formatted`, `Piece`, `Layout`: the text, and each top-level form's source and formatted spans, for an editor that applies a formatting change form by form.
- `FormatOptions`, and `PageWidth` re-exported from `gandr-surface-layout`.
- `Form`, `Selection`, `REWRITES`, `RewriteName`: the spelling a source is laid out in — its own, every token kept, or the explicit or sugared one through the table's named rewrites — asked for by `FormatOptions` and declared at a source's head with `@[ form(explicit) ]` or `@[ form(sugared) ]`, the declaration winning (crate docs, § The form a source is spelled in). Witnesses: `tests::rewrite::each_rewrite_moves_its_pair_both_ways`, `tests::rewrite::a_declared_form_wins_over_the_option`.
- `FormatError`, `Change`: why a source was not formatted.
- `comments`, `Comment`, `CommentKind`, `Role`, `Column`, `Width`: every comment of a source beside the node it belongs to — its owner and the owner's cross-tree key, its role among the owner's children (leading, trailing or dangling), its kind, its column and its width — the record a layout keeps and a later comment reflow reads (crate docs, § Every comment belongs to a node). Witnesses: `tests::attach::a_comment_on_its_own_line_leads_the_form_below_it`, `tests::attach::a_comment_after_material_on_its_line_trails_it`, `tests::attach::a_comment_before_a_closing_bracket_dangles_on_its_block`, `tests::attach::documentation_and_the_root_keep_their_owners`, `tests::attach::a_layout_that_breaks_or_joins_a_group_keeps_each_comment_with_its_owner`.

## Expected features

A caller parses the source under the grammar it hands `format`, and keeps the `ParseResult` alive while it reads the `Formatted` spans against the source.

## Examples

```rust
use gandr_surface_format::FormatOptions;
use gandr_surface_format::format;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

let grammar = built_in().expect("the built-in grammar builds");
let parsed = parse(&grammar, SourceText::from("def  answer =  42 ;")).expect("the source parses");
let formatted = format(&grammar, &parsed, FormatOptions::default()).expect("the source formats");
assert_eq!(<&str>::from(formatted.text()), "def answer = 42 ;\n");
```

## The tree, never the core

The formatter reads the concrete syntax tree, because the core drops comments and undoes the shorthand the surface exists for. It reads nothing the checker decides: it depends on the layout engine, the parser, the grammar and the syntax tree, and on neither the checker nor the presentation printer, so formatting a source never lowers, types or marks it.

## What moves and what does not

Only layout changes. Every token and comment is written once, in source order, with its own bytes. Between two tokens the source wrote touching, nothing is inserted; between two it separated, the formatter writes one space or a line break. Spacing inside a line is therefore the author's, normalised to one space.

- **Top level.** Each top-level form starts on a line of its own; a blank line the source wrote between two forms is kept, one at most. A comment the source wrote at the end of a form's last line stays there, and so does a `;` ending a top-level statement. A shebang stays first. The text ends in one line break.
- **Documentation.** A `///` line and a `doc` attribute block keep the line they stand on, since the parser attaches documentation by the lines between it and its declaration.
- **Comments.** A line comment is followed by a line break; a comment the source wrote on its own line stays on its own line.
- **Line endings.** The text uses the ending most of the source's line breaks use, `\r\n` or `\n`; a comment or a copied form keeps its own.

The choice was to keep the author's horizontal spacing and decide only the line structure. The alternative was a token-pair spacing table — no space after `(`, one around `=`, and so on — which also canonicalises spacing; it was not taken yet because a gap the source wrote touching can be one the lexer or the molder reads (a call's `(` absorbs leftwards), and the corpus spells several forms both ways. Reversal: when the surface records one spelling per form, a spacing table replaces the source's gaps.

## Groups are brackets

A group is a bracket pair — `(`, `[`, `{`, `@[` or `#{` and its closer — matched within one top-level form. An item of a group runs up to and including a `,` or `;`, with a comment written after it on the same line; an element the source started on a new line starts an item too, so a module's members and a block's statements keep their lines.

- **Flat or broken.** A group is laid on one line, with the spacing the source wrote inside its brackets, when that fits the page. Otherwise each item stands on its own line, indented two columns past the line holding the opener, and the closer returns to that line's indentation. A blank line the source wrote between two items is kept, one at most; none is kept just inside a bracket.
- **Kept broken.** A group whose opener the source ended a line with, or that holds a line comment, stays broken, so the formatter never joins lines an author split a block over.
- **Lists and blocks.** Only a `{` group and a group holding a separator break. A bracket around one item — a parenthesised type, a single argument — stays on the line around it, and a group inside it breaks instead; breaking it would only move one expression to a line of its own.
- **Continuation.** A line the source indented deeper than the statement before it, after no separator, continues that statement and is indented two further columns.
- **Flat means flat.** A group laid on one line lays every group inside it on one line too, unless an inner group must stay broken, which the outer line then holds as written.

The engine chooses among the flat and broken layout of every group at once, by least overflow and then fewest lines, so the outermost list that does not fit breaks first only when breaking it saves lines. The alternative of rules per grammar form — one document builder per form, naming its break points — was the recorded plan; it is the follow-up, since the bracket rule already lays out declarations, parameter lists, blocks, records, lists and attribute blocks, and a per-form rule can refine a form without changing the others. Reversal: a form whose layout needs a break point that is not a bracket gets its own rule.

## Copied as written

Some material is laid down byte for byte, the line breaks inside it included:

- **A string.** Its fragments are its text.
- **A shell block.** Its line breaks separate commands, so the formatter does not format its interior; formatting the shell fragment is its own decision, and keeping it byte-identical is the conservative one until the shell fragment states a layout.
- **A hole.** Holes are left as written, as error regions are.
- **A repaired form.** A top-level form holding grout or a minted close, or that a parser obligation touches, is copied from its first token to its last, so formatting a source mid-edit never moves what the parser had to guess at. Its `Piece` says `Layout::Repaired`.

A comment spanning lines, or holding a tab, is copied the same way.

## The meaning is checked, not assumed

The content digest skips layout, so `digest(parse(format(source))) == digest(parse(source))` holds for any correct formatting. `format` parses its own text before returning it, and refuses with `FormatError::Changed` when the digest differs, when the text's tokens and comments, read in order, are not the source's, or when a comment would leave the node it belongs to or change its role there. A rewrite changes tokens, so its check is the lowering instead: a declaration whose rewritten text lowers otherwise keeps its spelling. The corpus tests format every source at three page widths and into either form, and format the result again, asserting nothing moves.

## Not yet laid out

- **Per-form rules.** As above, the layout is the bracket rule; a long expression with no brackets stays on one line.
- **A fill layout.** A list too long for one line puts every item on its own line; packing several per line is a later rule.
- **Range formatting at isolation boundaries.** A caller formats a range by replacing the `Piece`s it touches, so the unit of a range edit is a top-level form.
- **Comment reflow.** Comments keep their own lines and bytes. A reflow pass that rewraps a comment at the page width would run over the attachment record before layout; it is not built.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
