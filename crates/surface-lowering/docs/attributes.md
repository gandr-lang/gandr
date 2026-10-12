# Attributes and documentation

The attribute and documentation halves of `gandr-surface-lowering`: the closed attribute registry, its diagnostics and the side table attributes are filed in, and a declaration's documentation read into one text with its links checked. The crate's [README](../README.md) states the rest of the crate, cites the [references](../README.md#references) this page leans on, and lists every feature with its witnesses.

<!-- toc -->

- [Attributes: a closed registry and a side table](#attributes-a-closed-registry-and-a-side-table)
- [Documentation: one text, its links checked](#documentation-one-text-its-links-checked)

<!-- tocstop -->

## Attributes: a closed registry and a side table

The registry is closed: `checks` takes no payload, `owes` an integer, `refuses`, `runs` and `doc` a text. Five diagnostics cover what an attribute can get wrong, checked in this order: an unknown name, with the registered name within edit distance two when one exists; the same attribute written twice for one declared name, naming the first; a payload that is not a value at all, decided before the schema is consulted because being no value is a different fact from being the wrong one; a missing payload; and a payload of a form the schema does not admit, a payload on a marker included. A payload is read as a value under no binder, and the schema types it at the literal: an integer or a text. A well-formed `doc` entry never reaches the registry, because the parser reads it as [documentation](#documentation-one-text-its-links-checked); `doc` is registered so that a malformed one meets the payload diagnostics.

Executable predicates preserve the registry inventory, exact lookup, the payload decision table, distance bounds and the borrowed identity of a filed entry list. Suggestions count Unicode scalar edits, include distance two and break equal-distance ties by registry order; boundary witnesses distinguish these choices without re-running an allocating distance algorithm in the suggestion predicate. Filing appends to one declaration key without replacing its earlier entries. An attribute record retains producer-supplied metadata; it does not itself authenticate a source span or validate a payload in an unheld value arena.

An admitted attribute is filed under the content identity of the declaration form it decorates. At the top level every attribute block is a form of its own standing before that declaration ([the grammar](../../surface-grammar/README.md#an-attribute-block-is-a-form-of-its-own)), and the collector carries the blocks it meets to the next declaration, a definition or a data declaration alike, so the identity excludes the attributes: adding, editing or removing one re-keys nothing. A block before no declaration — at the end of the module, or before an import or a module — refuses the module. A module member keeps its blocks inside its form, and its identity covers them.

The alternative was folding a definition's blocks into its form, which keys the definition by its attributes and, with the standalone block a data declaration takes, ties the two readings of every `@[` until the token after `]`. Two top-level declarations written alike share an identity and so one entry list; both declare one name, so the second is refused as a duplicate. Reversal: when two declarations written alike must keep separate entries, the key gains the declaration's position.

An attribute is filed whatever its declaration's outcome: a refused declaration still has its tree and its key, and an expectation about a refusal — `refuses` — can only be read off the declaration that refused. Its payload is minted for the same reason, the one part of a refused declaration that lowers. A declaration form whose own tiles fault records no half, and its attributes are not filed.

The alternative was to file attributes for unrefused declarations only. It was declined because it leaves every lowering refusal unexpectable: a fixture stating the refusal it expects would be read as stating nothing. Reversal: none while an attribute can state an expectation about its declaration's refusal.

## Documentation: one text, its links checked

A declaration's documentation is every `NodeLabel::Doc` the parser grouped inside the attribute blocks that decorate it or before its name: `///` runs and `doc("…")` entries alike, in source order. A run reads as its lines with the `///` and one following space removed, joined by line breaks; an entry reads as its string literal decoded; the pieces join by line breaks. `LoweredModule::documentation` answers it under the content identity of the declaration form, the key the attribute table uses, and the parser keeps documentation out of that identity, so documenting a declaration re-keys nothing. Documentation inside a body, before a constructor say, is not read.

A link is a bracketed name, `[name]` or ``[`name`]``, a dotted path included, as an intra-doc link is in rustdoc: a bracket pair followed by `(`, `[` or `:` is a Markdown link or reference instead, and a bracket inside a code span is text. A link resolves as a name written in the source does, as a declared path, any declared name, a module or a constructor, and one nothing answers refuses its declaration as `UnresolvedDocLink` at the linked name, so renaming or deleting a declaration breaks the documentation that names it where the link is written.

The alternative was storing documentation as an attribute entry with a text payload. It was declined because an entry's payload is minted into the core arena and the attribute table carries no source borrow, while a link names the source it was written in. A broken link refuses its declaration because the lowering has no warning severity; reversal: when diagnostics carry a severity, a broken link is a warning and the declaration lowers.
