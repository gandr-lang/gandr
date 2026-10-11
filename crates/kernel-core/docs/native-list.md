# Native List former

How `gandr-kernel-core` forms, checks and computes with the built-in `List A`, its introductions and its pure right fold. The crate's [README](../README.md) states the rest of the crate.

<!-- toc -->
- [Typing and computation](#typing-and-computation)
- [The decision](#the-decision)
- [Witnesses](#witnesses)
<!-- tocstop -->

## Typing and computation

`List A` is a built-in finite former beside nominal data and records. Its introductions and pure right fold participate in ordinary declaration checking, readmission, encoding, substitution and normalization. They are not a Sum encoding and add no effects to the kernel.

| Former | Typing and computation |
| ------ | ---------------------- |
| `List A` | Forms at the universe level of `A`; conversion compares element types. |
| `nil` | Checks at any expected `List A`; does not synthesize an element type. |
| `cons head tail` | Checks `head : A` and `tail : List A`; malformed tails and Sum injections refuse. |
| `fold[A, B] list on_nil on_cons` | Forms both annotations, checks `list : List A`, and synthesizes `F B`. The empty branch checks at `F B` in the ambient context. The cell branch checks beneath `head : A` then `folded : B`, with capture-avoiding shifts of the ambient types. Nil reduces to `on_nil`; cons folds its tail before entering `on_cons`. |

The two cell binders are ordered: folded result is index zero, head is index one. Substitution protects both binders and any outer context. A neutral list retains its fold rather than fabricating a result. Checking and replay use the existing iterative machines, not recursive host-language list ownership.

## The decision

**Choice.** Complete the already represented List former instead of translating it into sums or nominal declarations. The kernel needs no host operations or effect rows for this eliminator. **Reversal.** Dependent motives or general strictly positive descriptions require their own formation, binding and replay rules; neither is implied by this pure fold.

## Witnesses

The `native_list_introductions_and_fold_check` and `native_list_fold_reduces_without_capturing_outer_variables` witnesses exercise native typing, refusals and reduction. Core readmission and normalization witnesses run with and without specification enforcement. The [wire table](../../kernel-term/README.md#tag-numbering-and-versioning) assigns the persisted syntax.
