# gandr-surface-parser

The gandr surface parser: source text in, a molded syntax tree and its completion obligations out — a lossless labeler, a molder choosing each token's mold by the obligations it would leave, and a resumable push-machine melder over the checked grammar.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Completion obligations in place of error recovery](#completion-obligations-in-place-of-error-recovery)
- [Completion obligations are not typing obligations](#completion-obligations-are-not-typing-obligations)
- [Label, mold, meld](#label-mold-meld)
- [A closer with a required operand after it is a mid tile](#a-closer-with-a-required-operand-after-it-is-a-mid-tile)
- [The tree the melder commits](#the-tree-the-melder-commits)
- [The completion query is a bound](#the-completion-query-is-a-bound)
- [Checkpoints](#checkpoints)
- [Commit reads the caller's source](#commit-reads-the-callers-source)
- [Repair stops at the declaration boundary](#repair-stops-at-the-declaration-boundary)
- [No recursion over input](#no-recursion-over-input)
- [The corpus every molding is checked against](#the-corpus-every-molding-is-checked-against)
- [Grammar contracts witnessed by a parse](#grammar-contracts-witnessed-by-a-parse)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `label` splits a source into lexemes, losslessly: every byte belongs to exactly one token, layout included, and a byte no lexeme claims is an `Unknown` token rather than an error. `Molder` gives each token a mold — a tile of the checked grammar `gandr-surface-grammar` builds — choosing among the token's candidates the one whose completion obligations are least. `MeldState` is the push machine over that grammar: `push` is total, `commit` closes the input and builds a `gandr-surface-syntax` tree, `checkpoint` and `resume` continue a parse anywhere, and `finalize` reports what would complete it. `Oblig`, `ObligationInstance` and `Delta` are the completion obligations: the material a partial parse is missing, each with its class and span, ordered by severity. `parse` composes the three.

**Why.** An editor, a REPL and a batch checker all meet partial programs. A parser that stops at the first error gives each of them less than it has: no tree past the error, and one diagnostic where several independent gaps exist. A parser that completes every input with explicit, located, ranked material gives every consumer a whole tree and the full list of what the source still owes, and the batch checker reads "no obligations" as "well-formed".

**How.** The labeler is a hand-written total scanner. The molder enumerates a token's candidate molds from the grammar's per-label menus, discards those the slope head cannot admit, and dry-runs the survivors inside a mark/rollback transaction, keeping the least obligation delta with a deterministic tie-break. The melder is the paper's first-order push machine: Shift, Reduce and Degrout over one slope of cells, with grout at the bottom of the precedence order so every push concludes, and every emission appended to a log that `commit` replays into a level-order arena.

## References

- David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (2025). <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — molds, grout, the meld calculus and its push rules, the obligation-minimizing molder, and the traces the contract suite replays.
- tylr, the Hazel structure editor's parser. <https://github.com/hazelgrove/tylr> — the obligation taxonomy and `Delta.compare`, whose order `Delta` ports.

## Provided features

- `label`, `Token` and `Lexeme`: the total lossless labeler. Witnesses: `label::tests::span_tiling_is_total_and_gapless`, `label::tests::stray_bytes_are_unknown_never_a_panic`, `label::tests::multi_byte_operators_munch_maximally`, `label::tests::bridge_tiles_end_where_their_letter_does`.
- `Molder`, `candidate_labels`, `CandidateLabel` and `TokenText`: per-token mold choice by least obligation delta, deterministic across runs. Witnesses: `mold::tests::picks_the_obligation_minimum_mold`, `mold::tests::molding_is_deterministic_across_runs`, `mold::tests::unmoldable_token_takes_the_unmolded_path`.
- `MeldState`, `MoldedTile`, `TileText`, `SpaceText` and `MeldError`: the total push machine and its commit into a molded tree. Witnesses: `meld::tests::infix_reduces_after_precedence`, `meld::tests::brackets_close_on_the_matching_delimiter`, `meld::tests::a_bracket_before_a_required_tail_keeps_its_form_open`, `meld::tests::a_foreign_source_is_refused_at_commit`, `tests::contracts::arbitrary_real_mold_streams_parse_totally`, `tests::contracts::trace_precedence_climbs_like_figure_23`.
- `Frontier`, `MoldAdmissibility`, `FormContinuation`, `OperandContinuation`, `HeadOperandPresence` and `OpenFormPresence`: the slope-head queries the molder ranks candidates by. Witnesses: `meld::tests::admits_a_form_first_mid_at_a_fresh_slot`, `meld::tests::admits_rejects_a_stray_closer`, `meld::tests::expected_sort_reads_the_open_slot`.
- `Completion`, `CompletionStatus` and `Expected`: the non-destructive completion query. Witnesses: `meld::tests::finalize_is_non_destructive`, `meld::tests::finalize_charges_a_required_tail_only_when_it_is_absent`, `tests::acceptance::expected_agrees_with_committed_finalize`, `tests::acceptance::expected_completion_names_the_next_tile_or_hole`.
- `Checkpoint`, `CheckpointBytes`, `CheckpointBytesRef`, `CheckpointError` and `Mark`: serializable continuation and in-place transaction. Witnesses: `meld::tests::checkpoint_resume_is_equivalent`, `meld::tests::minted_close_round_trips_and_refuses_unknown_class`, `meld::tests::mark_rollback_restores_state_exactly`, `tests::contracts::checkpoint_resume_equals_uninterrupted`.
- `Oblig`, `ObligationInstance`, `Delta`, `DeltaEmptyStatus`, `ObligClassIndex`, `ObligationCount` and `OBLIG_CLASS_COUNT`: the completion-obligation taxonomy and its minimization order. Witnesses: `oblig::tests::severity_ladder_is_low_to_high`, `oblig::tests::higher_severity_class_dominates_the_order`, `oblig::tests::minimization_never_prefers_ambiguous_prec`.
- `parse`, `ParseResult` and `ParseCleanStatus`: the batch entry point. Witnesses: `tests::acceptance::corpus_molds_to_zero_obligations`, `parse::tests::parse_is_lossless_and_hash_stable`, `parse::tests::arbitrary_source_parses_totally`.

## Expected features

- **A checked grammar.** Every entry point takes a `Pbg` from `gandr-surface-grammar`; the built-in surface is `built_in()`. A tree records the grammar's fingerprint, and a consumer resolves the tree's mold ids against that grammar alone.
- **The source outlives the tree.** A committed tree borrows the text it spans; the caller keeps the `SourceText` alive for as long as it reads the tree.
- **A checkpoint resumes under its own grammar and revision.** `Checkpoint::fingerprint` names the grammar a snapshot was taken under; pairing it with the right grammar is the caller's, and the byte stream carries no version, so a stream written by one revision of this crate is read by that revision only.
- **`alloc`.** The crate is `no_std` with `alloc`; its tests link `std` for files and timing.

## Examples

```rust
use gandr_surface_grammar::built_in;
use gandr_surface_parser::Oblig;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

fn main() -> Result<(), Box<dyn core::error::Error>> {
    let pbg = built_in()?;

    let whole = parse(&pbg, SourceText::from("def answer = 42;"))?;
    assert!(bool::from(whole.is_clean()));

    // An unclosed group still yields a tree; the missing `)` is an obligation.
    let partial = parse(&pbg, SourceText::from("def answer = ( 42 ;"))?;
    assert!(
        partial
            .obligations()
            .iter()
            .any(|obligation| obligation.class == Oblig::MissingTile)
    );
    Ok(())
}
```

The same example is the doctest on `parse`.

## Completion obligations in place of error recovery

The parser is total: every input yields a tree, and every place the source falls short of the grammar carries a completion obligation — a closed class, from `MissingMeld` (an operand absent) through `MissingTile`, `IncompleteTile`, `UnmoldedTok`, `InconMeld`, `ExtraMeld` and `ReservedKeyword` to `AmbiguousPrec` (two operators with no declared precedence between them), and the span it stands at. The classes are declared in severity order, so `derive(Ord)` is the ladder; `Delta` counts per class and compares from the most severe class down, net change before gross insertion, so the molder never chooses a reading that adds an ambiguity when one without exists. `ParseResult::obligations` lists them most severe first.

The alternative was a parser that refuses: stop at the first ungrammatical token with a typed `ParseRefusal` naming it, as a minimal parse-and-check pipeline needs, with no operator handling and no completion. It is smaller, and it is all a batch checker reads. It was declined because a refusal is derivable from the obligations — the most severe one, with its span — while the obligations are not derivable from a refusal, and because the editor and the REPL need the tree past the first gap. Reversal: if a consumer needs refusal semantics that the obligation list cannot express, such as refusing on a class the parser would complete, that consumer maps obligations to its refusal; the parser keeps completing.

## Completion obligations are not typing obligations

Two different objects share the word. A completion obligation is produced here, by the parser, and says the source is missing material: a closer, an operand, a tile. A typing obligation is produced downstream, by elaboration, and says an artifact still owes a typing — a signature no definition completes. The taxonomy here is upstream of the typing-obligation ledger and does not feed it: a source with completion obligations is malformed or incomplete source, and nothing in this crate becomes a ledger entry. Reversal: none intended; a consumer that wants to show parse gaps beside typing goals maps them explicitly at its own boundary.

## Label, mold, meld

The labeler classifies lexemes and stops there. A lowercase word could be an identifier, a type variable or a keyword; an uppercase word a constructor, a type name or a primitive; `-` a prefix or an infix operator. Which one is decided by the molder, in context, never by the labeler — teaching the labeler grammar would duplicate the grammar and drift from it. Multi-byte operators munch longest first, so the shorter tiles `->`, `<-`, `==` and `<=` never shadow the circuit arrows `-->`, `<->`, `==>` and `<=>` that extend them. The bridges `+U` and `-F` are one tile each only where the letter ends, so `+Unit` stays a sign and a word and the sum keeps its spellings. Shell blocks, strings and interpolations switch the labeler into their own lexical modes.

The molder's candidates for a token are the union of the grammar's molds for each label the token could carry, visited in ascending `MoldId` order. The pre-filter drops every candidate the slope head cannot admit — a closer with no matching open form, an operator with no left operand — and most tokens are left with one, taken without a dry-run. The survivors are dry-run in a `Mark` / `rollback_to` transaction and ranked by their obligation delta, then form continuation, then sort compatibility, then the completion cost `finalize` reports, then the smaller `MoldId`; a bounded lookahead settles the families whose openers tie and diverge only at a later tile. Nothing process-dependent reaches the choice, so molding is a function of the token stream.

The melder follows the paper's push rules. Shift pushes a tile whose precedence the head yields to; Reduce closes the head operator or form when the incoming tile takes precedence; Degrout completes an incomparable pair with grout and an `AmbiguousPrec` obligation. Grout is comparable to everything and sits at the bottom of the precedence order, which is what makes every push conclude.

## A closer with a required operand after it is a mid tile

A tile with a same-form predecessor and no same-form successor ends its form in the paper's classification. The `]` of `+U[ω] C` and of `package [ T ] C` cannot: the grammar requires an operand after it. The melder classifies such a tile as a mid tile, so the form stays open until its operand arrives and closes around it; a closing bracket with nothing required after it, the `]` of `Type[+, 1]`, still ends its form. Read as an end, the bracket closed the bridge at its grade, and a parenthesised operand after it became a juxtaposed sibling that the lowering refused as a malformed form.

The completion query and the molder follow. `finalize` charges no tile to a required-tail frontier whose operand is written or already opened, because the commit's force-close mints none there. The lookahead window settles and bounds each token at its declaration as the stream does, so a tied opener is judged on the frontier the stream would leave. Without them, the mid-tile bracket made `package [ T ] Integer;` followed by another declaration rank the package reading below an instantiation of a type variable named `package`.

The alternative was a grammar change: spell the graded bridge as a prefix operator whose operand is its argument, keeping the three-way classification. It splits one form into two and moves the grade off the bridge's tile, and `package [ T ]` would need the same split. Reversal: if a grammar form ever needs a closing bracket that ends it while an operand still follows, the tail moves into an enclosing form and this case becomes a grammar check.

## The tree the melder commits

`commit` replays the emission log into a `gandr-surface-syntax` `TreeBuilder`. A completed form is a `NodeLabel::Meld` named by the mold of the tile that opened it; an operator form is named by its operator's mold; a written tile is a `NodeLabel::Tile` with its mold. A missing operand is convex grout of the slot's sort; a missing closer is a `NodeLabel::GhostClose` when the grammar says every completion of the form ends at one family of closer, and postfix grout otherwise. A token no candidate molds is convex `Item` grout covering that token's bytes, so the tree stays lossless and the bytes reach the node's digest. Layout is a `NodeLabel::Space` leaf. The form a node realises is the grammar's answer for its mold (`Pbg::named_kind`), so this crate restates no list of forms.

## The completion query is a bound

`finalize` (and its interaction-surface name `expected`) reports the material and the obligations closing the input here would introduce, without mutating the state. It reads the slope as it stands rather than replaying the commit, so it is a bound: every obligation a commit inserts is among those it names, and its only excess is a `MissingMeld` for an operator whose operand is a form still open, which the commit's force-close then turns into that operand. The molder uses this cost as one of its ranking keys, so the bound is part of the molding the corpus sources check.

The alternative was an exact query: replay the commit on a copy of the slope. It costs a slope clone and a collapse per query, which the molder pays once per surviving candidate per token. Reversal: if a consumer needs the exact obligations at a prefix, it commits a checkpointed copy; if the molder's ranking ever needs exactness, the query replays, and the corpus sources say whether any molding moved.

## Checkpoints

A `Checkpoint` is the melder's whole state: the grammar fingerprint, the assembled source, the emission log, the slope, the buffered obligations and the layout tokens. `to_bytes` writes it little-endian with every variable-width field length-prefixed; a node label is written as its pinned digest tag and its payload, so the checkpoint and the digest share one numbering and reordering the label enum changes neither. A minted close's family byte is checked on read, and an unknown family is refused rather than defaulted, because pairing a ghost against the wrong family is worse than not pairing it. `resume` rebuilds the slope-head caches from the slope, and a resumed run equals the uninterrupted one, obligations and root digest included.

A `Mark` is the cheap transaction beside it: the buffer and log lengths and a copy of the slope with its head caches, restored in place, which is what the molder's per-candidate dry-run uses.

## Commit reads the caller's source

The melder assembles its own copy of the text from the tiles and layout pushed into it — it must, to stream — while a `gandr-surface-syntax` tree borrows the source it spans. `commit` therefore takes the caller's `SourceText`, checks that it is exactly the assembled text, and builds the tree over the caller's buffer; any other text is refused with `MeldError::SourceMismatch`, because it would mis-span every node.

The alternatives were a tree owning a copy of the text, which costs a copy per parse and makes every tree a second owner of its source, and a commit returning the assembled buffer beside a tree borrowing it, which is a self-referential pair. Reversal: if a consumer needs a tree that outlives its source, the syntax crate gains an owning variant and commit hands it the assembled buffer.

## Repair stops at the declaration boundary

When a token's candidates include a declaration head, none of them continues the open form, and the innermost open form is not an item form — an unclosed `(` in a definition's value, say — the melder force-closes the open forms back to the nearest declaration before molding the head, so the repair's minted closes and obligations stay inside the damaged declaration and the next one parses whole. The boundary is any declaration head, not the `def` keyword alone.

Known bound: a container whose own member carries the damage — `module M { def bad = ( 1 ; def good = 2; }` — force-closes the container too, so `good` becomes a sibling of `M` rather than its member. Telling a container apart from a declaration needs the rule a mold was numbered for, which the grammar now reads back (`Pbg::rule_of`) and this repair does not yet consult. Both declarations survive as distinct items; what the repair does not preserve is which one owns the later declaration. Reversal: when a consumer needs the member kept in its container, the boundary consults the rule.

## No recursion over input

Every walk over caller-controlled input is a loop over an explicit worklist or the slope: collapse picks the highest reducible cell — an operator or an open form — until none remains above its floor, so a form's content is reduced before the form is force-closed, and closing a form wraps a contiguous run of cells. The `recursion_forbidden` lint holds the crate to it. Nested input therefore costs heap, never stack.

## The corpus every molding is checked against

The language's sources live in `gandr-surface-corpus` (`crates/surface-corpus/`), under its strict root and its fixture root. `tests::acceptance::corpus_molds_to_zero_obligations` reads every one of them and requires each to mold to zero obligations; the parse-totality, minimization and latency tests read the same set. No count is pinned: the corpus grows and shrinks with the language, and the corpus crate's runner reports how many sources each root holds. `tests/fixtures/` holds two incomplete sources that must carry obligations.

## Grammar contracts witnessed by a parse

Four of the grammar's contracts can only be witnessed by parsing: that each type operator the precedence table declares right-associative chains cleanly, that every recursion-marker instantiation parses cleanly, that a chain mixing incomparable set operators is refused a clean reading, and that every spelling of the universe reads cleanly wherever a type stands. They live here, in `tests::grammar`, because the dependency runs from this crate to the grammar; the grammar's own suite keeps the contracts it can state without a parser.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
