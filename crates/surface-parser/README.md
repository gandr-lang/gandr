# gandr-surface-parser

The gandr surface parser: source text in, a molded syntax tree and its completion obligations out — a lossless labeler, a molder choosing each token's mold by the obligations it would leave, and a resumable push-machine melder over the checked grammar.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `label` splits a source into lexemes, losslessly: every byte belongs to exactly one token, layout included, and a byte no lexeme claims is an `Unknown` token rather than an error. `Molder` gives each token a mold — a tile of the checked grammar `gandr-surface-grammar` builds — choosing among the token's candidates the one whose completion obligations are least. `MeldState` is the push machine over that grammar: `push` is total, `commit` closes the input and builds a `gandr-surface-syntax` tree, `checkpoint` and `resume` continue a parse anywhere, and `finalize` reports what would complete it. `Oblig`, `ObligationInstance` and `Delta` are the completion obligations: the material a partial parse is missing, each with its class and span, ordered by severity. `parse` composes the three.

**Why.** An editor, a REPL and a batch checker all meet partial programs. A parser that stops at the first error gives each of them less than it has: no tree past the error, and one diagnostic where several independent gaps exist. A parser that completes every input with explicit, located, ranked material gives every consumer a whole tree and the full list of what the source still owes, and the batch checker reads "no obligations" as "well-formed".

**How.** The labeler is a hand-written total scanner. The molder enumerates a token's candidate molds from the grammar's per-label menus, discards those the slope head cannot admit, and dry-runs the survivors inside a mark/rollback transaction, keeping the least obligation delta with a deterministic tie-break. The melder is the paper's first-order push machine: Shift, Reduce and Degrout over one slope of cells, with grout at the bottom of the precedence order so every push concludes, and every emission appended to a log that `commit` replays into a level-order arena.

## Provided features

- `label`, `Token` and `Lexeme`: the total lossless labeler. Witnesses: `label::tests::span_tiling_is_total_and_gapless`, `label::tests::stray_bytes_are_unknown_never_a_panic`, `label::tests::multi_byte_operators_munch_maximally`, `label::tests::bridge_tiles_end_where_their_letter_does`.
- `Labeling`: a source's tokens with where the labeler stood within a mode, and `Labeling::relabel`, the labeling of an edit made from the unedited source's by scanning only around the edit. Witnesses: `label::tests::an_edit_relabels_as_the_edited_source_labels`, `label::tests::a_relabel_restarts_before_what_a_token_read`.
- `Molder`, `candidate_labels`, `TokenLabels`, `CandidateLabel` and `TokenText`: per-token mold choice by least obligation delta, deterministic across runs. Witnesses: `mold::tests::picks_the_obligation_minimum_mold`, `mold::tests::molding_is_deterministic_across_runs`, `mold::tests::unmoldable_token_takes_the_unmolded_path`.
- `TokenIndex`, `TokenRun`, `Molder::mold_run` and `Molder::form_runs`: a stream molded run by run, each run reading past its end as lookahead, and the runs a stream splits into at its predicted top-level declaration boundaries. Witnesses: `mold::tests::runs_mold_as_the_whole_stream`, `parse::tests::a_source_splits_before_each_declaration_head`.
- `MeldState`, `MoldedTile`, `TileText`, `SpaceText` and `MeldError`: the total push machine and its commit into a molded tree. Witnesses: `meld::tests::infix_reduces_after_precedence`, `meld::tests::brackets_close_on_the_matching_delimiter`, `meld::tests::a_bracket_before_a_required_tail_keeps_its_form_open`, `meld::tests::a_foreign_source_is_refused_at_commit`, `tests::contracts::arbitrary_real_mold_streams_parse_totally`, `tests::contracts::trace_precedence_climbs_like_figure_23`.
- Comment placement: `commit` makes each comment a child of the node it describes, and leaves whitespace and a shebang under the root. Witnesses: `meld::tests::each_comment_is_owned_by_the_node_it_describes`, `tests::acceptance::comments_reach_no_digest_and_lose_no_byte`.
- Documentation grouping: `///` runs and `doc("…")` entries become `NodeLabel::Doc` nodes that no digest reads, owned by the form they document. Witnesses: `meld::tests::documentation_reaches_no_digest`, `meld::tests::a_doc_run_documents_the_form_below_it`, `meld::tests::a_malformed_doc_entry_stays_an_attribute`.
- `Frontier`, `MoldAdmissibility`, `FormContinuation`, `OperandContinuation`, `HeadOperandPresence` and `OpenFormPresence`: the slope-head queries the molder ranks candidates by. Witnesses: `meld::tests::admits_a_form_first_mid_at_a_fresh_slot`, `meld::tests::admits_rejects_a_stray_closer`, `meld::tests::expected_sort_reads_the_open_slot`.
- `Completion`, `CompletionStatus` and `Expected`: the non-destructive completion query, its material running from the slope head down, and `Completion::innermost`, the material that closes the innermost open form. Witnesses: `meld::tests::finalize_is_non_destructive`, `meld::tests::finalize_charges_a_required_tail_only_when_it_is_absent`, `meld::tests::finalize_closes_each_frontier_at_its_innermost_material`, `closing::tests::each_form_closes_at_its_cheapest_material`, `tests::acceptance::expected_agrees_with_committed_finalize`, `tests::acceptance::expected_completion_names_the_next_tile_or_hole`.
- `MeldState::continuations`, `Continuations`, `HeadForm`, `closings`, `Closing`, `ClosingLimit`, `Step` and `LeadingSlot`: the menu an inline completion offers — the hole the operator nearest the slope head owes, and the cheapest closings of the innermost open form from every reading of its tile, each a path of tiles and the holes between them, an empty bracket pair holding the hole its grammar admits. Witnesses: `closing::tests::closings_offer_each_path_cheapest_first`, `meld::tests::continuations_name_the_pending_hole_and_the_frontier`.
- `tile_spelling` and `TileSpelling`: how an expected tile is written, its text or the lexical class whose token fills it. Witness: `closing::tests::every_label_a_token_offers_is_spelled_as_it_reads`.
- `Checkpoint`, `CheckpointBytes`, `CheckpointBytesRef`, `CheckpointError` and `Mark`: serializable continuation and in-place transaction. Witnesses: `meld::tests::checkpoint_resume_is_equivalent`, `meld::tests::minted_close_round_trips_and_refuses_unknown_class`, `meld::tests::mark_rollback_restores_state_exactly`, `tests::contracts::checkpoint_resume_equals_uninterrupted`.
- `Oblig`, `ObligationInstance`, `Delta`, `DeltaEmptyStatus`, `ObligClassIndex`, `ObligationCount` and `OBLIG_CLASS_COUNT`: the completion-obligation taxonomy and its minimization order. Witnesses: `oblig::tests::severity_ladder_is_low_to_high`, `oblig::tests::higher_severity_class_dominates_the_order`, `oblig::tests::minimization_never_prefers_ambiguous_prec`.
- `parse`, `ParseResult` and `ParseCleanStatus`: the batch entry point. Witnesses: `tests::acceptance::corpus_molds_to_zero_obligations`, `parse::tests::parse_is_lossless_and_hash_stable`, `parse::tests::arbitrary_source_parses_totally`.
- `parse_by_form`, `FormSplit`, `FormJoin`, `FormUnit`, `UnitBase`, `UnitSeam` and `SeamBreak`: one source parsed by its top-level forms, each form molded apart from a form-boundary checkpoint and joined into the whole parse. Witnesses: `parse::tests::form_split_parses_as_the_whole_source`, `parse::tests::a_source_splits_before_each_declaration_head`, `parse::tests::arbitrary_source_parses_by_form_as_whole`.
- `FormUnit::park`, `FormUnit::resume`, `ParkedUnit`, `FormSplit::identity` and `FormIdentity`: a molded form kept apart from the source it was molded in, and taken up into another revision whose run spells the same identity. Witnesses: `parse::tests::a_parked_unit_joins_as_the_unit_it_parked`, `parse::tests::an_equal_identity_molds_an_equal_unit`, `parse::tests::hostile_edits_reuse_only_equal_units`, `meld::tests::a_parked_unit_keeps_whether_it_reached_its_stand_in`, `mold::tests::a_run_reads_eight_significant_tokens_past_its_end`.

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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Completion obligations in place of error recovery, not typing obligations | [`oblig`](src/oblig.rs) |
| Label, mold, meld; commit reads the caller's source; forms as units | [`parse`](src/parse.rs) |
| The molder's search and its tie rules | [`mold`](src/mold.rs) |
| Mid tiles, required tails, the committed tree, checkpoints, repair at the declaration boundary | [`meld`](src/meld.rs) |
| The completion query is a bound | [`closing`](src/closing.rs) |
| No recursion over input, the corpus, grammar contracts, specification evidence, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
