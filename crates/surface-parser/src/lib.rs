//! The **gandr surface parser**: source text in, a molded
//! [`SyntaxTree`](gandr_surface_syntax::SyntaxTree) and its completion
//! obligations out.
//!
//! - [`label()`] splits a source into lexemes, losslessly: every byte belongs
//!   to exactly one token, layout included.
//! - [`Molder`] chooses each token's mold from the grammar's candidates, the
//!   one whose completion obligations are least. Candidates that push alike and
//!   tied openers whose windows read alike share one dry run, by classes read
//!   off the grammar's tile automaton (the `tables` module states the shape and
//!   the decision); [`MoldVerdicts`] keeps the dry runs per candidate as the
//!   oracle the differential witness reads them against.
//! - [`MeldState`] is the resumable push machine over the checked grammar:
//!   `push` is total, a batch parse is the fold of `push` followed by
//!   [`commit`](MeldState::commit), and [`Checkpoint`] snapshots resume
//!   anywhere.
//! - [`Oblig`], [`ObligationInstance`] and [`Delta`] are the completion
//!   obligations: the material a partial parse is missing, ordered by severity.
//! - [`parse()`] runs the three over one source; [`FormSplit`] runs them over
//!   one source's top-level forms apart and joins them into the same parse.
//!
//! Each module's documentation states its part of the design, with the
//! alternatives each decision was chosen over.
//!
//! # No recursion over input
//!
//! Every walk over caller-controlled input is a loop over an explicit worklist
//! or the slope: collapse picks the highest reducible cell — an operator or an
//! open form — until none remains above its floor, so a form's content is
//! reduced before the form is force-closed, and closing a form wraps a
//! contiguous run of cells. The `recursion_forbidden` lint holds the crate to
//! it. Nested input therefore costs heap, never stack.
//!
//! # The corpus every molding is checked against
//!
//! The language's sources live in `gandr-surface-corpus`
//! (`crates/surface-corpus/`), under its strict root and its fixture root.
//! `tests::acceptance::corpus_molds_to_zero_obligations` reads every one of
//! them and requires each to mold to zero obligations; the parse-totality,
//! minimization and latency tests read the same set. No count is pinned: the
//! corpus grows and shrinks with the language, and the corpus crate's runner
//! reports how many sources each root holds. `tests/fixtures/` holds two
//! incomplete sources that must carry obligations.
//!
//! # Grammar contracts witnessed by a parse
//!
//! Five of the grammar's contracts can only be witnessed by parsing: that each
//! type operator the precedence table declares right-associative chains
//! cleanly, the value function space `=>` among them, that every
//! recursion-marker instantiation parses cleanly, that a chain mixing
//! incomparable set operators is refused a clean reading, that every spelling
//! of the universe reads cleanly wherever a type stands, and that every
//! spelling of a type operator — the static abstraction, its application, the
//! unary and n-ary `=>` — reads cleanly as a declared type, a definition's
//! value and an operator's argument, beside a case arm's `=>`. They live here,
//! in `tests::grammar`, because the dependency runs from this crate to the
//! grammar; the grammar's own suite keeps the contracts it can state without a
//! parser.
//!
//! # Specification evidence
//!
//! Executable predicates cover constant constructors and class rankings,
//! scanner decisions, candidate ordering, slope and cache transitions,
//! rollback, completion queries, source agreement and checkpoint fields. Each
//! nontrivial item states its adequacy domain and names local witnesses. Closed
//! wire-tag vocabularies and byte classes have exhaustive finite witnesses;
//! scanner modes, precedence and repair transitions use discriminating
//! examples; generated source and stream properties remain sampled evidence.
//! Run the predicates with `RUSTFLAGS="--cfg anodized_panic" cargo test -p
//! gandr-surface-parser --all-targets`.
//!
//! Grammar predicates preserve logarithmic successor and adjacency lookups:
//! successor minimality is checked by edge membership and the immediately
//! preceding adjacency. They do not scan the whole grammar on each speculative
//! completion.
//!
//! The witnesses do not establish universal malformed-input totality. A
//! trailing escape in a quoted shell assignment can advance past the source;
//! batch parsing then refuses source agreement. Checkpoint counts also lack
//! allocation bounds, so a maximal encoded count can panic before a typed
//! decoder refusal. These are runtime limits, not exemptions from the intended
//! losslessness and decoder contracts.
//!
//! # References
//!
//! - David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic
//!   Completions with Material Obligations." _Proceedings of the ACM on
//!   Programming Languages_ 9, OOPSLA2 (2025).
//!   <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — molds, grout, the
//!   meld calculus and its push rules, the obligation-minimizing molder, and
//!   the traces the contract suite replays.
//! - tylr, the Hazel structure editor's parser. <https://github.com/hazelgrove/tylr>
//!   — the obligation taxonomy and `Delta.compare`, whose order `Delta` ports.

// Module documentation that predates the shape lint: 34 headings outside the
// vocabulary, 24 decision records, 1 issue reference and 11 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod closing;
mod label;
mod meld;
mod mold;
mod oblig;
mod parse;
mod spec;
mod tables;
#[cfg(test)]
mod testing;

pub use crate::closing::Closing;
pub use crate::closing::ClosingLimit;
pub use crate::closing::LeadingSlot;
pub use crate::closing::Step;
pub use crate::closing::TileSpelling;
pub use crate::closing::closings;
pub use crate::closing::tile_spelling;
pub use crate::label::Labeling;
pub use crate::label::Lexeme;
pub use crate::label::Token;
pub use crate::label::WORD_PATTERN;
pub use crate::label::label;
pub use crate::meld::BoundarySlot;
pub use crate::meld::Checkpoint;
pub use crate::meld::CheckpointBytes;
pub use crate::meld::CheckpointBytesRef;
pub use crate::meld::CheckpointError;
pub use crate::meld::Completion;
pub use crate::meld::CompletionStatus;
pub use crate::meld::Continuations;
pub use crate::meld::DeclarationStart;
pub use crate::meld::Expected;
pub use crate::meld::FormContinuation;
pub use crate::meld::FormUnit;
pub use crate::meld::Frontier;
pub use crate::meld::HeadForm;
pub use crate::meld::HeadOperandPresence;
pub use crate::meld::Mark;
pub use crate::meld::MeldError;
pub use crate::meld::MeldState;
pub use crate::meld::MoldAdmissibility;
pub use crate::meld::MoldedTile;
pub use crate::meld::OpenFormPresence;
pub use crate::meld::OperandContinuation;
pub use crate::meld::ParkedUnit;
pub use crate::meld::SeamBreak;
pub use crate::meld::SpaceText;
pub use crate::meld::TileText;
pub use crate::meld::UnitBase;
pub use crate::meld::UnitSeam;
pub use crate::meld::declaration_head;
pub use crate::mold::CandidateLabel;
pub use crate::mold::DisagreementCount;
pub use crate::mold::MoldVerdicts;
pub use crate::mold::Molder;
pub use crate::mold::TokenIndex;
pub use crate::mold::TokenLabels;
pub use crate::mold::TokenRun;
pub use crate::mold::TokenText;
pub use crate::mold::candidate_labels;
pub use crate::oblig::Delta;
pub use crate::oblig::DeltaEmptyStatus;
pub use crate::oblig::OBLIG_CLASS_COUNT;
pub use crate::oblig::Oblig;
pub use crate::oblig::ObligClassIndex;
pub use crate::oblig::ObligationCount;
pub use crate::oblig::ObligationInstance;
pub use crate::parse::FormIdentity;
pub use crate::parse::FormJoin;
pub use crate::parse::FormSplit;
pub use crate::parse::ParseCleanStatus;
pub use crate::parse::ParseResult;
pub use crate::parse::Unlayable;
pub use crate::parse::parse;
pub use crate::parse::parse_by_form;
