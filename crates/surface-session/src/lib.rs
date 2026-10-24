//! The interactive session above the dispatcher: each revision of one source
//! lowered, judged, resumed through the incremental checker and persisted.
//!
//! A [`Session`] holds what the batch pipeline does not: the form store of the
//! latest parsed revision, the incremental checker's latest resume, the
//! checkpoint store it persists into, and the import scope of the latest
//! accepted revision. Its faces — the REPL, the language server, a terminal
//! interface — read it; it reads none of them.
//!
//! # A submission is a whole revision the caller owns
//!
//! [`Session::submit`] takes the full text of a revision and returns a
//! [`Submission`] borrowing it. The session keeps no text: a face that
//! accumulates lines, or applies an editor's changes, owns the buffer and
//! submits it whole.
//!
//! # The form store parses only the forms an edit touched
//!
//! The session keeps every top-level form of the latest parsed revision,
//! molded and parked under its identity — the exact spelling of everything
//! its molding reads. A revision takes up each form whose identity the store
//! holds and molds the rest across the session's width, so an edit molds the
//! forms it changed and the few whose lookahead reaches into it, and the
//! joined parse equals the whole parse of the revision. [`Submission::forms`]
//! counts them.
//!
//! # A readmission resumes the declarations a revision leads with
//!
//! A document that imports a sibling is judged laid out after its import
//! closure, and the kernel readmits the closure's declarations with its own.
//! [`Session::admit`] resumes that readmission from the longest run of
//! leading declarations the process holds for the same closure, or the
//! session holds past it — its text selects the candidate, the run's
//! checkpoints compared pointwise with the latest resume's admit it — and
//! records its own run for the next admission as far as its revision leads
//! with the one admitted before. An edit to the document's own text offers
//! the kernel its own declarations from the first one it changed, a revision
//! that changes none offers none, and [`Admitted::crossed`] counts them. The
//! stores are the `closures` module's.
//!
//! # The report is the dispatcher's composition
//!
//! A submission lowers its parse with the dispatcher's
//! [`lower_parsed`](gandr_surface_dispatcher::lower_parsed), then runs
//! [`judge_module`](gandr_surface_dispatcher::judge_module) — the two halves
//! of the composition — so its verdicts are exactly the ones `gandr check`
//! gives the same text, and hands the same lowered declarations, through
//! [`program`], to the incremental checker, which adopts what still answers
//! and persists the checkpoints.
//!
//! # An edit judges what its supports touch
//!
//! The resume is held to zero drift against a from-scratch judgement of the
//! same text. After each accepted edit the resumed checkpoints — content,
//! footprint, consulted answers and typing — are the ones a fresh session
//! records for the text, and the items judged are exactly those the two
//! support logs separate: an item is adopted when the previous resume holds a
//! checkpoint of its content whose consulted answers are the ones the fresh
//! judgement records, and judged otherwise. The same text submitted again
//! judges no item, molds no form, and composes the same report and kernel
//! manifest.
//!
//! # Edits are reconstructed from the lowered core
//!
//! Each accepted [`Submission`] carries the [`EditScript`] from the latest
//! accepted revision before it: [`diff`] of their [`Snapshot`]s, the id-free
//! image of each revision's lowered core. The session keeps the latest
//! snapshot, so a face localizes a source range against it with
//! [`Snapshot::localize`].
//!
//! # A hole-free item is evaluated
//!
//! [`Submission::evaluate`] runs one declaration of the revision on the
//! dispatcher's run stage — the [`Program`](gandr_surface_dispatcher::Program)
//! the composition built — when the checker accepted it whole: a declaration
//! owed its body is a hole and declines, and so does a refused one. A run that
//! reaches a goal is blamed on it rather than declined, because the item run
//! has no hole of its own.
//!
//! # A declaration's type is read off the latest resume
//!
//! [`type_of`] spells the type the latest resume gives a declaration at the
//! caller's page width — its signature, its synthesised type or its declared
//! universe — so every face names a declaration's type in the same words. The
//! type of a node inside a declaration is not the session's: a face reads it
//! off the dispatcher's type table, whose entries come from the typed run, the
//! description route's types for `theory` and `data` members, and the universes
//! of the written types the run formed.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! # A crate of its own, above the dispatcher
//!
//! The session owns incremental state and checkpoints the batch pipeline has no
//! use for, and three faces read it. It sits in `surface` after the dispatcher
//! and the diagnostics renderer and depends on the dispatcher and below, never
//! on a face.
//!
//! The alternatives were the dispatcher, which would carry state its `check`
//! and `test` verbs never read, and the first face, which would leave the
//! second to duplicate it. The choice reverses if one face remains the only
//! reader; the session would then fold into it.
//!
//! # Contract evidence and its limits
//!
//! Nontrivial callable items carry executable `#[spec(...)]` predicates and
//! bounded adequacy witnesses. The predicates observe recorded state: ordered
//! rows, preserved payloads, exact absence reasons, source bounds, canonical
//! tree numbering, and session transitions. They do not repeat parsing,
//! callback invocation, evaluation, or storage effects. The private child
//! iterator exposes its borrowed position to its predicates; `DeclarationTree`
//! makes native declaration categories explicit in the snapshot API.
//!
//! Declarations with no callable boundary, opaque strategy constructors,
//! formatter sinks, best-effort cleanup, and the consumed-input differential
//! helper state precise executable exemptions. Their observable obligations are
//! exercised where the inputs and effects exist. Every exemption names that
//! boundary rather than treating a non-const comparison as an exemption.
//!
//! | Decision surface | Evidence and bounded domain | Rung |
//! | ---------------- | --------------------------- | ---- |
//! | Incremental reuse | Literal adoption and retyping fixtures, plus 200 generated edit chains; complete typings compared with a fresh checker. Over 200 chains of each of two generators — one of them retyping definitions that later ones read — the resumed checkpoints and the judged set are compared with a from-scratch session, the same text resubmitted, and the reach of adopted, new and retouched items asserted. | L2 |
//! | Corpus composition | Every source from both configured corpus roots compared with the walk; both paths share parsing and judgement. | L3 |
//! | Edit reconstruction | Literal actions, 200 generated revision pairs, and a hand-built dynamic tree; applying the diff reconstructs the new image. | L3 |
//! | Item alignment | All subset/permutation pairs of three references compared with exhaustive reference subsequences. | L2 |
//! | Localization | Descent compared with a linear span oracle on generated trees, including ties; visited-node bounds cover the measured shapes only. | L2 |
//! | Arena and origin boundaries | Missing item/body/child, unrecorded spans, absent roots of each sort, descendant hulls, and callback-once fixtures. | L3 |
//! | Session and evaluation | Exact report rows, import retention, attempt counts, missing/refused/holed eligibility, and concrete integer/thunk results. | L3 |
//! | Persistence and formatting | Real file-store reopen/cleanup, kernel readback, refusing checkpoint/block stores, and refusing output sinks. External failure modes beyond those fixtures are not claimed. | L3 |
//!
//! Diagnostics assert stable refusal categories and exact primary/context
//! spans, not title wording or golden report text. The obligation suites
//! preserve repair classes, loci, multiplicities, and ordering; agreement with
//! the same parser is transfer evidence, not an independent repair oracle. Goal
//! flags are compared with the corresponding checkpoint footprints.
//!
//! The generated source domain uses the supported scalar, declaration,
//! reference, and nullary-function forms. Hand-built arena fixtures cover core
//! child ordering without pretending those effect formers have surface syntax.
//! These finite witnesses do not establish universal diff soundness, typing
//! correctness, storage atomicity, or behavior of surface forms the grammar
//! cannot express.
//!
//! The choice is cheap executable boundary checks plus independent or literal
//! consumer observations. Re-running the full parser, evaluator, or store in a
//! postcondition would duplicate work and effects; opaque test strategies are
//! not sampled a second time. An exemption can be removed when the relevant
//! state has a non-consuming observer. Broader grammars or new decision
//! branches require broader witnesses, not a stronger claim about the samples
//! in hand.
//!
//! # References
//!
//! - Microsoft. "Language Server Protocol Specification, version 3.17." 2022. <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/>
//!   — full-document synchronisation, the shape a submission takes: the client
//!   owns the buffer and sends it whole.
//! - Porter et al. "Incremental Bidirectional Typing via Order Maintenance."
//!   arXiv:2504.08946, 2025. <https://arxiv.org/abs/2504.08946> — an
//!   incremental checker that consumes structured edit actions rather than
//!   text, the input edit reconstruction produces.
//! - Hunt, J. W., and Szymanski, T. G. "A Fast Algorithm for Computing Longest
//!   Common Subsequences." Communications of the ACM 20(5), 1977. — the
//!   reduction of a longest common subsequence over distinct keys to a longest
//!   increasing subsequence, which item alignment uses.

// Module documentation that predates the shape lint: 34 headings outside the
// vocabulary, 8 decision records, 1 issue reference and 9 budgets exceeded.
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
extern crate alloc;

mod closures;
mod edit;
mod forms;
mod item_source;
mod live_match;
mod lowerings;
mod session;
mod typed;

pub use crate::edit::Action;
pub use crate::edit::ChildSlot;
pub use crate::edit::CorePath;
pub use crate::edit::DeclarationTree;
pub use crate::edit::EditScript;
pub use crate::edit::InterfaceTree;
pub use crate::edit::ItemTree;
pub use crate::edit::Snapshot;
pub use crate::edit::SourceEdit;
pub use crate::edit::Tree;
pub use crate::edit::addressed;
pub use crate::edit::apply;
pub use crate::edit::body_path;
pub use crate::edit::diff;
pub use crate::edit::located;
pub use crate::edit::spanned;
pub use crate::forms::FormCensus;
pub use crate::forms::FormCount;
pub use crate::item_source::Revision;
pub use crate::item_source::RevisionFault;
pub use crate::item_source::SurfaceItems;
pub use crate::item_source::fault_span;
pub use crate::item_source::program;
pub use crate::live_match::MatchAnalysis;
pub use crate::live_match::MatchCheckpoint;
pub use crate::live_match::MatchRun;
pub use crate::live_match::MatchRunFault;
pub use crate::lowerings::Led;
pub use crate::session::Admitted;
pub use crate::session::CandidateIndex;
pub use crate::session::ClosureKey;
pub use crate::session::ClosureSlot;
pub use crate::session::Detached;
pub use crate::session::Holding;
pub use crate::session::ImportRow;
pub use crate::session::JudgedParse;
pub use crate::session::KernelCheckpoint;
pub use crate::session::Laying;
pub use crate::session::Persistence;
pub use crate::session::Ran;
pub use crate::session::Reopened;
pub use crate::session::Resumed;
pub use crate::session::Session;
pub use crate::session::SessionFault;
pub use crate::session::Submission;
pub use crate::session::Tables;
pub use crate::session::Trial;
pub use crate::session::admission;
pub use crate::session::admitted;
pub use crate::session::evaluate;
pub use crate::session::evaluation;
pub use crate::session::import;
pub use crate::session::imported;
pub use crate::session::reopened;
pub use crate::session::resumed;
pub use crate::typed::spelled;
pub use crate::typed::type_of;
