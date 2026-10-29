//! The sequent tier of gandr's core: the command IL a call-by-push-value
//! program is focused into, the store a run's values are read back from, and
//! the vocabulary every run of a command answers in. In the storage picture
//! the [`Store`] is a LAM, a location-addressable memory of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`:
//! one append-only region per family, each value immutable at its location,
//! its [`HeapValueId`], which the store never recycles. A location proves
//! nothing, so the store stands behind no wall: validity was decided before
//! the run.
//!
//! - [`CommandArena`] holds producers, consumers and commands —
//!   [`ProducerNode`], [`ConsumerNode`], [`CommandNode`] — minted only over
//!   children it holds, with [`SequentWatermark`] and
//!   [`CommandArena::truncate_to`] the rollback a refused build takes.
//!   Covariables are de Bruijn indices ([`CovariableIndex`]); nothing mints a
//!   continuation name. A binder `μ̃x.c` carries an [`Independence`] mark that
//!   [`CommandArena::mark_independent`] sets, refusing with [`MarkRefusal`]: a
//!   run may start the writer of a marked binder before `c`, because the writer
//!   performs no operation. A truncation drops the marks of the binders it
//!   drops.
//! - [`focus_computation`], [`focus_value`], [`focus_top_value`] and
//!   [`focus_definition`] translate core terms into the IL, recording each
//!   created command's [`FocusOrigin`] in a [`Provenance`] table. A bind whose
//!   writer the caller names in [`Writers`] focuses as `⟨μα.𝓕⟦M⟧α |+ μ̃x.c⟩`,
//!   its binder marked. A bind inside an identity combinator's build is never
//!   marked, because its writer names a node of the combinator's own arena.
//!   [`unfocus_command`] and [`unfocus_value`] read the IL back, their left
//!   inverse.
//! - [`check_command`] is the typed-IL check: reference integrity, arity,
//!   focus, polarity and second-class closures, answering a command's
//!   [`FreeSet`].
//! - [`convert_step`], [`convert`] and [`convert_all`] convert a closure to an
//!   abstract closure, moving the context variables its code names into its
//!   environment one at a time; [`beta`] and [`enter_all`] enter a closure cut
//!   against a frame its code answers, refusing with [`ClosureRefusal`].
//! - [`render_command`], [`render_producer`] and [`render_consumer`] write the
//!   IL's notation.
//! - [`Store`] holds what a run moves out of its regions: immutable
//!   [`HeapValue`]s shared by address, over persistent [`Environment`] chains,
//!   a literal stack's bind frames each a [`ClosedCommand`].
//! - [`Outcome`] and [`Stuck`] say how a run ended — a value, or the named
//!   reason it stopped short of one — and [`Definitions`] holds the constants a
//!   run unfolds; `gandr-runtime-emitter` runs commands, natively or on the
//!   portable executor, and answers in these terms.
//! - [`read_back_terminal`] reads a run's answer back as a core term.
//! - [`stats`], [`origin_histogram`] and [`dump`] inspect a focused arena.
//! - [`reify_command`] reifies a ground cell pattern into the IL over a
//!   [`ConstructorResolver`].
//!
//! The crate is `no_std` and depends on `core`, `alloc`, the core language's
//! syntax, the kernel's leaf vocabularies and the cell substrate's
//! [`Polarity`](gandr_theory_cell_complexes::Polarity). Each module's
//! documentation states its mechanism and its decisions.
//!
//! # The differential against normalisation by evaluation
//!
//! `gandr-core-nbe` is the oracle: it evaluates the core itself, by closures
//! over a glued domain, and shares no step with the tiers. Each case in
//! `tests/differential.rs` runs both ways — native code where the host has a
//! patcher, the portable executor everywhere — and the tiers' terminal, read
//! back, is compared node for node with the normaliser's normal form. A
//! first-order answer agrees exactly. A run reads a suspended body back as
//! written, its environment substituted, where the normaliser reduces under
//! the binder, so a thunk or a function still holding a redex agrees once the
//! run's reading is normalised too; the hand-built cases pin which of the two
//! each answer needs, which shows the comparison telling terms apart. An
//! ill-typed redex stops both at the same elimination, a nominal match on
//! anything but a constructor it has a branch for included. Recursive
//! definitions over Nat, List and a Tree with a function field compute the same
//! answer on both. Over generated closed, well-typed computations every run
//! halts, the tiers read back alike, and the normalised reading is the normal
//! form.
//!
//! Outcome expectations live with the run verb `gandr run`, which lowers,
//! checks, focuses and runs a corpus source in one place: a corpus declaration
//! states `runs("…")`, and the dispatcher's corpus suite runs every one.
//! Outcome snapshots frozen from a run are not carried here: a snapshot is
//! evidence only while its source lowers to the term it was frozen from, and
//! checking that needs the lowering itself, an edge into the surface tier this
//! crate never takes. The alternative was core declarations transcribed by hand
//! and tied to their sources by digest, rejected because it asserts a lowering
//! the tree does not perform.
//!
//! # References
//!
//! - Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In
//!   _Proceedings of the Fifth ACM SIGPLAN International Conference on
//!   Functional Programming (ICFP '00)_, pages 233–243, September 2000.
//!   `doi:10.1145/351240.351262` — the command `⟨p | c⟩`, the binders `μα` and
//!   `μ̃x`, and the critical pair a cut's polarity resolves.
//! - Paul Downen and Zena M. Ariola. "A Tutorial on Computational Classical
//!   Logic and the Sequent Calculus." _Journal of Functional Programming_ 28
//!   (2018), e3. `doi:10.1017/S0956796818000023` — data and codata as
//!   constructor applications and copattern objects, pattern matches and
//!   destructor frames, and the polarized cut.
//! - Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." In _Typed
//!   Lambda Calculi and Applications (TLCA '99)_, Lecture Notes in Computer
//!   Science 1581, pages 228–243, 1999. `doi:10.1007/3-540-48959-2_17` — the
//!   value/computation split the IL's two polarities carry, and the thunk as
//!   the positive suspension of a computation.
//! - David Binder, Marco Tzschentke, Marius Müller and Klaus Ostermann.
//!   "Grokking the Sequent Calculus (Functional Pearl)." _Proceedings of the
//!   ACM on Programming Languages_ 8 (ICFP), 2024. `doi:10.1145/3674639` — the
//!   λμμ̃ command language as a compiler's intermediate language, which this
//!   crate's IL is in its polarized System L form, each cut's polarity
//!   resolving μ against μ̃.
//! - Jean Caspar and Guillaume Munch-Maccagnoni. "S4 Modal Sequent Calculus as
//!   Intermediate Logic and Intermediate Language (Short Paper)." PEPM 2026.
//!   `arXiv:2601.08071` — the operational machine that separates a heap from a
//!   stack, the two-region store read as residency; Lemma 3.1 (a heap value
//!   refers to no stack variable) and Theorem 4.1 (stackability), the
//!   second-class restriction `check` states on closures.
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: the
//!   LAM the [`Store`] is, a regioned append-only store addressed by
//!   location.
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-in-gandr item 1): a cut whose writer performs no operation is
//!   independent, so focus reads the caller's writers, focuses each such writer
//!   apart and marks its binder.

// Module documentation that predates the shape lint: 17 headings outside the
// vocabulary, 3 decision records and 9 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod boundary;
mod bridge;
mod check;
mod closure;
mod definitions;
mod focus;
mod identity;
mod il;
mod inspect;
mod outcome;
mod ownership;
mod pretty;
mod readback;
mod store;
mod unfocus;

pub use crate::boundary::ConsumerArity;
pub use crate::boundary::NodeCount;
pub use crate::boundary::ProducerArity;
pub use crate::bridge::ConstructorResolver;
pub use crate::bridge::ReifyRefusal;
pub use crate::bridge::reify_command;
pub use crate::check::ArityHead;
pub use crate::check::CheckRefusal;
pub use crate::check::FreeSet;
pub use crate::check::check_command;
pub use crate::closure::ClosureRefusal;
pub use crate::closure::beta;
pub use crate::closure::convert;
pub use crate::closure::convert_all;
pub use crate::closure::convert_step;
pub use crate::closure::enter_all;
pub use crate::definitions::Definition;
pub use crate::definitions::Definitions;
pub use crate::focus::FocusOrigin;
pub use crate::focus::FocusRefusal;
pub use crate::focus::Provenance;
pub use crate::focus::Writers;
pub use crate::focus::focus_computation;
pub use crate::focus::focus_definition;
pub use crate::focus::focus_top_value;
pub use crate::focus::focus_value;
pub use crate::identity::MotiveHead;
pub use crate::il::Captures;
pub use crate::il::CommandArena;
pub use crate::il::CommandId;
pub use crate::il::CommandNode;
pub use crate::il::ConstructorTag;
pub use crate::il::ConsumerId;
pub use crate::il::ConsumerNode;
pub use crate::il::CopatternArm;
pub use crate::il::CovariableIndex;
pub use crate::il::DestructorTag;
pub use crate::il::Independence;
pub use crate::il::Introduces;
pub use crate::il::MarkRefusal;
pub use crate::il::MintRefusal;
pub use crate::il::NodeAddress;
pub use crate::il::NodeFamily;
pub use crate::il::Opens;
pub use crate::il::PatternArm;
pub use crate::il::ProducerId;
pub use crate::il::ProducerNode;
pub use crate::il::REACHED;
pub use crate::il::REACHED_HOLE;
pub use crate::il::Route;
pub use crate::il::Selector;
pub use crate::il::SequentWatermark;
pub use crate::il::Suspension;
pub use crate::il::command_children;
pub use crate::il::consumer_children;
pub use crate::il::producer_children;
pub use crate::inspect::Stats;
pub use crate::inspect::dump;
pub use crate::inspect::origin_histogram;
pub use crate::inspect::stats;
pub use crate::outcome::Outcome;
pub use crate::outcome::Stuck;
pub use crate::ownership::Entry;
pub use crate::ownership::Ownership;
pub use crate::ownership::OwnershipRefusal;
pub use crate::ownership::Reuse;
pub use crate::ownership::Runs;
pub use crate::ownership::reach;
pub use crate::pretty::render_command;
pub use crate::pretty::render_consumer;
pub use crate::pretty::render_producer;
pub use crate::readback::ReadbackRefusal;
pub use crate::readback::read_back_terminal;
pub use crate::readback::read_back_value;
pub use crate::store::ClosedCommand;
pub use crate::store::Environment;
pub use crate::store::HeapFamily;
pub use crate::store::HeapValue;
pub use crate::store::HeapValueId;
pub use crate::store::Store;
pub use crate::store::StoreFault;
pub use crate::unfocus::UnfocusRefusal;
pub use crate::unfocus::unfocus_command;
pub use crate::unfocus::unfocus_value;
