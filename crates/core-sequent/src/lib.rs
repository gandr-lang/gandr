//! The sequent tier of gandr's core: the command IL a call-by-push-value
//! program is focused into, and the store the abstract machine that runs it
//! works over.
//!
//! - [`CommandArena`] holds producers, consumers and commands —
//!   [`ProducerNode`], [`ConsumerNode`], [`CommandNode`] — minted only over
//!   children it holds, with [`SequentWatermark`] and
//!   [`CommandArena::truncate_to`] the rollback a refused build takes.
//!   Covariables are de Bruijn indices ([`CovariableIndex`]); nothing mints a
//!   continuation name.
//! - [`focus_computation`], [`focus_value`] and [`focus_top_value`] translate
//!   core terms into the IL, recording each created command's [`FocusOrigin`]
//!   in a [`Provenance`] table; [`unfocus_command`] and [`unfocus_value`] read
//!   the IL back, their left inverse.
//! - [`check_command`] is the typed-IL check: reference integrity, arity, focus
//!   and polarity, answering a command's [`FreeSet`].
//! - [`render_command`], [`render_producer`] and [`render_consumer`] write the
//!   IL's notation.
//! - [`Store`] is the machine's two-region store: the heap region of
//!   [`HeapValue`]s, memo cells and environment chains, and the walkable frame
//!   region of [`Frame`]s addressed by [`ContinuationMark`]s.
//! - [`Machine`] runs a command over the store, unfolding constants from
//!   [`Definitions`], to an [`Outcome`] within a [`StepCount`] budget, and
//!   reads a halted value back as a core term.
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
//! over a glued domain, and shares no step with the machine. Each case in
//! `tests/differential.rs` runs both ways, and the machine's terminal, read
//! back, is compared node for node with the normaliser's normal form. A
//! first-order answer agrees exactly. The machine reads a suspended body back
//! as written, its environment substituted, where the normaliser reduces under
//! the binder, so a thunk or a function still holding a redex agrees once the
//! machine's reading is normalised too; the hand-built cases pin which of the
//! two each answer needs, which shows the comparison telling terms apart. An
//! ill-typed redex stops both at the same elimination, a nominal match on
//! anything but a constructor it has a branch for included. Recursive
//! definitions over Nat, List and a Tree with a function field compute the same
//! answer on both. Over generated closed, well-typed computations every run
//! halts, two runs read back alike, and the normalised reading is the normal
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
//! - John Launchbury. "A Natural Semantics for Lazy Evaluation." In
//!   _Proceedings of the 20th ACM SIGPLAN-SIGACT Symposium on Principles of
//!   Programming Languages (POPL '93)_, pages 144–154, 1993.
//!   `doi:10.1145/158511.158618` — call-by-need as a heap of updatable
//!   suspensions, and the black hole a re-entered suspension shows.
//! - Peter O'Hearn, John Reynolds and Hongseok Yang. "Local Reasoning about
//!   Programs that Alter Data Structures." In _Computer Science Logic (CSL
//!   2001)_, Lecture Notes in Computer Science 2142, pages 1–19, 2001.
//!   `doi:10.1007/3-540-44802-0_1` — the heap as a partial commutative monoid
//!   under disjoint union, and the frame rule the memo-cell suite states its
//!   four conditions in.

#![no_std]

extern crate alloc;

mod boundary;
mod bridge;
mod check;
mod flow;
mod focus;
mod il;
mod inspect;
mod machine;
mod pretty;
mod readback;
mod store;
mod unfocus;

pub use crate::boundary::ConsumerArity;
pub use crate::boundary::FrameHeight;
pub use crate::boundary::FrameSerial;
pub use crate::boundary::NodeCount;
pub use crate::boundary::ProducerArity;
pub use crate::boundary::StepCount;
pub use crate::bridge::ConstructorResolver;
pub use crate::bridge::ReifyRefusal;
pub use crate::bridge::reify_command;
pub use crate::check::ArityHead;
pub use crate::check::CheckRefusal;
pub use crate::check::FreeSet;
pub use crate::check::check_command;
pub use crate::focus::FocusOrigin;
pub use crate::focus::FocusRefusal;
pub use crate::focus::Provenance;
pub use crate::focus::focus_computation;
pub use crate::focus::focus_top_value;
pub use crate::focus::focus_value;
pub use crate::il::CommandArena;
pub use crate::il::CommandId;
pub use crate::il::CommandNode;
pub use crate::il::ConstructorTag;
pub use crate::il::ConsumerId;
pub use crate::il::ConsumerNode;
pub use crate::il::CopatternArm;
pub use crate::il::CovariableIndex;
pub use crate::il::DestructorTag;
pub use crate::il::MintRefusal;
pub use crate::il::NodeFamily;
pub use crate::il::PatternArm;
pub use crate::il::ProducerId;
pub use crate::il::ProducerNode;
pub use crate::il::Selector;
pub use crate::il::SequentWatermark;
pub use crate::inspect::Stats;
pub use crate::inspect::dump;
pub use crate::inspect::origin_histogram;
pub use crate::inspect::stats;
pub use crate::machine::Definition;
pub use crate::machine::Definitions;
pub use crate::machine::HostHandler;
pub use crate::machine::HostOutcome;
pub use crate::machine::HostReply;
pub use crate::machine::HostRequest;
pub use crate::machine::HostValues;
pub use crate::machine::Machine;
pub use crate::machine::MachineFault;
pub use crate::machine::Outcome;
pub use crate::machine::Stuck;
pub use crate::pretty::render_command;
pub use crate::pretty::render_consumer;
pub use crate::pretty::render_producer;
pub use crate::readback::ReadbackRefusal;
pub use crate::store::CellId;
pub use crate::store::ContinuationMark;
pub use crate::store::Covalue;
pub use crate::store::CovalueBindingId;
pub use crate::store::CovalueScope;
pub use crate::store::Environment;
pub use crate::store::ForceEntry;
pub use crate::store::Frame;
pub use crate::store::HeapFamily;
pub use crate::store::HeapValue;
pub use crate::store::HeapValueId;
pub use crate::store::Memo;
pub use crate::store::MemoState;
pub use crate::store::ObservationArguments;
pub use crate::store::Store;
pub use crate::store::StoreFault;
pub use crate::store::ValueBindingId;
pub use crate::store::ValueScope;
pub use crate::unfocus::UnfocusRefusal;
pub use crate::unfocus::unfocus_command;
pub use crate::unfocus::unfocus_value;
