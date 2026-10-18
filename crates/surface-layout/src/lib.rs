//! The shared document-layout engine.
//!
//! A client builds an immutable document in a sealed arena, the resolver picks
//! a Pareto-optimal layout for a page width, and a first-order machine renders
//! the winning plan. Every client of the layout engine — the presentation
//! printer, a source formatter, a language-server face — shares this one
//! implementation, so a layout decision is made in exactly one place.
//!
//! The engine is more expressive than a greedy Wadler printer: it carries
//! arbitrary choice and unaligned concatenation. Those two features cannot be
//! added to a greedy representation afterwards without rewriting every client
//! document.
//!
//! | module                 | what it holds                                                    |
//! | ---------------------- | ---------------------------------------------------------------- |
//! | [`units`]              | the nominal counts, widths and ceilings every other module reads |
//! | [`error`]              | the typed build and render failures                              |
//! | [`limits`]             | the build and render ceilings and the meters that charge them    |
//! | [`arena`]              | the sealed document arena and its validated handles              |
//! | [`build`]              | the document builder and its finalization pass                   |
//! | [`measure`]            | cost, width taint and the layout options                         |
//! | [`taint`]              | the tainted-promise algebra over measure sets                    |
//! | [`plan`]               | the generational plan arena                                      |
//! | [`mod@resolve`]        | the memoized resolver                                            |
//! | [`vm`]                 | the first-order render machine                                   |
//! | [`mod@render`]         | the render entry point and the rendered bytes                    |
//!
//! # The boundary this crate owns
//!
//! Document nodes, physical line emission, identity validity, flattening,
//! choice resolution, width taint, cost and frontier order, memoization, render
//! plans, and every resource limit belong here, because they must be identical
//! for every client. Which syntactic form groups, aligns, or nests is a
//! language decision and belongs to the client. The requested page width and
//! the client's presentation budget belong to the caller: a batch run, a
//! language server, a read-evaluate loop, and a narrow terminal pane each have
//! a different one.
//!
//! The cost order is squared overflow followed by line count, and a client may
//! add choices and nesting but may not replace that order.
//!
//! # Totality
//!
//! Nothing in this crate panics, diverges, or truncates. Construction and
//! rendering are metered against explicit limits, every arithmetic step is
//! checked, every vector store checks its limit and then reserves fallibly,
//! and the two ordered maps — the flatten interner and the resolver memo — are
//! bounded by the node and memo-state ceilings charged before each insertion.
//! A failure returns a typed error rather than partial output, and a broken
//! internal invariant is a typed error too, never a panic. A document too wide
//! for its computation width is reported as width-tainted and is still
//! rendered in full; taint marks a layout as outside the optimality theorem,
//! never as a candidate to cut short.
//!
//! # Executable specifications
//!
//! Nontrivial items pair their specification clauses with `#[spec]` predicates
//! and an adequacy argument naming concrete witnesses. Enforcing builds check
//! arithmetic and refusal precedence, unchanged counters after refused charges,
//! adopted allocation identities, handle namespaces, plan generations and
//! ownership, taint contexts, resolver transitions, Pareto ordering and exact
//! output accounting. Predicates use bounded snapshots or borrowed observations
//! rather than cloning owned stores or replaying callbacks.
//!
//! Run the same witnesses with executable checks enabled:
//!
//! ```sh
//! RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-surface-layout
//! ```
//!
//! Each `executable: none` clause names an unavailable observation: data
//! declarations have no call boundary, formatters expose write-only sinks, the
//! small-stack witness consumes a one-shot callback, and opaque const
//! projections lack const value observers. Their adequacy sections identify the
//! runtime consumers that observe the obligation. Bounded exhaustive models are
//! distinguished from selected graph fixtures; allocator exhaustion is not
//! claimed as exercised.
//!
//! # Explicit stacks
//!
//! Nothing in the crate recurses. Finalization is one forward pass, because
//! every edge names an earlier node; balanced concatenation builds explicit
//! levels; resolution runs one work vector of evaluations and continuations;
//! releasing a plan returns its children to the caller's stack; rendering walks
//! plan identities on a heap stack. A deep document is ordinary input: the
//! witnesses seal spines of two hundred thousand nodes and release a chain of a
//! hundred thousand plan sequences on a 64 KiB native stack
//! (`tests::algebra::deep_left_spine_construction_uses_a_heap_work_stack`,
//! `plan::tests::plan_release_recycles_a_deep_sequence_iteratively`). The
//! resolver's and the machine's stacks have their own ceilings
//! (`tests::algebra::render_vm_stack_limit_is_checked_before_output`).
//!
//! # References
//!
//! - Sorawee Porncharoenwase, Justin Pombrio, and Emina Torlak. "A Pretty
//!   Expressive Printer." _Proceedings of the ACM on Programming Languages_ 7,
//!   OOPSLA2, October 2023.
//!   [doi:10.1145/3622837](https://doi.org/10.1145/3622837),
//!   [arXiv:2310.01530](https://arxiv.org/abs/2310.01530) — the optimality
//!   theorem, the measure set and its dominance order, the computation width
//!   and the taint state machine, in-context memoization, and the complexity
//!   bounds this engine implements.
//! - Jean-Philippe Bernardy. "A Pretty But Not Greedy Printer (Functional
//!   Pearl)." _Proceedings of the ACM on Programming Languages_ 1, ICFP,
//!   article 6, September 2017.
//!   [doi:10.1145/3110250](https://doi.org/10.1145/3110250) — resolution as a
//!   frontier of non-dominated measures rather than a greedy first fit.
//! - Philip Wadler. "A Prettier Printer." In Jeremy Gibbons and Oege de Moor
//!   (editors), _The Fun of Programming_, Palgrave Macmillan, 2003.
//!   [prettier.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf)
//!   — the document algebra that this crate's choice and flattening generalize.

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

pub mod arena;
pub mod build;
pub mod error;
pub mod limits;
pub mod measure;
pub mod plan;
pub mod render;
pub mod resolve;
pub mod taint;
pub mod units;
pub mod vm;

pub use error::RenderError;
pub use limits::RenderLimits;
pub use limits::RenderMeter;
pub use limits::RenderUsage;
pub use measure::LayoutCost;
pub use measure::LayoutOptions;
pub use measure::PhysicalLineEnding;
pub use measure::WidthTaint;
pub use plan::PlanId;
pub use resolve::Resolved;
pub use resolve::resolve;
pub use units::ComputationWidth;
pub use units::PageWidth;
