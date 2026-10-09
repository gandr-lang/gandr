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
