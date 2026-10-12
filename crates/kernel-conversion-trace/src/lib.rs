//! The **conversion-decision seam** between the untrusted convertibility engine
//! and the certified kernel.
//!
//! # Why the seam exists
//!
//! Convertibility is proof search, and the proof is what gets certified. The
//! engine searches and is trusted with nothing; what it emits is a trace of the
//! decisions it made, and the kernel replays that trace with a sequential
//! algorithm that performs no search. A wrong engine therefore costs
//! completeness and never soundness.
//!
//! # The seam names no term type
//!
//! This crate owns no term vocabulary, no storage format, no wire
//! representation, and no replay policy. Its generic identifier parameter keeps
//! those concerns in the consumer that owns the arena, and the constraint is
//! enforced by the generics rather than by review.
//!
//! # The vocabulary covers branches, not heuristics
//!
//! [`ConversionDecision`] records **the side of every reduction and the branch
//! taken at every choice point** — which is the grain a proof search needs,
//! against the grain a heuristic unfolding strategy needs. That is what makes
//! replay search-free: with the recorded choices in hand the rechecker has at
//! most one applicable rule at every step.
//!
//! # The static-dispatch discipline
//!
//! [`TraceSink`] carries an associated [`SinkActivity`] constant, the same
//! discipline the check-memo seam takes. Instantiated at [`NullSink`] a
//! conversion path builds no decision values and holds no recording state, so
//! sink-off conversion is **the same function at a different type parameter**
//! rather than a second implementation. [`TraceLog`] is the recording side,
//! and it is what a differential counts its exercised path through: a suite
//! that instantiates only [`NullSink`] can be green while reaching no
//! recording code at all.
//!
//! # Traces and equality
//!
//! A trace individuates strictly more finely than convertibility: two
//! convertible terms can carry different traces. A trace is replay evidence
//! and never an equality, so comparing two traces decides something finer
//! than conversion and would disagree on convertible inputs while raising
//! nothing.
//!
//! A trace records that two occurrences met, not that they agreed. A
//! refutation and a proof can carry the same closing decision, and the replay
//! recomputes the verdict from the terms.
//!
//! # Portable path dialogues
//!
//! `gandr-kernel-term`'s `PathEvidence` persists this vocabulary with unit
//! anchors, source and target dialogue boundaries, and ordered decision words.
//! The kernel reconstructs every replay obligation from typed terms; a stored
//! trace is not an admission receipt. `Dialogue::pair` in `gandr-kernel-core`
//! prefixes two `Decompose` decisions before concatenating returner component
//! traces, so a component's closing shortcut cannot discharge the enclosing
//! pair.
//!
//! **Choice.** One decision alphabet for ordinary conversion and the
//! computations that native paths, higher fields, funext and `Flow_U` replay.
//! **Alternative.** A separate certificate protocol, which would duplicate
//! side, decomposition and negative-premise semantics. **Reversal.** A
//! consumer needing a new payload defines its replay rule and framing without
//! reinterpreting an existing decision. The consumer owns the replay budget;
//! exhaustion is a decline, not an equality decision.
//!
//! # Exhaustive matching
//!
//! No enum here is `#[non_exhaustive]`. The workspace does not publish, so the
//! attribute would protect no external consumer while forcing a wildcard arm
//! at every match and defeating exhaustiveness exactly where a new variant
//! should break every consumer.
//!
//! # Specification attributes
//!
//! The `# Specification` prose states the obligation; `#[spec(...)]` checks
//! the clauses expressible over one call. Both shipped sinks have exact count
//! predicates: the null sink remains at zero, an append grows the log by one,
//! and the count reports the held sequence's length. These predicates capture
//! scalar counts, not owned snapshots.
//!
//! Each nontrivial item has a bounded `# Adequacy` hypothesis. The storage
//! witnesses cover every decision kind, side-specific payloads, position
//! boundaries, repeated events and non-Copy identifiers through exact
//! iteration and counts. The layered-term workload checks atom-derived
//! verdicts and closing decisions; malformed traces exercise each refusal
//! guard and error precedence. Reusing a populated log checks that a new
//! refutation appends without clearing its prefix. These observations do not
//! measure optimizer elimination of decision construction.
//!
//! A final `- executable: none` clause names the remaining boundary: external
//! arenas or event histories, data construction that invokes no predicate,
//! trait instrumentation that would change required implementor methods,
//! unsupported associated constants, or the opaque iterator return type. The
//! witnesses certify the shipped implementations on their stated domains, not
//! arbitrary consumers or traces.
//!
//! The crate is `no_std` and depends only on `core`, `alloc` and the
//! specification facade.
//!
//! The papers the crate draws on are in its `README.md`, § References.

#![no_std]

extern crate alloc;

pub mod decision;
pub mod sink;

pub use crate::decision::ConversionDecision;
pub use crate::decision::ConversionSide;
pub use crate::decision::SubgoalPosition;
pub use crate::sink::DecisionCount;
pub use crate::sink::NullSink;
pub use crate::sink::SinkActivity;
pub use crate::sink::TraceLog;
pub use crate::sink::TraceSink;
