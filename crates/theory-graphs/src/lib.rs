//! Graph theory for the gandr surface: the operator-precedence DAG, the walk
//! machine a grammar's tiles are closed under, and the graph algorithms both
//! stand on.
//!
//! The **grammar half** is what the surface tier depends on this crate for:
//! the named precedence DAG ([`PrecSpec`], [`PrecDag`], [`Prec`], [`Assoc`],
//! [`Bound`]) and the declarative walk index ([`WalkSpec`], [`WalkIndex`],
//! [`Walk`], [`Dir`], [`End`]). The **algorithm half** is the part of a graph
//! library they need, over one dense boundary, [`EdgeSource`]:
//! [`cycle_witness`], [`reachability`] and [`condensation`]. The fixed
//! FNV-1a accumulator [`Fnv64`] computes every stable fingerprint, here and in
//! the consumers.
//!
//! The condensation runs on petgraph, which no public signature names: a
//! graph enters as an [`EdgeSource`] and every result is in dense node
//! identities.
//!
//! The crate is `no_std` and depends on `core`, `alloc` and petgraph.
//!
//! # Scope
//!
//! The algorithm half carries what the grammar reads and nothing else: cycle
//! evidence and reachability for the precedence DAG, condensation for the
//! closing-class derivation. The DAG's linear extension is its own Kahn order,
//! so no general topological sort is exposed. Dominators, shortest paths,
//! simple-path enumeration, transitive reduction, partition refinement and an
//! adjacency fingerprint are absent because no consumer reads them; an
//! algorithm with no reader is maintained surface with no contract a consumer
//! depends on. The walk index needs no partition refinement: its rows are
//! canonicalised by key, not by bisimulation.
//!
//! The determinism probe — a binary that prints the byte-level projection of
//! every public result while scratch allocation is perturbed — and the
//! benchmarks are a lateral, outside this crate. Determinism is held here by
//! construction and by test: every tie is broken by the smallest dense
//! identifier, every collection the results are read from is ordered, no hasher
//! is process-random, and the pinned fingerprints and permuted-insertion tests
//! fail on any drift.
//!
//! Executable `#[spec]` predicates check arithmetic and refusal boundaries,
//! dense incidence, precedence comparisons, walk shape and canonical-row
//! invariants. They retain scalar snapshots or borrowed observers rather than
//! copies of entire inputs. Each nontrivial operation names its same-crate
//! witnesses and the boundary of their evidence under `# Adequacy`; the
//! enforcing test lane runs the predicates. Complete closure and canonical
//! tie-breaking are checked against independent fixtures and generated oracles,
//! not assumed from the structural predicates.
//!
//! Required trait declarations, opaque iterator returns and consuming generic
//! fingerprint conversions record why their contracts cannot be instrumented
//! locally without changing a protocol or ownership boundary. Display evidence
//! observes numeric fields and sink refusal without pinning wording.
//!
//! # References
//!
//! - David Moon, Andrew Blinn, Thomas J. Porter, and Cyrus Omar. "Syntactic
//!   Completions with Material Obligations." _Proceedings of the ACM on
//!   Programming Languages_ 9, OOPSLA2 (October 2025). `doi:10.1145/3763182`;
//!   preprint `arXiv:2508.16848` — the walk, swing and stance vocabulary, the
//!   validity and minimality filters and canonical order of § 4.1, and the
//!   figure-33 fragments the walk suite pins.
//! - Nils Anders Danielsson and Ulf Norell. "Parsing Mixfix Operators." In
//!   _Implementation and Application of Functional Languages (IFL 2008)_,
//!   Lecture Notes in Computer Science 5836, pages 80–99, 2011.
//!   `doi:10.1007/978-3-642-24452-0_5` — the precedence-graph presentation the
//!   precedence DAG follows: groups related by a tighter-than order that need
//!   not be total.
//! - A. B. Kahn. "Topological Sorting of Large Networks." _Communications of
//!   the ACM_ 5, 11 (November 1962), pages 558–562. `doi:10.1145/368996.369025`
//!   — the ready-set topological sort the DAG's linear extension is, with its
//!   tie-break fixed to the smallest ready group.
//! - Micha Sharir. "A Strong-Connectivity Algorithm and Its Applications in
//!   Data Flow Analysis." _Computers & Mathematics with Applications_ 7, 1
//!   (1981), pages 67–72. `doi:10.1016/0898-1221(81)90008-0` — the two-pass
//!   strongly-connected-component algorithm petgraph's condensation runs.
//! - Glenn Fowler, Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd, and
//!   Tony Hansen. "The FNV Non-Cryptographic Hash Algorithm." RFC 9923,
//!   February 2026. `doi:10.17487/RFC9923` — the 64-bit FNV-1a parameters
//!   `Fnv64` fixes, pinned against the published test vectors.

// Module documentation that predates the shape lint: 5 headings outside the
// vocabulary and 1 decision record. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod algorithms;
mod fingerprint;
mod prec;
mod types;
mod walk;

pub use crate::algorithms::Condensation;
pub use crate::algorithms::CycleWitness;
pub use crate::algorithms::EdgeSource;
pub use crate::algorithms::GraphValidationError;
pub use crate::algorithms::Reachability;
pub use crate::algorithms::ReachabilityRow;
pub use crate::algorithms::condensation;
pub use crate::algorithms::cycle_witness;
pub use crate::algorithms::reachability;
pub use crate::fingerprint::Fnv64;
pub use crate::prec::Assoc;
pub use crate::prec::Bound;
pub use crate::prec::Prec;
pub use crate::prec::PrecCycle;
pub use crate::prec::PrecDag;
pub use crate::prec::PrecDagError;
pub use crate::prec::PrecGroupCount;
pub use crate::prec::PrecIndex;
pub use crate::prec::PrecName;
pub use crate::prec::PrecSetEmpty;
pub use crate::prec::PrecSpec;
pub use crate::prec::PrecSpecError;
pub use crate::prec::PrecedenceComparison;
pub use crate::types::ComponentEdge;
pub use crate::types::ComponentIndex;
pub use crate::types::EdgeId;
pub use crate::types::Fingerprint;
pub use crate::types::FingerprintByte;
pub use crate::types::FingerprintBytes;
pub use crate::types::FingerprintWord16;
pub use crate::types::FingerprintWord32;
pub use crate::types::FingerprintWord64;
pub use crate::types::NodeCount;
pub use crate::types::NodeId;
pub use crate::types::NodeIdRange;
pub use crate::types::SwingHeight;
pub use crate::types::WalkChainLength;
pub use crate::types::WalkHeight;
pub use crate::walk::Dir;
pub use crate::walk::End;
pub use crate::walk::SeenKeyVerdict;
pub use crate::walk::StanceTileSorted;
pub use crate::walk::Swing;
pub use crate::walk::SwingAdvance;
pub use crate::walk::SwingArc;
pub use crate::walk::Walk;
pub use crate::walk::WalkBuildError;
pub use crate::walk::WalkEquality;
pub use crate::walk::WalkIndex;
pub use crate::walk::WalkInequality;
pub use crate::walk::WalkSpec;
pub use crate::walk::WalkStep;
pub use crate::walk::WalkSym;
pub use crate::walk::WalkSymbolKey;
