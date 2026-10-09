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
//! The crate is `no_std` and depends on `core`, `alloc` and petgraph. The
//! papers it draws on are in its `README.md`, § References.

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
