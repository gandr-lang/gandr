//! Virtual double categories and their first-order reflected judgments.
//!
//! Engine facts are checked by certificate replay. The public law suite
//! witnesses cartesian action, restriction, composition and directed rules.

#![no_std]

extern crate alloc;

pub mod boundary;
pub mod cartesian;
pub mod check;
pub mod directed;
pub mod iso;
pub mod query;
pub mod signature;
pub mod syntax;
pub mod vdc;

pub use crate::boundary::CartesianDiagonalPreservation;
pub use crate::boundary::CartesianProjectionPreservation;
pub use crate::boundary::CartesianStructurePreservation;
pub use crate::boundary::CertificateInvertibility;
pub use crate::boundary::CheckContextDeclaration;
pub use crate::boundary::CutCoherence;
pub use crate::boundary::CutDeclination;
pub use crate::boundary::DerivationIndex;
pub use crate::boundary::DerivationReplay;
pub use crate::boundary::DescTableEmptyStatus;
pub use crate::boundary::DescTableLength;
pub use crate::boundary::DiagramCarrierEmptyStatus;
pub use crate::boundary::DiagramCarrierLength;
pub use crate::boundary::DirectedContextDeclaration;
pub use crate::boundary::DirectedHomReflexivity;
pub use crate::boundary::DirectedObjectCovariance;
pub use crate::boundary::DiscreteHomInhabitation;
pub use crate::boundary::IsoValidity;
pub use crate::boundary::MotiveCovariance;
pub use crate::boundary::RewriteCompletion;
pub use crate::boundary::RewriteReachability;
pub use crate::boundary::RewriteStepBudget;
pub use crate::boundary::RoundTripIdentity;
pub use crate::boundary::SigMorphismIdentity;
pub use crate::boundary::VdcCellEquality;
pub use crate::cartesian::CartesianLawError;
pub use crate::cartesian::CartesianWitness;
pub use crate::cartesian::WCartesianAction;
pub use crate::check::CheckError;
pub use crate::check::Checker;
pub use crate::check::Context;
pub use crate::directed::boundary::CutOutcome;
pub use crate::directed::boundary::all_participating_invertible;
pub use crate::directed::boundary::directed_cut;
pub use crate::directed::coend::BiDiagram;
pub use crate::directed::coend::Coend;
pub use crate::directed::coend::Diagram;
pub use crate::directed::coend::End;
pub use crate::directed::coend::coyoneda_collapse;
pub use crate::directed::coend::discrete_hom_inhabited;
pub use crate::directed::coend::fubini_swap;
pub use crate::directed::context::DirectedContext;
pub use crate::directed::context::OpSig;
pub use crate::directed::context::Variance;
pub use crate::directed::context::VarianceError;
pub use crate::directed::hom::DirectedHom;
pub use crate::directed::hom::DirectedJ;
pub use crate::directed::hom::JError;
pub use crate::directed::hom::MotiveShape;
pub use crate::directed::hom::check_directed_j;
pub use crate::iso::IsoWitness;
pub use crate::iso::ProtypeIso;
pub use crate::query::ExtensionCandidate;
pub use crate::query::InstanceRow;
pub use crate::query::InstanceTable;
pub use crate::query::Query;
pub use crate::query::RewritePath;
pub use crate::query::SeamComposite;
pub use crate::syntax::DerivationId;
pub use crate::syntax::ProVar;
pub use crate::syntax::Proterm;
pub use crate::syntax::Protype;
pub use crate::vdc::CellStoreVdc;
pub use crate::vdc::Derivation;
pub use crate::vdc::DescTable;
pub use crate::vdc::Elaborated;
pub use crate::vdc::RelationRef;
pub use crate::vdc::SigMorphism;
pub use crate::vdc::SignatureRef;
pub use crate::vdc::TermRef;
pub use crate::vdc::Vdc;
