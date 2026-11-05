//! Canonical dyadics, oriented intervals and the scoped plan DAG: the finite
//! arithmetic and the plan language that exact real computation reads.
//!
//! A real number is an infinite object, and a program can hold only finite
//! approximations of it. Floating point rounds each result without a record,
//! so its enclosures are not sound. This crate gives two exact finite domains
//! instead. A [`Dyadic`] is a number `m · 2^e` in one canonical form. A
//! [`NumericInterval`] is a pair of dyadic or infinite endpoints with an
//! explicit closure for each endpoint and an explicit orientation. Its
//! operations round outward, so each result contains every exact result of
//! its operands. The crate does not depend on the gandr kernel, and no real
//! number enters kernel conversion.
//!
//! Every operation is total and never panics, and it refuses each malformed
//! input by name. The work of one arithmetic operation is bounded by its
//! operands' bit widths and the requested precision.
//!
//! # Items
//!
//! - [`Plan`] — a computation over the reals: a finite DAG of real, open and
//!   domain nodes whose binders are de Bruijn indices. A plan holds each
//!   distinct subterm once, and it has one canonical byte form.
//! - [`approximate`] — an enclosure or a pair of approximants for each node of
//!   a validated plan, each sound on its own. It never reports an undecided
//!   proposition as false.
//! - [`check`], [`Certificate`] — the replay of a certificate with no search.
//! - [`refine`] — the narrowing of a registered cut, one certificate step for
//!   each halving.
//! - [`Obligation`], [`Dovetail`], [`Outcome`] — the refinement machine. An
//!   obligation names a node and the evidence that it asks for. A dovetail runs
//!   a set of them in bounded quanta, in a fixed order, within a budget. None
//!   of the five outcomes reads as false.
//!
//! # References
//!
//! - `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — lineage: the exact-reals
//!   design, its canonical dyadics with an inline path, its oriented intervals
//!   as runtime approximants, its scoped plan DAG that keeps sharing as edges,
//!   and its firewall from the kernel.

#![no_std]

extern crate alloc;

pub mod approx;
pub mod certificate;
pub mod codec;
pub mod dovetail;
pub mod dyadic;
pub mod interval;
pub mod plan;
pub mod schema;
pub mod semidecision;
pub mod validate;

pub use crate::approx::Approximation;
pub use crate::approx::BilateralApprox;
pub use crate::approx::NegativeApprox;
pub use crate::approx::PositiveApprox;
pub use crate::approx::approximate;
pub use crate::certificate::Certificate;
pub use crate::certificate::CertificateCheck;
pub use crate::certificate::CertificateRefusal;
pub use crate::certificate::Checked;
pub use crate::certificate::CheckerQuotas;
pub use crate::certificate::Conclusion;
pub use crate::certificate::FormatVersion;
pub use crate::certificate::Side;
pub use crate::certificate::Step;
pub use crate::certificate::StepCount;
pub use crate::certificate::StepId;
pub use crate::certificate::StepSite;
pub use crate::certificate::check;
pub use crate::codec::CertificateBytes;
pub use crate::codec::DecodeError;
pub use crate::codec::EncodedCertificate;
pub use crate::codec::EncodedPlan;
pub use crate::codec::PlanBytes;
pub use crate::dovetail::Budget;
pub use crate::dovetail::Dovetail;
pub use crate::dovetail::Position;
pub use crate::dovetail::Quantum;
pub use crate::dovetail::Report;
pub use crate::dovetail::Rounds;
pub use crate::dovetail::Steps;
pub use crate::dovetail::Stop;
pub use crate::dovetail::Work;
pub use crate::dyadic::BitWidth;
pub use crate::dyadic::Dyadic;
pub use crate::dyadic::DyadicError;
pub use crate::dyadic::Exactness;
pub use crate::dyadic::Exponent;
pub use crate::dyadic::Precision;
pub use crate::dyadic::Rounded;
pub use crate::dyadic::Rounding;
pub use crate::dyadic::Sign;
pub use crate::interval::Bound;
pub use crate::interval::Closure;
pub use crate::interval::Containment;
pub use crate::interval::Endpoint;
pub use crate::interval::IntervalError;
pub use crate::interval::NumericInterval;
pub use crate::interval::Orientation;
pub use crate::plan::Cut;
pub use crate::plan::DeBruijn;
pub use crate::plan::Domain;
pub use crate::plan::DomainId;
pub use crate::plan::Edge;
pub use crate::plan::Edges;
pub use crate::plan::Evidence;
pub use crate::plan::EvidenceSlot;
pub use crate::plan::Node;
pub use crate::plan::NodeCount;
pub use crate::plan::NodeId;
pub use crate::plan::Open;
pub use crate::plan::OpenId;
pub use crate::plan::Plan;
pub use crate::plan::PlanBuilder;
pub use crate::plan::PlanError;
pub use crate::plan::Power;
pub use crate::plan::Quantifier;
pub use crate::plan::Real;
pub use crate::plan::RealId;
pub use crate::plan::Root;
pub use crate::plan::Scope;
pub use crate::plan::Site;
pub use crate::plan::Sort;
pub use crate::schema::radicand;
pub use crate::schema::refine;
pub use crate::schema::square_root;
pub use crate::schema::square_root_of_two;
pub use crate::semidecision::Demand;
pub use crate::semidecision::Obligation;
pub use crate::semidecision::Outcome;
pub use crate::semidecision::SuspendReason;
pub use crate::validate::ByteLength;
pub use crate::validate::Check;
pub use crate::validate::Conflict;
pub use crate::validate::EvidenceTable;
pub use crate::validate::Height;
pub use crate::validate::Judgement;
pub use crate::validate::Quotas;
pub use crate::validate::Refusal;
pub use crate::validate::ValidatedPlan;
pub use crate::validate::admit;
pub use crate::validate::validate;
