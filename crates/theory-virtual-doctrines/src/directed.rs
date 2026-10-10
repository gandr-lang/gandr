//! Variance, directed hom, finite quantifiers and certificate cut.

pub mod boundary;
pub mod coend;
pub mod context;
pub mod hom;

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
