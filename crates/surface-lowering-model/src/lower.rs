//! The family of the lowering that this crate holds, at the paths it keeps in
//! the lowering. It reads the base's records and context by the names the
//! lowering's `lower` module gives them.

pub mod arity;
pub mod model;

use gandr_surface_lowering_base::lower::Code;
use gandr_surface_lowering_base::lower::Context;
use gandr_surface_lowering_base::lower::InstanceType;
use gandr_surface_lowering_base::lower::LabelRead;
use gandr_surface_lowering_base::lower::Lowered;
use gandr_surface_lowering_base::lower::MODEL;
use gandr_surface_lowering_base::lower::Parameter;
use gandr_surface_lowering_base::lower::Plan;
use gandr_surface_lowering_base::lower::Produced;
use gandr_surface_lowering_base::lower::Reading;
use gandr_surface_lowering_base::lower::Resolved;
use gandr_surface_lowering_base::lower::Sink;
use gandr_surface_lowering_base::lower::Site;
use gandr_surface_lowering_base::lower::Statement;
use gandr_surface_lowering_base::lower::StatementBinding;
use gandr_surface_lowering_base::lower::Stretch;
use gandr_surface_lowering_base::lower::closed;
use gandr_surface_lowering_base::lower::exhausted;
use gandr_surface_lowering_base::lower::exits;
use gandr_surface_lowering_base::lower::implicit;
use gandr_surface_lowering_base::lower::inert;
use gandr_surface_lowering_base::lower::lowered;
use gandr_surface_lowering_base::lower::multiplicity_one;
use gandr_surface_lowering_base::lower::named;
use gandr_surface_lowering_base::lower::native;

use crate::module::DeclarationOutcome;
use crate::resolve::Frame;
