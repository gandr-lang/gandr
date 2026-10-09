//! Normalization by evaluation for the core language: the **glued value
//! domain**, the per-run arena that owns it, its policy parameters, the
//! machine that evaluates a core term to weak head, the machine that reads one
//! back, and the machine that decides conversion.
//!
//! - [`DomainArena`] owns every glued node one run produces. A node carries a
//!   [`TermFace`], and a neutral carries an [`Unfolding`] beside its neutral
//!   form.
//! - [`ValueClosure`] and [`CompClosure`] suspend a body over a two-zone
//!   [`Environment`].
//! - [`SchedulingPolicy`], [`DuplicationPolicy`] and [`GranularityPolicy`] are
//!   the parameters the domain and its conversion machine are written against.
//! - [`eval_value`] and [`eval_computation`] evaluate to weak head;
//!   [`readback_value`] and [`readback_computation`] read back under a
//!   [`ReadbackMode`].
//! - [`convert_values`] and [`convert_computations`] run the conversion steps
//!   that need no search — identity, the [`Guard`] every node is minted with,
//!   and structural comparison — answering a [`Settlement`].
//! - [`decide`] runs step 4, the lazy concurrent search over goals and
//!   evaluation channels, answering a [`MachineVerdict`] and emitting its
//!   winning derivation through a trace sink. It re-shares the goals it starts
//!   fresh through a check memo keyed by [`GoalSupport`], [`ResharingMemo`] on
//!   the engine path, and reports the [`SupportEdges`] its entries rest on.
//! - [`Overlay`] holds sharing syntax over the core language in four flat
//!   families, minted only over children it holds and checked by
//!   [`Overlay::validate`] over a heap worklist; [`erase_value`] and its
//!   siblings erase it, with no policy, back to the unshared core term.
//!
//! The design, and what a caller must guarantee, is stated in this crate's
//! `README.md`, § Synopsis and § Expected features, and in the sections they
//! link.

#![no_std]

extern crate alloc;

mod arena;
mod closure;
mod conv;
mod derivation;
mod domain;
mod eval;
mod guard;
mod machine;
mod overlay;
mod policy;
mod readback;
mod resharing;
mod rules;

pub use crate::arena::CompClosureId;
pub use crate::arena::DomainArena;
pub use crate::arena::DomainCompId;
pub use crate::arena::DomainFault;
pub use crate::arena::DomainValueId;
pub use crate::arena::NeutralId;
pub use crate::arena::RunWatermark;
pub use crate::arena::ValueClosureId;
pub use crate::closure::CompClosure;
pub use crate::closure::Environment;
pub use crate::closure::EnvironmentDepth;
pub use crate::closure::ValueClosure;
pub use crate::conv::ConversionFault;
pub use crate::conv::Convertibility;
pub use crate::conv::Deferral;
pub use crate::conv::Settlement;
pub use crate::conv::convert_computations;
pub use crate::conv::convert_values;
pub use crate::derivation::DerivationCount;
pub use crate::domain::BinderLevel;
pub use crate::domain::CompTermFace;
pub use crate::domain::DomainComp;
pub use crate::domain::DomainValue;
pub use crate::domain::Elimination;
pub use crate::domain::ForceRefusal;
pub use crate::domain::Glued;
pub use crate::domain::LevelEntry;
pub use crate::domain::LiftTarget;
pub use crate::domain::Neutral;
pub use crate::domain::NeutralHead;
pub use crate::domain::TermFace;
pub use crate::domain::Unfolding;
pub use crate::eval::Definitions;
pub use crate::eval::EvalFault;
pub use crate::eval::Fuel;
pub use crate::eval::LoweredChain;
pub use crate::eval::eval_computation;
pub use crate::eval::eval_value;
pub use crate::guard::ContentHash;
pub use crate::guard::Guard;
pub use crate::guard::GuardAnswer;
pub use crate::machine::DeclineReason;
pub use crate::machine::MachineReport;
pub use crate::machine::MachineSettings;
pub use crate::machine::MachineVerdict;
pub use crate::machine::Problem;
pub use crate::machine::ProcessCount;
pub use crate::machine::ProcessId;
pub use crate::machine::StepBudget;
pub use crate::machine::StepCount;
pub use crate::machine::decide;
pub use crate::overlay::Bound;
pub use crate::overlay::CompGraft;
pub use crate::overlay::CompNode;
pub use crate::overlay::CompTypeGraft;
pub use crate::overlay::CompTypeNode;
pub use crate::overlay::EraseFault;
pub use crate::overlay::Overlay;
pub use crate::overlay::OverlayCompId;
pub use crate::overlay::OverlayCompTypeId;
pub use crate::overlay::OverlayFamily;
pub use crate::overlay::OverlayFault;
pub use crate::overlay::OverlayId;
pub use crate::overlay::OverlayRefusal;
pub use crate::overlay::OverlayValueId;
pub use crate::overlay::OverlayValueTypeId;
pub use crate::overlay::OverlayWatermark;
pub use crate::overlay::ShareArity;
pub use crate::overlay::ShareDistance;
pub use crate::overlay::SharePosition;
pub use crate::overlay::Sharing;
pub use crate::overlay::ValueGraft;
pub use crate::overlay::ValueNode;
pub use crate::overlay::ValueTypeGraft;
pub use crate::overlay::ValueTypeNode;
pub use crate::overlay::erase_comp_type;
pub use crate::overlay::erase_computation;
pub use crate::overlay::erase_value;
pub use crate::overlay::erase_value_type;
pub use crate::policy::Copied;
pub use crate::policy::DuplicationPolicy;
pub use crate::policy::DuplicationStance;
pub use crate::policy::GranularityPolicy;
pub use crate::policy::GranularityStance;
pub use crate::policy::PolicyRefusal;
pub use crate::policy::SchedulingPolicy;
pub use crate::policy::SchedulingStance;
pub use crate::policy::Share;
pub use crate::policy::SharedPart;
pub use crate::readback::ReadbackFault;
pub use crate::readback::ReadbackMode;
pub use crate::readback::readback_computation;
pub use crate::readback::readback_value;
pub use crate::resharing::EdgeCount;
pub use crate::resharing::GoalSupport;
pub use crate::resharing::ResharingMemo;
pub use crate::resharing::ResharingPlane;
pub use crate::resharing::SupportEdges;
pub use crate::resharing::SupportSides;
