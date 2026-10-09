//! Normalization by evaluation for the core language: the **glued value
//! domain**, the per-run arena that owns it, its two policy parameters, the
//! machine that evaluates a core term to weak head, and the machine that reads
//! one back.
//!
//! - [`DomainArena`] owns every glued node one run produces. A node carries a
//!   [`TermFace`], and a neutral carries an [`Unfolding`] beside its neutral
//!   form.
//! - [`ValueClosure`] and [`CompClosure`] suspend a body over a two-zone
//!   [`Environment`].
//! - [`SchedulingPolicy`] and [`DuplicationPolicy`] are the parameters the
//!   domain is written against.
//! - [`eval_value`] and [`eval_computation`] evaluate to weak head;
//!   [`readback_value`] and [`readback_computation`] read back under a
//!   [`ReadbackMode`].
//! - [`convert_values`] and [`convert_computations`] run the conversion steps
//!   that need no search — identity, the [`Guard`] every node is minted with,
//!   and structural comparison — answering a [`Settlement`].
//!
//! The design, and what a caller must guarantee, is stated in this crate's
//! `README.md`, § Synopsis and § Expected features, and in the sections they
//! link.

#![no_std]

extern crate alloc;

mod arena;
mod closure;
mod conv;
mod domain;
mod eval;
mod guard;
mod policy;
mod readback;

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
pub use crate::policy::Copied;
pub use crate::policy::DuplicationPolicy;
pub use crate::policy::DuplicationStance;
pub use crate::policy::PolicyRefusal;
pub use crate::policy::SchedulingPolicy;
pub use crate::policy::SchedulingStance;
pub use crate::policy::Share;
pub use crate::policy::SharedPart;
pub use crate::readback::ReadbackFault;
pub use crate::readback::ReadbackMode;
pub use crate::readback::readback_computation;
pub use crate::readback::readback_value;
