//! The **glued value domain**: both faces and both closure spaces named on the
//! domain's own types, the per-run arena that owns them, the two policy
//! parameters the domain is written against, the machine that evaluates a core
//! term to weak head over it, and the machine that reads one back.
//!
//! The crate holds the domain's **shape**, the walk that fills it, and the walk
//! that chooses among what was filled. It holds no sharing overlay and no
//! conversion machine.
//!
//! # Two faces, filled by one walk and chosen by the other
//!
//! Readback chooses a face and conversion forces a face, so the two policies
//! are one table and a domain that grew the second face after the first was in
//! use would get two tables that disagree at the seams.
//!
//! **The term face** caches the core term a domain value came from, and keeps
//! it exactly while nothing inside the value reduced — so an unreduced subterm
//! reads back as an id rather than a rebuild, and the sharing the core arena
//! carried survives the round trip. The moment anything reduces the face says
//! so, because a stale source id is a wrong readback rather than a slow one.
//!
//! **The unfolding face** keeps a neutral's neutral form beside its lazily
//! forced unfolded form. Forcing adds the second reading and never replaces the
//! first, which is what lets conversion compare neutral forms and fall back to
//! unfolding rather than choosing between them.
//!
//! # Two closure spaces, named together
//!
//! A suspended body is a value body or a computation body, and entering a
//! closure is one operation — so both spaces are named now even though only the
//! computation space has producers at today's vocabulary. The environment they
//! close over mirrors the typing context's two zones, which is forced rather
//! than preferred: an occurrence names a zone, and a single-stack environment
//! could not answer a linear one.
//!
//! # Two policy parameters, from day one
//!
//! **Scheduling** carries a uniform-fair default with the height-weighted
//! stance behind it. The property the module enforces is that every stance
//! gives every height a strictly positive share: a definitional height is
//! allowed to change how fast a process runs and never which proofs exist.
//!
//! **Duplication** carries the erase-and-clone baseline, which is the unshared
//! reference every later stance replays against, with the spinal stance
//! representable and refused at installation while the conversion trace that
//! would certify it is absent.
//!
//! # Evaluation stops at weak head, and expands sharing
//!
//! The machine is a task stack and two result stacks rather than two mutually
//! recursive functions, so its depth lives on the heap. It sets the term face
//! by a check rather than a convention, reads the unfolding face off the
//! definition chain through the scope's transparency, and expands nothing: a
//! constant becomes a neutral carrying its body, never the body itself.
//!
//! It walks a core term's DAG as a tree, so a node reached twice is evaluated
//! twice. Removing that cost belongs under the duplication parameter rather
//! than inside the evaluator, and the fuel budget is what bounds the expansion
//! meanwhile.
//!
//! # Readback chooses a face, and drives evaluation to do it
//!
//! Readback is the same machine shape — task stack, result stacks, fuel — over
//! the domain rather than over the syntax, and it is where the two faces stop
//! being unread. [`ReadbackMode::ZeroUnfold`] prefers the term face, so an
//! unreduced node hands back the core id it came from and mints nothing, and it
//! forces no unfolding at all; [`ReadbackMode::Unfolding`] rebuilds every node
//! and spends an unfolding already forced.
//!
//! Going under a binder mints a fresh variable at a de Bruijn **level** and
//! evaluates the closure's body against it, so the readback drives evaluation
//! from the same fuel budget and the levels it minted are converted back to the
//! indices the syntax counts in.
//!
//! The named ideas, the crate's status, and its plan-milestone mapping are in
//! this crate's `README.md`.

#![no_std]

extern crate alloc;

mod arena;
mod closure;
mod domain;
mod eval;
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
pub use crate::eval::eval_computation;
pub use crate::eval::eval_value;
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
