//! What a recording context keeps as each judgement of a typed run finishes:
//! the term, the type it was judged at and the binders it stood under.
//!
//! The context records, and the judgement's typed run reads the record back
//! (`judgement::elaboration`). The record's types live here, below both.

use alloc::vec::Vec;

use gandr_core_term::BinderDepth;
use gandr_core_term::Carried;
use gandr_kernel_strata::Level;

use crate::refusal::TermNode;
use crate::refusal::TypeNode;

/// A term judgement a typed run finished: the term, the type it was judged
/// at, and how many intuitionistic binders were open where it was judged.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Typing
{
    /// The term judged.
    pub term: TermNode,
    /// The type the term was checked against, or the type it synthesised.
    pub ty: TypeNode,
    /// The intuitionistic binders open where the judgement began: the context
    /// [`Self::ty`] is read under.
    pub depth: BinderDepth,
}

/// A type formation a typed run finished: the type and the level it formed
/// at, read under the binders it was formed under.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Formed
{
    /// The type formed.
    pub ty: TypeNode,
    /// The level it formed at.
    pub level: Level,
}

/// What a recording context kept: the term judgements, the type formations,
/// the endpoints' standings, the world register's moves, and the nodes the
/// kept types were copied to, each in the order finished.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Kept
{
    /// The term judgements finished.
    pub typings: Vec<Typing>,
    /// The type formations finished.
    pub formed: Vec<Formed>,
    /// The session type each action's endpoint stood at, keyed by the action.
    pub endpoints: Vec<Typing>,
    /// The world register's moves, in the order made.
    pub moves: Vec<crate::worlds::WorldMove>,
    /// Each node a kept type was copied to when it was settled, beside the
    /// node it copies, in the order minted.
    pub copies: Vec<Carried>,
}
