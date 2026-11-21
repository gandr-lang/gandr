//! What a recording context keeps as each judgement of a typed run finishes:
//! the term, the type it was judged at and the binders it stood under. Beside
//! it, the value type that each judgement gives a binder of a bind and a field
//! of a structural former, which focusing writes into the IL (#8161).
//!
//! The context records, and the judgement's typed run reads the record back
//! (`judgement::elaboration`). The record's types live here, below both.

use alloc::vec::Vec;

use gandr_core_term::BinderDepth;
use gandr_core_term::Carried;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::FieldPosition;

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

/// A place of the IL whose value type the judgement gives (#8161).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Site
{
    /// The binder of each bind that runs this computation.
    Binder(ComputationId),
    /// A producer field of this structural former, at this position, in the
    /// order in which focusing pushes the former's fields.
    Field(ValueId, FieldPosition),
}

/// The value type that the judgement gives one [`Site`], read under the
/// intuitionistic binders open there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Annotation
{
    /// The site.
    pub site: Site,
    /// Its value type.
    pub ty: ValueTypeId,
    /// The intuitionistic binders open at the site: the context
    /// [`Self::ty`] is read under.
    pub depth: BinderDepth,
}
