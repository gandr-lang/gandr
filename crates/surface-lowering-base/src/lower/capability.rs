//! The records of capabilities that the lowering's context holds.
//!
//! The classification reads an exercise, a perform, a returner's row and a
//! capability scope into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use answered::Answering;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::capability::Region;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use crate::by_form::FormStretch;
use crate::form::Placed;
use crate::module::ForeignInterface;
use crate::resolve::Frame;

pub mod answered;
pub mod theory;

pub use theory::TheoryInterface;

/// The operations a capability type grants, named bare.
pub type Authority = BTreeSet<OperationName>;

/// What performs an operation a call `x.op(v, …)` selects.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Performer
{
    /// `c.op(v)`: the capability `c` names is exercised, of the theory its
    /// scope handles where one does.
    Capability(NodeIndex, Option<Arc<TheoryInterface>>),
    /// `I.op(v)`: the operation of the host interface `I` is performed by
    /// name, handled by whichever handler stands nearest when it runs — the
    /// host's at the program's entry.
    Interface(EffectName),
}

/// The interface a form names: a host interface, a theory a capability scope
/// handles or a row names at the sorts it fixes, or an extern block's.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Interface
{
    /// The host interface of this name.
    Host(EffectName),
    /// The theory a capability scope or a row reads as an interface.
    Theory(Arc<TheoryInterface>),
    /// The interface an extern block of the source declares, which the host
    /// the run is offered to answers.
    Foreign(Arc<ForeignInterface>),
}

impl Interface
{
    /// The name a row keys the interface's default instance by: the host
    /// interface's, the theory's or the extern block's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &EffectName
    {
        match *self {
            Self::Host(ref name) => name,
            Self::Theory(ref theory) => &theory.name,
            Self::Foreign(ref foreign) => &foreign.name,
        }
    }
}

/// An exercise `c.op(v, …)` or a perform `I.op(v, …)`, as the classification
/// read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Exercised
{
    /// What performs the operation.
    pub performer: Performer,
    /// The interface the operation belongs to.
    pub interface: Interface,
    /// The operation exercised.
    pub operation: OperationName,
    /// The bytes of the head `c.op` that selects it.
    pub head: ByteSpan,
    /// The frame the exercise is read under.
    pub frame: Frame,
    /// The payload's values, in the lowerer's operand store.
    pub payload: FormStretch,
}

quenchant_shape::reason_enum! {
    /// Why a returner's row stands open through no tail.
    pub mod tail {
        /// The row is closed: it names its interfaces alone.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no `| t` after the interfaces.
            Closed,
        }
    }
}

/// A returner's row, `[I, …]`, `[a : I, …]`, `[I, … | t]` or `[t]`, each
/// entry a host interface or a theory at the sorts it fixes, `[T with sort x
/// = A]`, as the classification read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenRow
{
    /// The interfaces the row names whole, each its default instance, in
    /// name order.
    pub interfaces: Vec<Interface>,
    /// Each label `a : I` the row writes, its tile beside its interface.
    pub labels: Vec<(Placed, Interface)>,
    /// Each label's instance, its interface at the region its name resolves
    /// to, once the row is planned under its frame.
    pub placed: Vec<(Interface, Region)>,
    /// Each type a theory entry fixes a sort to, read as the row is planned.
    pub fixed: Vec<Placed>,
    /// Each theory entry's name, beside the theory it resolves to.
    pub named: Vec<(ByteSpan, ConstantIndex)>,
    /// The operand the row stays open through, read as a row value.
    pub tail: Maybe<NodeIndex, tail::Absent>,
}

/// A capability scope, as the classification read it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scoped
{
    /// The interface the scope handles.
    pub interface: Interface,
    /// The capability's binder, as written.
    pub binder: NodeIndex,
    /// The frame the scope is read under, where its manifest's types are read.
    pub frame: Frame,
    /// The subject, under the capability's binder.
    pub subject: Block,
    /// What answers the interface's operations.
    pub handlers: Handlers,
}

/// What answers a capability scope's operations, as the classification read
/// it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Handlers
{
    /// The clauses the scope writes, `with { … }`.
    Written(Written),
    /// The model answering a theory's scope: the module it names, `with N`,
    /// or the one model in scope, for a scope writing no `with`.
    Model(Arc<Answering>),
}

/// A capability scope's written clauses, as the classification read them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Written
{
    /// The return clause's body, under its result's binder.
    pub on_return: NodeIndex,
    /// The return clause's result binder, as written.
    pub result: NodeIndex,
    /// Each operation clause, in written order.
    pub clauses: Vec<Clause>,
}

/// An operation clause of a capability scope, as the classification read
/// it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Clause
{
    /// The operation the clause handles.
    pub operation: OperationName,
    /// The payload's binder, as written; none for `oper op(k)`.
    pub payload: Option<NodeIndex>,
    /// The continuation's binder, as written.
    pub continuation: NodeIndex,
    /// The body, under the clause's binders.
    pub body: NodeIndex,
    /// The buffer the scope mints for the clause, for an operation that
    /// replies one.
    pub mint: Mint,
}

/// The buffer a clause's scope mints, by the names its clause gives it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mint
{
    /// The operation replies no buffer: the payload binder holds the payload.
    Unminted,
    /// The payload binder holds the pair of the payload and the mint, split
    /// into the payload's name and the mint's, the mint placed live.
    Minted
    {
        /// The mint's name, as written.
        mint: NodeIndex,
    },
}
