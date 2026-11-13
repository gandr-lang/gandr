//! The records of capabilities that the lowering's context holds.
//!
//! The classification reads an exercise, a perform, a returner's row and a
//! capability scope into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use answered::Answering;
use gandr_core_term::Sort;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::host::HostSignatures;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Sink;
use super::lowered;
use crate::by_form::FormStretch;
use crate::form::Placed;
use crate::module::ForeignInterface;
use crate::module::ForeignType;
use crate::origin::Insertion;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
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

/// Where a theory's signature stands: where its fixed types were read, in the
/// signature's telescope, or in the term context of a frame under it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Standing
{
    /// Where the fixed types were read: a row in a declaration's type.
    Read,
    /// The term context of this frame: a scope's, or an exercise's.
    Term(Frame),
}

/// The host signatures the mint sweep has minted into the module's arena.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub enum Host
{
    /// No capability form has been minted.
    Unminted,
    /// The host table, in the module's arena.
    Minted(HostSignatures),
}

impl Sink<'_>
{
    /// The host table in the module's arena, minted at the first call, each
    /// of its types at `origin`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the host table, every type of which resolves in the arena; it
    ///   is minted at most once per sink.
    /// - fails: the unminted absence if the host table conflicts with itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module with capability forms over two interfaces
    ///   mints one table and checks.
    /// - witness: `gandr-surface-lowering::lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    #[spec(ensures: |ref ret| match *ret {
        | Maybe::Present(table) => table.interfaces().iter().all(|signature| signature.types().all(|ty| self.arena.value_type(ty).is_some())),
        | Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn host(
        &mut self,
        origin: Origin,
    ) -> Maybe<&HostSignatures, lowered::Absent>
    {
        if matches!(self.host, Host::Unminted) {
            let mark = self.arena.watermark();
            let Ok(minted) = HostSignatures::new(self.arena)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            for id in self.arena.value_types_since(mark) {
                self.origins.record_value_type(id, origin);
            }
            self.host = Host::Minted(minted);
        }
        match self.host {
            Host::Minted(ref table) => Maybe::Present(table),
            Host::Unminted => Maybe::Absent(lowered::Absent::Unminted),
        }
    }

    /// The signature of the host interface `interface` in the module's arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the interface's signature, as [`Self::host`] mints it; the
    ///   unminted absence for a name the host does not declare, which the
    ///   classification rules out.
    /// - fails: as [`Self::host`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::host`].
    /// - witness: `gandr-surface-lowering::lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    #[spec(ensures: |ref ret| match *ret {
        | Maybe::Present(ref signature) => signature.name() == interface,
        | Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn signature(
        &mut self,
        interface: &EffectName,
        origin: Origin,
    ) -> Maybe<EffectSig, lowered::Absent>
    {
        self.host(origin)
            .and_then(|table| match table.named(interface) {
                Maybe::Present(signature) => Maybe::Present(signature.clone()),
                Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
            })
    }

    /// The signature of the extern block's interface `foreign` in the
    /// module's arena, minted at the first call, each member type where the
    /// member writes it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one operation per member, in order, its payload the unit for
    ///   no parameter, the parameter's width for one and the product of their
    ///   widths in order for several, as a call passes its arguments, and its
    ///   reply its result's width; minted at the first call for the block, as
    ///   [`Self::foreign_type`] mints each member type, the product inserted at
    ///   the member's name, and the same signature at every call after.
    /// - fails: the unminted absence for a block naming one member twice, which
    ///   the collection refuses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row and two performs of one block check against one
    ///   signature.
    /// - witness: `gandr-surface-lowering::lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
    #[spec(ensures: |ref ret| match *ret {
        | Maybe::Present(ref signature) => signature.name() == &foreign.name
            && signature.operations().len() == foreign.operations.len(),
        | Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn foreign(
        &mut self,
        foreign: &ForeignInterface,
    ) -> Maybe<EffectSig, lowered::Absent>
    {
        if let Some(minted) = self.foreign.get(&foreign.named.start()) {
            return Maybe::Present(minted.clone());
        }
        let mut operations: Vec<EffectOp> = Vec::with_capacity(foreign.operations.len());
        let mut parameters: Vec<ValueTypeId> = Vec::new();
        for operation in &foreign.operations {
            parameters.clear();
            for parameter in &operation.parameters {
                parameters.push(self.foreign_type(parameter.ty));
            }
            let payload = if let [only] = *parameters.as_slice() {
                only
            }
            else {
                let product = self.arena.value_type_product(&parameters);
                let named = Origin::new(operation.named.node, operation.named.span);
                self.origins
                    .record_value_type(product, named.inserted(Insertion::Foreign));
                product
            };
            let reply = self.foreign_type(operation.result);
            operations.push(EffectOp {
                name: operation.name.clone(),
                payload,
                reply,
            });
        }
        let Ok(signature) = EffectSig::new(foreign.name.clone(), operations)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let _first = self
            .foreign
            .insert(foreign.named.start(), signature.clone());

        Maybe::Present(signature)
    }

    /// The base type an extern block's member writes as `written`, read at
    /// its kind there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh base type of `written`'s width, recorded as written
    ///   at the bytes that write it, and a kind label there naming a fresh
    ///   value universe inserted for the block: no judgement forms the type
    ///   where it is written, so it answers at its kind, as a functor
    ///   parameter's abstract type does.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each member type of a block answers at its own bytes,
    ///   whether or not a declaration performs the block's operations.
    /// - witness: `gandr-surface-lowering::lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
    #[spec(
        captures: labels = self.origins.labels().len(),
        ensures: |ret| matches!(self.arena.value_type(ret), Some(&ValueType::Base(BaseType::Fixed(width))) if width == written.width)
            && self.origins.labels().len() == labels.saturating_add(1),
    )]
    #[inline]
    pub fn foreign_type(
        &mut self,
        written: ForeignType,
    ) -> ValueTypeId
    {
        let at = Origin::new(written.written.node, written.written.span);
        let ty = self.arena.value_type_base(BaseType::Fixed(written.width));
        self.origins.record_value_type(ty, at);
        let kind = self
            .arena
            .value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        self.origins
            .record_value_type(kind, at.inserted(Insertion::Foreign));
        self.origins.record_label(Label {
            span: written.written.span,
            labelled: Labelled::Kind(kind),
        });
        ty
    }
}

/// What a binder's declared type states to a call its name heads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Stated
{
    /// A continuation's type, `Stack(C, D)`: the call resumes it.
    Stack,
    /// Any other type: the call applies it.
    Other,
}
