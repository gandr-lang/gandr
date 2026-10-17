//! The store a run's answer moves into: an append-only heap of values and
//! the environment chains their closures close over.
//!
//! [`HeapValue`]s are immutable once allocated and addressed by
//! [`HeapValueId`]; sharing a value is sharing its address. An
//! [`Environment`] is the innermost binding of a persistent chain of producer
//! bindings, so extending one never copies it and a closure captures one by
//! value. A literal stack is held as the core writes one, innermost frame
//! first, each bind frame a [`ClosedCommand`].
//!
//! # The run keeps its own regions
//!
//! `gandr-runtime-emitter` runs a command over regions of its own and moves
//! into the store only what leaves the run: a host request's payload, the
//! answer, and the values a stuck run names. Readback reads the store. The
//! alternative was readback over the run's words, which no caller can hold
//! past the run: the regions are the thread's, reused by its next run. The
//! choice reverses if a run's regions come to outlive it, when readback can
//! read them in place and the move disappears.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;

use crate::boundary::FamilyAddress as _;
use crate::boundary::address_wrapper;
use crate::il::CommandId;
use crate::il::ConstructorTag;
use crate::il::ProducerId;

address_wrapper! {
    /// The address of a [`HeapValue`] in a [`Store`].
    pub struct HeapValueId;
}

address_wrapper! {
    /// The address of one producer binding of an environment chain.
    struct ValueBindingId;
}

/// A value a run answered with or named: what a producer evaluates to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum HeapValue
{
    /// A literal stack, innermost frame first.
    Stack
    {
        /// Each frame: an application's argument, a projection's side, or a
        /// bind frame's command closed over its environment.
        frames: Box<[StackFrame<HeapValueId, ClosedCommand>]>,
    },
    /// A base-type literal.
    Literal(Literal),
    /// A constructor applied to evaluated fields.
    Constructed
    {
        /// The head.
        tag: ConstructorTag,
        /// The fields, left to right.
        fields: Box<[HeapValueId]>,
    },
    /// A thunk: a suspended command and the environment it closes over.
    Thunk
    {
        /// The suspended command, binding one covariable.
        body: CommandId,
        /// The captured environment.
        environment: Environment,
    },
    /// A recursive thunk: a thunk whose forcing binds the thunk itself as its
    /// body's innermost producer variable, beside the continuation.
    Fixpoint
    {
        /// The suspended command, binding one producer variable and one
        /// covariable.
        body: CommandId,
        /// The captured environment, without the thunk itself.
        environment: Environment,
        /// The termination claim the core fixpoint carried.
        evidence: gandr_kernel_term::FixpointEvidence,
    },
    /// A negative value: a copattern object or a suspended context capture,
    /// closed over its environment.
    Closure
    {
        /// The closed producer: a [`crate::ProducerNode::Cocase`] or a
        /// [`crate::ProducerNode::Mu`].
        producer: ProducerId,
        /// The captured environment.
        environment: Environment,
    },
    /// A constant with no body to run: an owed or refused declaration, which
    /// a run carries as itself.
    Opaque(ConstantIndex),
    /// A capability a handler introduced: its address is its identity.
    Capability,
}

/// A bind frame's command and the environment it runs under.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ClosedCommand
{
    /// The command, binding one producer variable and one covariable.
    pub body: CommandId,
    /// The environment it runs under.
    pub environment: Environment,
}

/// The innermost producer binding of an environment, or none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ValueScope
{
    /// No producer is bound.
    Empty,
    /// The innermost binding.
    Innermost(ValueBindingId),
}

/// An environment: the producer chain a closed command runs under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Environment
{
    /// The producer bindings, innermost first.
    values: ValueScope,
}

impl Environment
{
    /// The environment binding nothing.
    pub const EMPTY: Self = Self {
        values: ValueScope::Empty,
    };
}

/// One producer binding: the value and the chain it extends.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ValueBinding
{
    /// The bound value.
    value: HeapValueId,
    /// The chain this binding extends.
    outer: ValueScope,
}

/// The families of the store, for a full-family refusal.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HeapFamily
{
    /// The values.
    Values,
    /// The producer bindings.
    ValueBindings,
}

/// Why the store refused an operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StoreFault
{
    /// A family has reached its address ceiling.
    RegionFull(HeapFamily),
}

impl fmt::Display for StoreFault
{
    /// Names the full family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::RegionFull(family) => {
                let name = match family {
                    HeapFamily::Values => "value",
                    HeapFamily::ValueBindings => "producer binding",
                };
                write!(f, "the {name} family of the store is full")
            },
        }
    }
}

impl core::error::Error for StoreFault
{
}

/// The values a run moved out and the environments they close over.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Store
{
    /// The values.
    values: Vec<HeapValue>,
    /// The producer bindings of every environment chain.
    value_bindings: Vec<ValueBinding>,
}

impl Store
{
    /// An empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Allocate a value.
    ///
    /// # Specification
    /// - requires: every address `value` names was allocated by this store.
    /// - ensures: on success a fresh address, above every value address already
    ///   allocated, reading back as `value`.
    /// - provides: the one append point of the value family.
    /// - fails: [`StoreFault::RegionFull`] at the address ceiling, the store
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dense distinct allocations, exact retrieval and the
    ///   first missing offset distinguish address reuse, a shifted offset and a
    ///   misplaced value. The helper covers the ceiling with zero-sized slices;
    ///   the store is not populated to the ceiling.
    /// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[spec(
        captures: [entry = self.values.len()],
        ensures: |ret| match ret {
            | Ok(id) => usize::try_from(u32::from(id)) == Ok(entry)
                && entry.checked_add(1) == Some(self.values.len()),
            | Err(error) => error == StoreFault::RegionFull(HeapFamily::Values)
                && self.values.len() == entry,
        },
    )]
    pub fn allocate(
        &mut self,
        value: HeapValue,
    ) -> Result<HeapValueId, StoreFault>
    {
        let id =
            HeapValueId::next_in(&self.values).ok_or(StoreFault::RegionFull(HeapFamily::Values))?;
        self.values.push(value);
        Ok(id)
    }

    /// Resolve a value address, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some(value)` exactly when the store allocated the address.
    /// - provides: the read side of the value family.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, first, last and exact-end reads observe
    ///   distinct values, distinguishing a wrong offset and endpoint
    ///   acceptance.
    /// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        | Some(value) => usize::try_from(u32::from(id)).ok()
            .and_then(|offset| self.values.get(offset))
            .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(value))),
        | None => usize::try_from(u32::from(id)).map_or(true, |offset| offset >= self.values.len()),
    })]
    pub fn value(
        &self,
        id: HeapValueId,
    ) -> Option<&HeapValue>
    {
        id.read_in(&self.values)
    }

    /// Extend an environment's producer chain with one binding.
    ///
    /// # Specification
    /// - requires: `value` and the chain were allocated by this store.
    /// - ensures: on success an environment whose walk reads `value` first and
    ///   then what `environment`'s walk reads.
    /// - provides: the one way a producer variable is bound.
    /// - fails: [`StoreFault::RegionFull`], the store unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two bindings walked from the inner and from the outer
    ///   environment separate the shift from the base.
    /// - witness: `store::tests::environments_bind_innermost_first`
    #[inline]
    #[spec(
        captures: [entry = self.value_bindings.len()],
        ensures: |ret| match ret {
            | Ok(extended) => entry.checked_add(1) == Some(self.value_bindings.len())
                && match extended.values {
                    | ValueScope::Empty => false,
                    | ValueScope::Innermost(id) => usize::try_from(u32::from(id)) == Ok(entry)
                        && id.read_in(&self.value_bindings).is_some_and(|binding|
                            binding.value == value && binding.outer == environment.values),
                },
            | Err(error) => error == StoreFault::RegionFull(HeapFamily::ValueBindings)
                && self.value_bindings.len() == entry,
        },
    )]
    pub fn bind_value(
        &mut self,
        environment: Environment,
        value: HeapValueId,
    ) -> Result<Environment, StoreFault>
    {
        let id = ValueBindingId::next_in(&self.value_bindings)
            .ok_or(StoreFault::RegionFull(HeapFamily::ValueBindings))?;
        self.value_bindings.push(ValueBinding {
            value,
            outer: environment.values,
        });
        Ok(Environment {
            values: ValueScope::Innermost(id),
        })
    }

    /// The values an environment's producer chain binds, innermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the `i`-th item is the value bound `i` links out from the
    ///   innermost; the walk ends past the chain or at a dangling link.
    /// - provides: the closing substitution a readback builds from a captured
    ///   environment, in one pass.
    /// - fails: never; a dangling link ends the walk.
    /// - panics: none.
    /// - executable: none — anodized cannot instrument a postcondition on this
    ///   opaque return type (E0562: `impl Trait` in a closure return type).
    ///   There is no nontrivial precondition; replacing the opaque return type
    ///   would change the public API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-element chains, distinct payloads and a
    ///   dangling link distinguish reversed order, a dropped binding and a walk
    ///   past the chain.
    /// - witness: `store::tests::environments_bind_innermost_first`
    /// - witness: `store::tests::a_dangling_chain_binds_nothing`
    #[inline]
    pub fn bound_values(
        &self,
        environment: Environment,
    ) -> impl Iterator<Item = HeapValueId>
    {
        let mut scope = environment.values;
        core::iter::from_fn(move || {
            let ValueScope::Innermost(id) = scope
            else {
                return None;
            };
            let binding = id.read_in(&self.value_bindings)?;
            scope = binding.outer;
            Some(binding.value)
        })
    }
}

#[cfg(test)]
mod tests;
