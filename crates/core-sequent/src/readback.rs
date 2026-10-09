//! Readback: a heap value of the L machine read back as a core term.
//!
//! A positive value reads back as the core value it is: a literal as
//! itself, a constructed value over its fields' readbacks, an opaque constant
//! as the constant, and a thunk as its suspended command decoded back by the
//! unfocusing walk and closed over its environment's readbacks. A run's
//! terminal reads back as a computation: `return v` for a positive value, and
//! the function itself for a copattern object, closed the same way. A
//! suspended `μ` has no core reading.
//!
//! Values are read in increasing address order. Every value the machine
//! allocates names only values allocated before it, so each value's
//! dependencies are read before it, and the readback is a loop with no
//! recursion; a value naming a later one is refused as dangling.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;

use crate::il::CommandArena;
use crate::il::ConstructorTag;
use crate::il::ProducerNode;
use crate::store::Environment;
use crate::store::HeapValue;
use crate::store::HeapValueId;
use crate::store::Store;
use crate::unfocus::Decoded;
use crate::unfocus::Root;
use crate::unfocus::UnfocusRefusal;
use crate::unfocus::decode;

/// Why a heap value has no core reading.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ReadbackRefusal
{
    /// The value has none: a suspended `μ`, a copattern object standing as a
    /// value, or a constructed value whose fields contradict its head.
    Unreadable(HeapValueId),
    /// A value address the store does not hold, or one named by a value
    /// allocated before it.
    Dangling(HeapValueId),
    /// A thunk's or a function's suspended command has no core reading.
    Decode(UnfocusRefusal),
}

impl fmt::Display for ReadbackRefusal
{
    /// Names the value with no reading.
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
            | Self::Unreadable(id) => write!(f, "value {id} has no core reading"),
            | Self::Dangling(id) => write!(f, "value {id} is not readable from the store"),
            | Self::Decode(refusal) => {
                write!(f, "a suspended command has no core reading: {refusal}")
            },
        }
    }
}

impl core::error::Error for ReadbackRefusal
{
}

impl From<UnfocusRefusal> for ReadbackRefusal
{
    /// Carries the decoder's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: UnfocusRefusal) -> Self
    {
        Self::Decode(refusal)
    }
}

/// Read a positive heap value back as a core value.
///
/// # Specification
/// - requires: `store` was built by runs over `arena`.
/// - ensures: on success the core value the heap value denotes, closed.
/// - provides: the readback of a value.
/// - fails: [`ReadbackRefusal`] naming the first value with no reading; `core`
///   is then exactly as on entry.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
pub fn read_back_value(
    arena: &CommandArena,
    store: &Store,
    value: HeapValueId,
    core: &mut CoreArena,
) -> Result<ValueId, ReadbackRefusal>
{
    let mark = core.watermark();
    let mut reading = Reading::new(arena, store, core);
    let answer = reading.read([value]).and_then(|()| reading.lookup(value));
    if answer.is_err() {
        core.truncate_to(mark);
    }
    answer
}

/// Read a run's terminal back as a core computation.
///
/// # Specification
/// - requires: as [`read_back_value`].
/// - ensures: on success `return v` for a positive value `v`, and the function
///   a copattern object denotes, closed over its environment.
/// - provides: the readback of a halted run.
/// - fails: as [`read_back_value`], with the same rollback.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
pub fn read_back_terminal(
    arena: &CommandArena,
    store: &Store,
    value: HeapValueId,
    core: &mut CoreArena,
) -> Result<ComputationId, ReadbackRefusal>
{
    let mark = core.watermark();
    let answer = terminal(arena, store, value, core);
    if answer.is_err() {
        core.truncate_to(mark);
    }
    answer
}

/// [`read_back_terminal`] without its rollback.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`read_back_terminal`].
fn terminal(
    arena: &CommandArena,
    store: &Store,
    value: HeapValueId,
    core: &mut CoreArena,
) -> Result<ComputationId, ReadbackRefusal>
{
    let held = store.value(value).ok_or(ReadbackRefusal::Dangling(value))?;
    if let &HeapValue::Closure {
        producer,
        environment,
    } = held
    {
        let Some(&ProducerNode::Cocase { .. }) = arena.producer(producer)
        else {
            return Err(ReadbackRefusal::Unreadable(value));
        };
        let mut reading = Reading::new(arena, store, core);
        let closing = reading.closing(environment)?;
        return match decode(arena, Root::Function(producer), core, &closing)? {
            | Decoded::Computation(function) => Ok(function),
            | Decoded::Value(_) => Err(UnfocusRefusal::DecodeInvariant.into()),
        };
    }
    let mut reading = Reading::new(arena, store, core);
    reading.read([value])?;
    let read = reading.lookup(value)?;
    Ok(core.computation_return(read))
}

/// The state of one readback.
struct Reading<'run>
{
    /// The IL the store's suspended commands live in.
    arena: &'run CommandArena,
    /// The store read from.
    store: &'run Store,
    /// The core arena built into.
    core: &'run mut CoreArena,
    /// Each value read so far, with its core reading.
    read: BTreeMap<HeapValueId, ValueId>,
}

impl<'run> Reading<'run>
{
    /// A readback with nothing read yet.
    ///
    /// # Specification
    /// trivial.
    fn new(
        arena: &'run CommandArena,
        store: &'run Store,
        core: &'run mut CoreArena,
    ) -> Self
    {
        Self {
            arena,
            store,
            core,
            read: BTreeMap::new(),
        }
    }

    /// The readings of an environment's bound values, innermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one closed core value per binding, innermost first.
    /// - provides: the closing substitution of a suspended command.
    /// - fails: as [`Self::read`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn closing(
        &mut self,
        environment: Environment,
    ) -> Result<Vec<ValueId>, ReadbackRefusal>
    {
        let store = self.store;
        self.read(store.bound_values(environment))?;
        store
            .bound_values(environment)
            .map(|bound| self.lookup(bound))
            .collect()
    }

    /// Read every value reachable from `roots`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every value reachable from `roots` through fields and
    ///   captured environments has its reading recorded.
    /// - provides: the loop every readback drives.
    /// - fails: [`ReadbackRefusal::Unreadable`] for a closure reached,
    ///   [`ReadbackRefusal::Dangling`] for an address the store does not hold
    ///   or one read before the value naming it, and a suspended command's
    ///   decoding refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn read(
        &mut self,
        roots: impl IntoIterator<Item = HeapValueId>,
    ) -> Result<(), ReadbackRefusal>
    {
        let store = self.store;
        let mut reachable: BTreeSet<HeapValueId> = BTreeSet::new();
        let mut pending: Vec<HeapValueId> = roots.into_iter().collect();
        while let Some(id) = pending.pop() {
            if self.read.contains_key(&id) || !reachable.insert(id) {
                continue;
            }
            match *store.value(id).ok_or(ReadbackRefusal::Dangling(id))? {
                | HeapValue::Literal(_) | HeapValue::Opaque(_) => {},
                | HeapValue::Constructed { ref fields, .. } => {
                    pending.extend(fields.iter().copied());
                },
                | HeapValue::Thunk { environment, .. } => {
                    pending.extend(store.bound_values(environment));
                },
                | HeapValue::Closure { .. } => return Err(ReadbackRefusal::Unreadable(id)),
            }
        }
        for id in reachable {
            let reading = self.reading(id)?;
            self.read.insert(id, reading);
        }
        Ok(())
    }

    /// The reading of one value whose dependencies are read.
    ///
    /// # Specification
    /// - requires: every value `id` names was read before it.
    /// - ensures: the core value `id` denotes.
    /// - provides: one row of the readback table.
    /// - fails: as [`Self::read`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn reading(
        &mut self,
        id: HeapValueId,
    ) -> Result<ValueId, ReadbackRefusal>
    {
        let store = self.store;
        let held = store.value(id).ok_or(ReadbackRefusal::Dangling(id))?;
        match *held {
            | HeapValue::Literal(ref literal) => Ok(self.core.value_literal(literal.clone())),
            | HeapValue::Opaque(constant) => Ok(self.core.value_constant(constant)),
            | HeapValue::Constructed {
                ref tag,
                ref fields,
            } => match (tag, fields.as_ref()) {
                | (&ConstructorTag::Unit, &[]) => Ok(self.core.value_unit()),
                | (&ConstructorTag::Pair, &[first, second]) => {
                    let first = self.lookup(first)?;
                    let second = self.lookup(second)?;
                    Ok(self.core.value_pair(first, second))
                },
                | (&ConstructorTag::Injection(side), &[body]) => {
                    let body = self.lookup(body)?;
                    Ok(self.core.value_injection(side, body))
                },
                | (&ConstructorTag::Lift(ref level), &[body]) => {
                    let body = self.lookup(body)?;
                    Ok(self.core.value_lift(level.clone(), body))
                },
                | _ => Err(ReadbackRefusal::Unreadable(id)),
            },
            | HeapValue::Thunk {
                body, environment, ..
            } => {
                let closing = store
                    .bound_values(environment)
                    .map(|bound| self.lookup(bound))
                    .collect::<Result<Vec<_>, _>>()?;
                match decode(self.arena, Root::ThunkBody(body), self.core, &closing)? {
                    | Decoded::Value(thunk) => Ok(thunk),
                    | Decoded::Computation(_) => Err(UnfocusRefusal::DecodeInvariant.into()),
                }
            },
            | HeapValue::Closure { .. } => Err(ReadbackRefusal::Unreadable(id)),
        }
    }

    /// The recorded reading of a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reading [`Self::read`] recorded for `id`.
    /// - provides: a dependency's reading.
    /// - fails: [`ReadbackRefusal::Dangling`] when none is recorded.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn lookup(
        &self,
        id: HeapValueId,
    ) -> Result<ValueId, ReadbackRefusal>
    {
        self.read
            .get(&id)
            .copied()
            .ok_or(ReadbackRefusal::Dangling(id))
    }
}
