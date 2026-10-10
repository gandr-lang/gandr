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
///
/// # Adequacy
/// - hypothesis: L2 — closed first-order and captured terms are compared with
///   the independent normaliser, including a deliberately different injection.
///   L3 — malformed shapes, missing values and decoding failures preserve a
///   populated core prefix; this does not enumerate all programs.
/// - witness: `tests::differential::first_order_returns_compare_exactly`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
#[anodized::spec(
    captures: [entry = core.watermark()],
    ensures: |ret| match ret {
        | Ok(read) => store.value(value).is_some() && core.value(read).is_some(),
        | Err(_) => core.watermark() == entry,
    },
)]
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
///
/// # Adequacy
/// - hypothesis: L2 — closed first-order and captured terms are compared with
///   the independent normaliser, including a deliberately different injection.
///   L3 — malformed shapes, missing values and decoding failures preserve a
///   populated core prefix; this does not enumerate all programs.
/// - witness: `tests::differential::first_order_returns_compare_exactly`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
#[anodized::spec(
    captures: [entry = core.watermark()],
    ensures: |ret| match ret {
        | Ok(read) => store.value(value).is_some_and(|held| match held {
            | &HeapValue::Closure { .. } => matches!(core.computation(read), Some(&gandr_core_term::Computation::Lambda(_))),
            | _ => matches!(core.computation(read), Some(&gandr_core_term::Computation::Return(_))),
        }),
        | Err(_) => core.watermark() == entry,
    },
)]
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
/// - requires: as [`read_back_terminal`].
/// - ensures: a function for a copattern closure, otherwise a return of the
///   value's reading.
/// - provides: terminal dispatch before the caller's transactional boundary.
/// - fails: an absent or unreadable value, or a decoding refusal; intermediate
///   readings remain in the core arena.
/// - panics: none.
///
/// # Errors
/// As [`read_back_terminal`].
///
/// # Adequacy
/// - hypothesis: L2 — returned values and captured functions are compared with
///   normal forms; L3 — a capture used as a terminal has the exact unreadable
///   refusal. These distinguish dispatch to the wrong root kind.
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `machine::tests::a_suspended_capture_has_no_reading`
/// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
#[anodized::spec(ensures: |ret| match ret {
    | Ok(read) => store.value(value).is_some_and(|held| match held {
        | &HeapValue::Closure { .. } => matches!(core.computation(read), Some(&gandr_core_term::Computation::Lambda(_))),
        | _ => matches!(core.computation(read), Some(&gandr_core_term::Computation::Return(_))),
    }),
    | Err(error) => store.value(value).is_some() || error == ReadbackRefusal::Dangling(value),
})]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct outer and inner bindings are observed as
    ///   exact core values in reverse binding order, and lookup is refused
    ///   before recording. L2 — captured functions and thunks compare with the
    ///   independent normaliser, distinguishing omitted or reversed closing.
    /// - witness: `readback::tests::closing_records_innermost_values_and_exact_lookup`
    /// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
    #[anodized::spec(ensures: |ref ret| match ret.as_ref() {
        | Ok(values) => self.store.bound_values(environment).map(|id| self.read.get(&id).copied())
            .eq(values.iter().copied().map(Some))
            && values.iter().all(|id| self.core.value(*id).is_some()),
        | Err(_) => true,
    })]
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
    /// - requires: recorded heap addresses and core readings still resolve.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared, distinct fields and all first-order heads are
    ///   observed in the resulting core graph; a forward dependency is refused
    ///   at its exact address and malformed arity is refused after reading
    ///   dependencies. L2 — suspended bodies compare with normal forms.
    /// - witness: `readback::tests::shared_fields_preserve_their_order`
    /// - witness: `readback::tests::forward_dependencies_are_refused_before_reading_the_parent`
    /// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
    /// - witness: `tests::differential::thunks_compare_structurally_through_readback`
    #[anodized::spec(
        requires: self.read.iter().all(|(held, read)| self.store.value(*held).is_some() && self.core.value(*read).is_some()),
        ensures: |ret| ret.is_err() || self.read.iter().all(|(held, read)|
            self.store.value(*held).is_some() && self.core.value(*read).is_some()),
    )]
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

    /// The reading of one value, looking up its previously recorded
    /// dependencies.
    ///
    /// # Specification
    /// - requires: recorded heap addresses and core readings still resolve.
    /// - ensures: the core value `id` denotes.
    /// - provides: one row of the readback table.
    /// - fails: as [`Self::read`], including a dependency not yet recorded.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact literal, opaque, unit, pair, injection and lift
    ///   nodes distinguish changed payloads, head tags and field order; invalid
    ///   arity and a dependency read too early have exact refusals. L2 — thunk
    ///   readings compare with the independent normaliser.
    /// - witness: `readback::tests::shared_fields_preserve_their_order`
    /// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
    /// - witness: `readback::tests::forward_dependencies_are_refused_before_reading_the_parent`
    /// - witness: `tests::differential::thunks_compare_structurally_through_readback`
    #[anodized::spec(
        requires: self.read.iter().all(|(held, read)| self.store.value(*held).is_some() && self.core.value(*read).is_some()),
        ensures: |ret| match ret {
            | Err(error) => self.store.value(id).is_some() || error == ReadbackRefusal::Dangling(id),
            | Ok(read) => self.store.value(id).zip(self.core.value(read)).is_some_and(|(held, node)| match *held {
                | HeapValue::Literal(ref literal) => matches!(*node, gandr_core_term::Value::Literal(ref found) if found == literal),
                | HeapValue::Opaque(constant) => *node == gandr_core_term::Value::Constant(constant),
                | HeapValue::Constructed { ref tag, ref fields } => match (tag, fields.as_ref()) {
                    | (&ConstructorTag::Unit, &[]) => *node == gandr_core_term::Value::Unit,
                    | (&ConstructorTag::Pair, &[first, second]) => matches!(*node, gandr_core_term::Value::Pair(left, right)
                        if self.read.get(&first) == Some(&left) && self.read.get(&second) == Some(&right)),
                    | (&ConstructorTag::Injection(side), &[body]) => matches!(*node, gandr_core_term::Value::Injection(found, value)
                        if side == found && self.read.get(&body) == Some(&value)),
                    | (&ConstructorTag::Lift(ref level), &[body]) => matches!(*node, gandr_core_term::Value::Lift { ref target, body: value }
                        if target == level && self.read.get(&body) == Some(&value)),
                    | _ => false,
                },
                | HeapValue::Thunk { .. } => matches!(*node, gandr_core_term::Value::Thunk(_)),
                | HeapValue::Closure { .. } => false,
            }),
        },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held but unrecorded value is refused, then two
    ///   distinct recorded values return their exact core addresses; changing
    ///   the key, inventing a fallback or reversing the map is observable.
    /// - witness: `readback::tests::closing_records_innermost_values_and_exact_lookup`
    #[anodized::spec(ensures: |ret| ret == self.read.get(&id).copied().ok_or(ReadbackRefusal::Dangling(id)))]
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

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;

    use gandr_core_term::Value;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::StringLiteral;
    use gandr_theory_cell_complexes::Polarity;

    use super::*;
    use crate::il::ConsumerNode;
    use crate::il::CopatternArm;
    use crate::il::DestructorTag;

    /// A shared graph retains distinct ordered payloads and every first-order
    /// head.
    #[test]
    fn shared_fields_preserve_their_order()
    {
        let arena = CommandArena::new();
        let mut store = Store::new();
        let literal = Literal::Text(StringLiteral::new("payload".into()));
        let unit = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Unit,
                fields: Box::from([]),
            })
            .expect("room");
        let opaque = store
            .allocate(HeapValue::Opaque(7_usize.into()))
            .expect("room");
        let text = store
            .allocate(HeapValue::Literal(literal.clone()))
            .expect("room");
        let pair = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Pair,
                fields: Box::from([text, opaque]),
            })
            .expect("room");
        let injection = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Injection(Side::Right),
                fields: Box::from([unit]),
            })
            .expect("room");
        let lift = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Lift(Level::zero()),
                fields: Box::from([injection]),
            })
            .expect("room");
        let branch = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Pair,
                fields: Box::from([pair, lift]),
            })
            .expect("room");
        let root = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Pair,
                fields: Box::from([branch, branch]),
            })
            .expect("room");
        let mut core = CoreArena::new();
        let mut reading = Reading::new(&arena, &store, &mut core);
        reading.read([root]).expect("closed first-order graph");
        let read_unit = reading.lookup(unit).expect("recorded");
        let read_opaque = reading.lookup(opaque).expect("recorded");
        let read_text = reading.lookup(text).expect("recorded");
        let read_pair = reading.lookup(pair).expect("recorded");
        let read_injection = reading.lookup(injection).expect("recorded");
        let read_lift = reading.lookup(lift).expect("recorded");
        let read_branch = reading.lookup(branch).expect("recorded");
        let read_root = reading.lookup(root).expect("recorded");
        for (id, expected) in [
            (read_unit, Value::Unit),
            (read_opaque, Value::Constant(7_usize.into())),
            (read_text, Value::Literal(literal)),
            (read_pair, Value::Pair(read_text, read_opaque)),
            (read_injection, Value::Injection(Side::Right, read_unit)),
            (read_lift, Value::Lift {
                target: Level::zero(),
                body: read_injection,
            }),
            (read_branch, Value::Pair(read_pair, read_lift)),
            (read_root, Value::Pair(read_branch, read_branch)),
        ] {
            assert_eq!(Some(&expected), reading.core.value(id));
        }
    }

    /// Lookup distinguishes held from recorded values, and closing reverses
    /// binding order.
    #[test]
    fn closing_records_innermost_values_and_exact_lookup()
    {
        let arena = CommandArena::new();
        let mut store = Store::new();
        let outer = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Unit,
                fields: Box::from([]),
            })
            .expect("room");
        let inner = store
            .allocate(HeapValue::Opaque(7_usize.into()))
            .expect("room");
        let environment = store.bind_value(Environment::EMPTY, outer).expect("room");
        let environment = store.bind_value(environment, inner).expect("room");
        let mut core = CoreArena::new();
        let mut reading = Reading::new(&arena, &store, &mut core);
        assert_eq!(Err(ReadbackRefusal::Dangling(outer)), reading.lookup(outer));
        let closing = reading.closing(environment).expect("closed bindings");
        let inner_read = reading.lookup(inner).expect("recorded");
        let outer_read = reading.lookup(outer).expect("recorded");
        assert_eq!([inner_read, outer_read], closing.as_slice());
        assert_eq!(
            Some(&Value::Constant(7_usize.into())),
            reading.core.value(inner_read)
        );
        assert_eq!(Some(&Value::Unit), reading.core.value(outer_read));
        let missing = HeapValueId::from(u32::MAX);
        assert_eq!(
            Err(ReadbackRefusal::Dangling(missing)),
            reading.lookup(missing)
        );
    }

    /// Refusals after partial dependency or closing reads restore an existing
    /// core prefix.
    #[test]
    fn refusals_restore_an_existing_core_prefix()
    {
        let mut arena = CommandArena::new();
        let producer = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let body = arena
            .mint_cut(Polarity::Positive, producer, top)
            .expect("references resolve");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body })
            .expect("body resolves");
        let wrong_function = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([CopatternArm {
                    destructor: DestructorTag::Force,
                    body,
                }]),
            })
            .expect("body resolves");
        let mut store = Store::new();
        let unit = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Unit,
                fields: Box::from([]),
            })
            .expect("room");
        let opaque = store
            .allocate(HeapValue::Opaque(7_usize.into()))
            .expect("room");
        let malformed = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Pair,
                fields: Box::from([unit, opaque, unit]),
            })
            .expect("room");
        let environment = store.bind_value(Environment::EMPTY, opaque).expect("room");
        let captured = store
            .allocate(HeapValue::Closure {
                producer: capture,
                environment,
            })
            .expect("room");
        let function = store
            .allocate(HeapValue::Closure {
                producer: wrong_function,
                environment,
            })
            .expect("room");
        let cell = store.allocate_cell().expect("room");
        let thunk = store
            .allocate(HeapValue::Thunk {
                body,
                environment,
                cell,
            })
            .expect("room");
        let missing = HeapValueId::from(u32::MAX);
        let mut core = CoreArena::new();
        let prefix = core.value_constant(42_usize.into());
        let mark = core.watermark();
        for (value, positive_refusal, terminal_refusal) in [
            (
                missing,
                ReadbackRefusal::Dangling(missing),
                ReadbackRefusal::Dangling(missing),
            ),
            (
                malformed,
                ReadbackRefusal::Unreadable(malformed),
                ReadbackRefusal::Unreadable(malformed),
            ),
            (
                captured,
                ReadbackRefusal::Unreadable(captured),
                ReadbackRefusal::Unreadable(captured),
            ),
            (
                thunk,
                ReadbackRefusal::Decode(UnfocusRefusal::EscapingContinuation(top)),
                ReadbackRefusal::Decode(UnfocusRefusal::EscapingContinuation(top)),
            ),
            (
                function,
                ReadbackRefusal::Unreadable(function),
                ReadbackRefusal::Decode(UnfocusRefusal::ProducerOutsideTheImage(wrong_function)),
            ),
        ] {
            assert_eq!(
                Err(positive_refusal),
                read_back_value(&arena, &store, value, &mut core)
            );
            assert_eq!(mark, core.watermark());
            assert_eq!(
                Err(terminal_refusal),
                read_back_terminal(&arena, &store, value, &mut core)
            );
            assert_eq!(mark, core.watermark());
            assert_eq!(Some(&Value::Constant(42_usize.into())), core.value(prefix));
        }
    }

    /// A later-address dependency is rejected even when the store holds it.
    #[test]
    fn forward_dependencies_are_refused_before_reading_the_parent()
    {
        let arena = CommandArena::new();
        let mut store = Store::new();
        let future = HeapValueId::from(1_u32);
        let parent = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Pair,
                fields: Box::from([future, future]),
            })
            .expect("room");
        store
            .allocate(HeapValue::Opaque(7_usize.into()))
            .expect("room");
        let mut core = CoreArena::new();
        let mark = core.watermark();
        assert_eq!(
            Err(ReadbackRefusal::Dangling(future)),
            read_back_value(&arena, &store, parent, &mut core)
        );
        assert_eq!(mark, core.watermark());
        assert_eq!(
            Err(ReadbackRefusal::Dangling(future)),
            read_back_terminal(&arena, &store, parent, &mut core)
        );
        assert_eq!(mark, core.watermark());
    }
}
