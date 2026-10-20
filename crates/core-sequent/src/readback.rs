//! Readback: a run's heap value read back as a core term.
//!
//! A positive value reads back as the core value it is: a literal as
//! itself, a constructed value over its fields' readbacks — a datatype's
//! constructor at the unknown value type, since the IL carries no types — an
//! opaque constant as the constant, and a thunk or a recursive thunk as its
//! suspended command decoded back by the unfocusing walk and closed over its
//! environment's readbacks. A run's terminal reads back as a computation:
//! `return v` for a positive value, and the function itself for a copattern
//! object, closed the same way. A suspended `μ` has no core reading.
//!
//! A suspended command's environment binds exactly the intuitionistic
//! variables its support selects, innermost first
//! ([`CommandArena::captures`]), so readback pairs each bound value with the
//! index it closes; an environment that is not the support is refused by
//! name.
//!
//! Values are read in increasing address order. Every value a run moves into
//! the store names only values allocated before it, so each value's
//! dependencies are read before it, and the readback is a loop with no
//! recursion; a value naming a later one is refused as dangling.
//!
//! # Readback refuses rather than approximates
//!
//! [`read_back_terminal`] reads a positive terminal as `return v` and a
//! copattern object as the function it is; a literal reads as itself, a
//! constructed value over its fields — a datatype's constructor at the unknown
//! value type — an opaque constant as the constant, and a thunk, a recursive
//! thunk or a function as its suspended command decoded by the unfocusing walk
//! with its captured environment's readbacks substituted. Values are read in
//! increasing address order, since every value a run moves into the store names
//! only earlier ones, so the readback is a loop. A value with no core reading —
//! a suspended `μ`, a copattern object standing as a value — is refused by name
//! with the core arena at its mark.
//!
//! A placeholder of the right kind is not a readback: it could let a
//! differential pass on a value it never observed. Unsupported readings
//! therefore return a named refusal and restore the destination arena. This
//! boundary does not reverse merely to make an observation succeed.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::DeBruijnIndex;

use crate::il::CommandArena;
use crate::il::ConstructorTag;
use crate::il::ProducerNode;
use crate::il::Suspension;
use crate::store::Environment;
use crate::store::HeapValue;
use crate::store::HeapValueId;
use crate::store::Store;
use crate::unfocus::Closing;
use crate::unfocus::Decoded;
use crate::unfocus::Root;
use crate::unfocus::UnfocusRefusal;
use crate::unfocus::decode;

/// Why a heap value has no core reading.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ReadbackRefusal
{
    /// The value has none: a suspended `μ`, a copattern object standing as a
    /// value, a handler's capability, which no term introduces, or a
    /// constructed value whose fields contradict its head.
    Unreadable(HeapValueId),
    /// A value address the store does not hold, or one named by a value
    /// allocated before it.
    Dangling(HeapValueId),
    /// A thunk's or a function's suspended command has no core reading.
    Decode(UnfocusRefusal),
    /// A closure whose environment is not its suspended command's support:
    /// a bound value too many or too few, or a command the arena does not
    /// hold.
    Capture(HeapValueId),
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
            Self::Unreadable(id) => write!(f, "value {id} has no core reading"),
            Self::Dangling(id) => write!(f, "value {id} is not readable from the store"),
            Self::Decode(refusal) => {
                write!(f, "a suspended command has no core reading: {refusal}")
            },
            Self::Capture(id) => {
                write!(f, "value {id} binds an environment that is not its support")
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
#[spec(
    captures: [entry = core.watermark()],
    ensures: |ret| match ret {
        | Ok(read) => store.value(value).is_some() && core.value(read).is_some(),
        | Err(_) => core.watermark() == entry,
    },
)]
#[inline]
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
#[spec(
    captures: [entry = core.watermark()],
    ensures: |ret| match ret {
        | Ok(read) => store.value(value).is_some_and(|held| match held {
            | &HeapValue::Closure { .. } => matches!(core.computation(read), Some(&gandr_core_term::Computation::Lambda(_))),
            | _ => matches!(core.computation(read), Some(&gandr_core_term::Computation::Return(_))),
        }),
        | Err(_) => core.watermark() == entry,
    },
)]
#[inline]
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
/// - witness: `tests::run::a_suspended_capture_has_no_reading`
/// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
#[spec(ensures: |ret| match ret {
    | Ok(read) => store.value(value).is_some_and(|held| match held {
        | &HeapValue::Closure { .. } => matches!(core.computation(read), Some(&gandr_core_term::Computation::Lambda(_) | &gandr_core_term::Computation::With(..))),
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
        let values = reading.closing(environment)?;
        let selected = captured(arena, value, Suspension::Producer(producer))?;
        let closing = Closing::new(&selected, &values).ok_or(ReadbackRefusal::Capture(value))?;
        return match decode(arena, Root::Copattern(producer), core, closing)? {
            Decoded::Computation(function) => Ok(function),
            Decoded::Value(_) => Err(UnfocusRefusal::DecodeInvariant.into()),
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
    #[spec(ensures: |ref ret| match ret.as_ref() {
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
    ///   dependencies. L2 — suspended bodies, datatype constructors and
    ///   recursive thunks compare with normal forms.
    /// - witness: `readback::tests::shared_fields_preserve_their_order`
    /// - witness: `readback::tests::forward_dependencies_are_refused_before_reading_the_parent`
    /// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
    /// - witness: `tests::differential::thunks_compare_structurally_through_readback`
    /// - witness: `tests::differential::hand_built_declared_data_cases_agree`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "invariant: the table holds only values this readback recorded, each checked by `reading` as it was inserted; the check re-reads the table once per call, one call per root set and one per suspended environment the readback closes"
        )
    )]
    #[spec(
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
                HeapValue::Stack { ref frames } => {
                    for frame in frames {
                        match *frame {
                            StackFrame::Apply(value) => pending.push(value),
                            StackFrame::Project(_) => {},
                            StackFrame::Bind(closed) => {
                                pending.extend(store.bound_values(closed.environment));
                            },
                        }
                    }
                },
                HeapValue::Literal(_) | HeapValue::Opaque(_) | HeapValue::Code(_) => {},
                HeapValue::Constructed { ref fields, .. } => {
                    pending.extend(fields.iter().copied());
                },
                HeapValue::Thunk { environment, .. } | HeapValue::Fixpoint { environment, .. } => {
                    pending.extend(store.bound_values(environment));
                },
                HeapValue::Closure { .. } | HeapValue::Capability => {
                    return Err(ReadbackRefusal::Unreadable(id));
                },
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
    /// - requires: recorded heap addresses and core readings still resolve,
    ///   which [`Self::read`] checks around the loop that calls this once per
    ///   value, so the requirement is not re-checked per value here.
    /// - ensures: the core value `id` denotes.
    /// - provides: one row of the readback table.
    /// - fails: as [`Self::read`], including a dependency not yet recorded.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact literal, opaque, tuple, record, injection and
    ///   lift nodes distinguish changed payloads, head tags, labels and field
    ///   order; invalid arity and a dependency read too early have exact
    ///   refusals. L2 — thunk, recursive-thunk and datatype-constructor
    ///   readings compare with the independent normaliser.
    /// - witness: `readback::tests::shared_fields_preserve_their_order`
    /// - witness: `readback::tests::refusals_restore_an_existing_core_prefix`
    /// - witness: `readback::tests::forward_dependencies_are_refused_before_reading_the_parent`
    /// - witness: `tests::differential::thunks_compare_structurally_through_readback`
    /// - witness: `tests::differential::hand_built_declared_data_cases_agree`
    /// - witness: `tests::run::a_recursive_thunk_computes_through_its_own_binding`
    /// - witness: `tests::run::a_selection_reads_the_width_of_the_value_it_meets`
    /// - witness: `readback::tests::a_record_reads_back_only_from_one_field_per_ascending_label`
    /// - witness: `readback::tests::a_recorded_run_reads_back_only_from_one_field_per_payload`
    #[spec(
        ensures: |ret| match ret {
            | Err(error) => self.store.value(id).is_some() || error == ReadbackRefusal::Dangling(id),
            | Ok(read) => self.store.value(id).zip(self.core.value(read)).is_some_and(|(held, node)| match *held {
                | HeapValue::Stack { ref frames } => matches!(node, gandr_core_term::Value::Reify(source) if source.len() == frames.len()),
                | HeapValue::Literal(ref literal) => matches!(*node, gandr_core_term::Value::Literal(ref found) if found == literal),
                | HeapValue::Opaque(constant) => *node == gandr_core_term::Value::Constant(constant),
                | HeapValue::Code(_) => matches!(*node, gandr_core_term::Value::Quote(_) | gandr_core_term::Value::QuoteComputation(_)),
                | HeapValue::Constructed { ref tag, ref fields } => match (tag, fields.as_ref()) {
                    | (&ConstructorTag::ListNil, &[]) => *node == gandr_core_term::Value::ListNil,
                    | (&ConstructorTag::ListCons, &[head, tail]) => matches!(*node, gandr_core_term::Value::ListCons(h, t) if self.read.get(&head) == Some(&h) && self.read.get(&tail) == Some(&t)),
                    | (&ConstructorTag::Tuple(arity), fields) => fields.len() == usize::from(arity)
                        && node.components().is_some_and(|values| fields.iter().map(|field| self.read.get(field)).eq(values.iter().map(Some))),
                    | (&ConstructorTag::Record(ref labels), fields) => fields.len() == labels.len()
                        && matches!(*node, gandr_core_term::Value::Record(ref read) if read.keys().eq(labels.iter())
                            && fields.iter().map(|field| self.read.get(field)).eq(read.values().map(Some))),
                    | (&ConstructorTag::Injection(summand), &[body]) => matches!(*node, gandr_core_term::Value::Injection(found, value)
                        if summand == found && self.read.get(&body) == Some(&value)),
                    | (&ConstructorTag::Lift(ref level), &[body]) => matches!(*node, gandr_core_term::Value::Lift { ref target, body: value }
                        if target == level && self.read.get(&body) == Some(&value)),
                    | (&ConstructorTag::Data { tag, arity, .. }, fields) => fields.len() == usize::from(arity)
                        && matches!(*node, gandr_core_term::Value::Constructor { tag: found, fields: ref values, .. }
                            if found == tag && fields.iter().map(|field| self.read.get(field)).eq(values.iter().map(Some))),
                    | (&ConstructorTag::Recorded(ref shape), fields) => matches!(*node, gandr_core_term::Value::Recorded(ref read)
                        if read.iter().map(|movement| movement.carrying(())).eq(shape.iter().cloned())
                            && fields.iter().map(|field| self.read.get(field).copied()).eq(read.iter().filter_map(|movement| match *movement {
                                | gandr_core_term::session::RecordedMove::Sent(payload)
                                | gandr_core_term::session::RecordedMove::Received(payload) => Some(Some(payload)),
                                | _ => None,
                            }))),
                    | _ => false,
                },
                | HeapValue::Thunk { .. } => matches!(*node, gandr_core_term::Value::Thunk(_)),
                | HeapValue::Fixpoint { evidence, .. } => matches!(*node, gandr_core_term::Value::Thunk(body)
                    if matches!(self.core.computation(body), Some(&gandr_core_term::Computation::Fixpoint { evidence: claimed, .. }) if claimed == evidence)),
                | HeapValue::Closure { .. } | HeapValue::Capability => false,
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
            HeapValue::Stack { ref frames } => {
                let mut source = Vec::with_capacity(frames.len());
                for frame in frames {
                    source.push(match *frame {
                        StackFrame::Apply(value) => StackFrame::Apply(self.lookup(value)?),
                        StackFrame::Project(side) => StackFrame::Project(side),
                        StackFrame::Bind(closed) => {
                            let values = store
                                .bound_values(closed.environment)
                                .map(|bound| self.lookup(bound))
                                .collect::<Result<Vec<_>, _>>()?;
                            let selected = captured(self.arena, id, Suspension::Bind(closed.body))?;
                            let closing = Closing::new(&selected, &values)
                                .ok_or(ReadbackRefusal::Capture(id))?;
                            let Decoded::Computation(body) = decode(
                                self.arena,
                                Root::BindBody(closed.body),
                                self.core,
                                closing,
                            )?
                            else {
                                return Err(UnfocusRefusal::DecodeInvariant.into());
                            };
                            StackFrame::Bind(body)
                        },
                    });
                }
                Ok(self.core.value_reify(source.into()))
            },
            HeapValue::Literal(ref literal) => Ok(self.core.value_literal(literal.clone())),
            HeapValue::Opaque(constant) => Ok(self.core.value_constant(constant)),
            HeapValue::Code(code) => {
                let arena = self.arena;
                gandr_core_term::TypeImporter::new(arena.annotations(), self.core)
                    .value(code)
                    .map_err(|gandr_core_term::ImportFault| ReadbackRefusal::Unreadable(id))
            },
            HeapValue::Constructed {
                ref tag,
                ref fields,
            } => match (tag, fields.as_ref()) {
                (&ConstructorTag::ListNil, &[]) => Ok(self.core.value_list_nil()),
                (&ConstructorTag::ListCons, &[head, tail]) => {
                    let head = self.lookup(head)?;
                    let tail = self.lookup(tail)?;
                    Ok(self.core.value_list_cons(head, tail))
                },
                (&ConstructorTag::Tuple(arity), components)
                    if components.len() == usize::from(arity) =>
                {
                    let components = components
                        .iter()
                        .map(|&component| self.lookup(component))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(self.core.value_tuple(&components))
                },
                (&ConstructorTag::Record(ref labels), fields)
                    if fields.len() == labels.len()
                        && labels
                            .iter()
                            .zip(labels.iter().skip(1))
                            .all(|(before, after)| before < after) =>
                {
                    let record = labels
                        .iter()
                        .zip(fields)
                        .map(|(label, &field)| self.lookup(field).map(|read| (label.clone(), read)))
                        .collect::<Result<alloc::collections::BTreeMap<_, _>, _>>()?;
                    Ok(self.core.value_record(record))
                },
                (&ConstructorTag::Injection(summand), &[body]) => {
                    let body = self.lookup(body)?;
                    Ok(self.core.value_injection(summand, body))
                },
                (&ConstructorTag::Lift(ref level), &[body]) => {
                    let body = self.lookup(body)?;
                    Ok(self.core.value_lift(level.clone(), body))
                },
                (&ConstructorTag::Data { tag, arity, family }, fields)
                    if fields.len() == usize::from(arity) =>
                {
                    let fields = fields
                        .iter()
                        .map(|&field| self.lookup(field))
                        .collect::<Result<Vec<_>, _>>()?;
                    let datatype = match family {
                        Some(declaration) => self.core.value_type_data(declaration, Vec::new()),
                        None => self.core.value_type_unknown(),
                    };
                    Ok(self.core.value_constructor(datatype, tag, fields))
                },
                (&ConstructorTag::Recorded(ref shape), fields)
                    if fields.len() == usize::from(tag.producer_arity()) =>
                {
                    use gandr_core_term::session::RecordedMove;
                    let mut payloads = fields.iter();
                    let mut read = Vec::with_capacity(shape.len());
                    for movement in shape.iter() {
                        read.push(match *movement {
                            RecordedMove::Sent(()) | RecordedMove::Received(()) => {
                                let &payload =
                                    payloads.next().ok_or(ReadbackRefusal::Unreadable(id))?;
                                movement.carrying(self.lookup(payload)?)
                            },
                            RecordedMove::Selected(ref label) => {
                                RecordedMove::Selected(label.clone())
                            },
                            RecordedMove::Offered(ref label) => {
                                RecordedMove::Offered(label.clone())
                            },
                            RecordedMove::Closed => RecordedMove::Closed,
                        });
                    }
                    Ok(self.core.value_recorded(alloc::sync::Arc::from(read)))
                },
                _ => Err(ReadbackRefusal::Unreadable(id)),
            },
            HeapValue::Thunk {
                body, environment, ..
            } => {
                let values = store
                    .bound_values(environment)
                    .map(|bound| self.lookup(bound))
                    .collect::<Result<Vec<_>, _>>()?;
                let selected = captured(self.arena, id, Suspension::Thunk(body))?;
                let closing =
                    Closing::new(&selected, &values).ok_or(ReadbackRefusal::Capture(id))?;
                match decode(self.arena, Root::ThunkBody(body), self.core, closing)? {
                    Decoded::Value(thunk) => Ok(thunk),
                    Decoded::Computation(_) => Err(UnfocusRefusal::DecodeInvariant.into()),
                }
            },
            HeapValue::Fixpoint {
                body,
                environment,
                evidence,
                ..
            } => {
                let values = store
                    .bound_values(environment)
                    .map(|bound| self.lookup(bound))
                    .collect::<Result<Vec<_>, _>>()?;
                let selected = captured(self.arena, id, Suspension::Fixpoint(body))?;
                let closing =
                    Closing::new(&selected, &values).ok_or(ReadbackRefusal::Capture(id))?;
                match decode(
                    self.arena,
                    Root::FixpointBody(body, evidence),
                    self.core,
                    closing,
                )? {
                    Decoded::Value(thunk) => Ok(thunk),
                    Decoded::Computation(_) => Err(UnfocusRefusal::DecodeInvariant.into()),
                }
            },
            HeapValue::Closure { .. } | HeapValue::Capability => {
                Err(ReadbackRefusal::Unreadable(id))
            },
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
    #[spec(ensures: |ret| ret == self.read.get(&id).copied().ok_or(ReadbackRefusal::Dangling(id)))]
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

/// The indices the suspension a value holds captured, innermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the indices [`CommandArena::captures`] names for `suspension`.
/// - provides: the half of a closing the IL states; the store's environment is
///   the other.
/// - fails: [`ReadbackRefusal::Capture`] naming `value` when the arena does not
///   hold the suspension's node.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a thunk over a body the arena does not hold is refused by
///   the value's name; L2 — every generated closure reads back.
/// - witness: `readback::tests::an_environment_that_is_not_the_support_is_refused`
/// - witness: `tests::run::a_captured_environment_holds_exactly_its_support`
#[spec(ensures: |ret| ret.is_ok() == arena.captures(suspension).is_some())]
fn captured(
    arena: &CommandArena,
    value: HeapValueId,
    suspension: Suspension,
) -> Result<Vec<DeBruijnIndex>, ReadbackRefusal>
{
    Ok(arena
        .captures(suspension)
        .ok_or(ReadbackRefusal::Capture(value))?
        .collect())
}

#[cfg(test)]
mod tests;
