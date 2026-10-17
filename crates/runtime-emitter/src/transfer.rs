//! A run's answer moved into the L machine's store, so the machine's
//! readback reads it as it reads the machine's own.
//!
//! The answer is a graph of heap objects and constants, acyclic because
//! every object is allocated after the objects it holds. It is walked once,
//! children before parents, each object allocated once however many objects
//! hold it, so sharing survives the move:
//!
//! | object | store value |
//! | --- | --- |
//! | an integer | a literal |
//! | a literal object | the literal its run's literal table holds |
//! | a tuple, an injection, a datatype's constructor | a constructed value of the same head, the family named |
//! | a head object | a constructed value of the head its function's head table holds |
//! | an opaque object | the opaque constant its family names |
//! | a closure of a thunk | a thunk over the site's body, with a fresh memo cell |
//! | a closure of a fixpoint | a fixpoint over the site's body, its evidence and a fresh memo cell |
//! | a closure of a copattern object | a closure over the site's producer |
//!
//! A closure's environment binds the captures its site names — the visible
//! producer binders where it was created — outermost first, so de Bruijn
//! index zero is the innermost, as the machine's own environments bind. A
//! covariable or a slot the lowering held a temporary in is not bound:
//! readback closes a suspended command over producer bindings alone.

use alloc::collections::BTreeMap;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Environment;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Memo;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Store;
use gandr_core_sequent::StoreFault;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Word;

use crate::host::integer_literal;
use crate::lower::Site;

/// Why an answer could not be moved into the store.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TransferRefusal
{
    /// The store refused an allocation.
    Store(StoreFault),
    /// A header's kind bits name no kind.
    Kind(Word),
    /// A closure's code word is no closure site of the function.
    Site(Word),
    /// A site's producer is not a thunk, a fixpoint or a copattern object.
    Producer,
    /// The graph holds a cycle, which no run builds.
    Cycle(Word),
    /// A head or literal object names no entry of its table.
    Entry(Word),
    /// A stack or a cell, which only the host reads, reached the answer.
    HostObject(Word),
}

/// The tables a run's objects name by their family: the function's heads
/// and the run's literals.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct Tables<'run>
{
    /// The function's heads, by family.
    pub heads: &'run [ConstructorTag],
    /// The run's literals, by family.
    pub literals: &'run [Literal],
}

impl From<StoreFault> for TransferRefusal
{
    /// The store's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: StoreFault) -> Self
    {
        Self::Store(fault)
    }
}

/// The closure sites of one function, by the code word a closure of each
/// carries.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug, Default)]
pub struct Sites<'lowered>
{
    /// Each site, by its entry's code word.
    by_code: BTreeMap<Word, &'lowered Site>,
}

impl<'lowered> Sites<'lowered>
{
    /// Index `sites` by the code word `code` gives each.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn new<C>(
        sites: &'lowered [Site],
        code: C,
    ) -> Self
    where
        C: Fn(&Site) -> Word,
    {
        Self {
            by_code: sites.iter().map(|site| (code(site), site)).collect(),
        }
    }
}

/// One step of the walk.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// Queue the object's children.
    Enter(Word),
    /// Allocate the object, its children allocated.
    Exit(Word),
}

/// Read the word `offset` words into the object at `object`.
///
/// # Specification
/// - requires: as [`transfer`].
/// - executable: none — the read's validity is the run's invariant.
///
/// # Adequacy
/// - hypothesis: L2 — every named program's answer is read through this, field
///   by field, and compared with the machine's; a wrong offset reads a
///   neighbouring word and the answers differ.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
fn field(
    object: Word,
    offset: Field,
) -> Word
{
    let pointer = object
        .to_pointer::<Word>()
        .cast_const()
        .wrapping_add(offset.0);
    // SAFETY: `transfer`'s caller guarantees every object reachable from the
    // answer is live and holds the words its header counts.
    unsafe { pointer.read() }
}

/// A word offset into an object.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Field(usize);

/// Move the answer `value` of a halted run into `store`.
///
/// # Specification
/// - requires: `value` is the value register of a run that halted, over a heap
///   and constants still live, of a function whose closure sites `sites`
///   indexes, whose heads and run's literals `tables` holds and whose IL is
///   `arena`.
/// - ensures: the store holds one value per object reachable from `value`, each
///   object's value allocated after its children's; the answer's id is
///   returned.
/// - executable: none — the requirement is about memory no predicate reads.
///
/// # Errors
/// [`TransferRefusal`] naming what could not be moved.
///
/// # Safety
/// - unsafe invariants: every word reachable from `value` through the headers'
///   field counts addresses live memory a run wrote or a constant the function
///   holds; a transfer reads nothing else.
///
/// # Adequacy
/// - hypothesis: L2 — every named program's answer, a function's, a thunk's and
///   a pair holding one among them, is moved and compared value by value with
///   the machine's, environments included; a wrong head, field order or capture
///   differs.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub unsafe fn transfer(
    value: Word,
    sites: &Sites<'_>,
    tables: Tables<'_>,
    arena: &CommandArena,
    store: &mut Store,
) -> Result<HeapValueId, TransferRefusal>
{
    let mut moved: BTreeMap<Word, HeapValueId> = BTreeMap::new();
    let mut pending = Vec::from([Visit::Enter(value)]);
    while let Some(visit) = pending.pop() {
        match visit {
            Visit::Enter(object) => {
                if moved.contains_key(&object) {
                    continue;
                }
                pending.push(Visit::Exit(object));
                for child in children(object, sites)? {
                    if !moved.contains_key(&child) {
                        pending.push(Visit::Enter(child));
                    }
                }
            },
            Visit::Exit(object) => {
                if moved.contains_key(&object) {
                    continue;
                }
                let id = allocate(object, sites, tables, arena, store, &moved)?;
                moved.insert(object, id);
            },
        }
    }
    moved
        .get(&value)
        .copied()
        .ok_or(TransferRefusal::Cycle(value))
}

/// The objects `object` holds, in field order.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`TransferRefusal::Kind`] or [`TransferRefusal::Site`] for an object the
/// walk cannot read.
fn children(
    object: Word,
    sites: &Sites<'_>,
) -> Result<Vec<Word>, TransferRefusal>
{
    let header = Header::from_word(field(object, Field(0)));
    let arity = usize::from(header.arity());
    match header
        .kind()
        .map_err(|unknown| TransferRefusal::Kind(unknown.0))?
    {
        Kind::Integer | Kind::Literal | Kind::Opaque | Kind::Capability => Ok(Vec::new()),
        Kind::Stack | Kind::Cell => Err(TransferRefusal::HostObject(object)),
        Kind::Tuple | Kind::Injection | Kind::Data | Kind::Head => Ok((1 ..= arity)
            .map(|offset| field(object, Field(offset)))
            .collect()),
        Kind::Closure => {
            let code = field(object, Field(1));
            let site = sites
                .by_code
                .get(&code)
                .ok_or(TransferRefusal::Site(code))?;
            Ok(site
                .captures
                .iter()
                .map(|slot| {
                    field(
                        object,
                        Field(usize::try_from(slot.0).unwrap_or(0).saturating_add(2)),
                    )
                })
                .collect())
        },
    }
}

/// Allocate `object`'s store value, its children already moved.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`transfer`].
fn allocate(
    object: Word,
    sites: &Sites<'_>,
    tables: Tables<'_>,
    arena: &CommandArena,
    store: &mut Store,
    moved: &BTreeMap<Word, HeapValueId>,
) -> Result<HeapValueId, TransferRefusal>
{
    let header = Header::from_word(field(object, Field(0)));
    let arity = usize::from(header.arity());
    let lookup = |child: Word| {
        moved
            .get(&child)
            .copied()
            .ok_or(TransferRefusal::Cycle(child))
    };
    let constructed = |tag: ConstructorTag| -> Result<HeapValue, TransferRefusal> {
        let fields = (1 ..= arity)
            .map(|offset| lookup(field(object, Field(offset))))
            .collect::<Result<Box<[HeapValueId]>, TransferRefusal>>()?;
        Ok(HeapValue::Constructed { tag, fields })
    };
    let entry = usize::try_from(header.family()).map_err(|_unnamed| TransferRefusal::Entry(object));
    let value = match header
        .kind()
        .map_err(|unknown| TransferRefusal::Kind(unknown.0))?
    {
        Kind::Integer => {
            HeapValue::Literal(Literal::Integer(integer_literal(field(object, Field(1)))))
        },
        Kind::Literal => HeapValue::Literal(
            tables
                .literals
                .get(entry?)
                .cloned()
                .ok_or(TransferRefusal::Entry(object))?,
        ),
        Kind::Head => constructed(
            tables
                .heads
                .get(entry?)
                .cloned()
                .ok_or(TransferRefusal::Entry(object))?,
        )?,
        Kind::Opaque => HeapValue::Opaque(ConstantIndex::from(entry?)),
        Kind::Capability => HeapValue::Capability,
        Kind::Stack | Kind::Cell => return Err(TransferRefusal::HostObject(object)),
        Kind::Tuple => constructed(ConstructorTag::Tuple(ProducerArity::from(arity)))?,
        Kind::Injection => constructed(ConstructorTag::Injection(Summand::from(usize::from(
            header.tag(),
        ))))?,
        Kind::Data => constructed(ConstructorTag::Data {
            tag: gandr_kernel_term::ConstructorTag::from(usize::from(header.tag())),
            arity: ProducerArity::from(arity),
            family: usize::try_from(header.family())
                .ok()
                .map(ConstantIndex::from),
        })?,
        Kind::Closure => {
            let code = field(object, Field(1));
            let site = sites
                .by_code
                .get(&code)
                .ok_or(TransferRefusal::Site(code))?;
            let mut environment = Environment::EMPTY;
            for slot in site.captures.iter().rev() {
                let capture = field(
                    object,
                    Field(usize::try_from(slot.0).unwrap_or(0).saturating_add(2)),
                );
                environment = store.bind_value(environment, lookup(capture)?)?;
            }
            match arena.producer(site.producer) {
                Some(&ProducerNode::Thunk { body }) => HeapValue::Thunk {
                    body,
                    environment,
                    cell: store.allocate_cell()?,
                },
                Some(&ProducerNode::Fixpoint { body, evidence }) => HeapValue::Fixpoint {
                    body,
                    environment,
                    memo: Memo::Cell(store.allocate_cell()?),
                    evidence,
                },
                Some(&ProducerNode::Cocase { .. }) => HeapValue::Closure {
                    producer: site.producer,
                    environment,
                },
                Some(_) | None => return Err(TransferRefusal::Producer),
            }
        },
    };
    Ok(store.allocate(value)?)
}

/// The opaque constant `value` addresses, when a stuck or unmatched exit
/// returned an opaque object as the value it observed.
///
/// # Specification
/// - requires: `value` is zero or addresses a live object's header.
/// - ensures: the constant an opaque object's header names; nothing for zero,
///   for an object of another kind, or for a header naming no constant.
/// - executable: none — the requirement is about memory no predicate reads.
///
/// # Safety
/// - unsafe invariants: a nonzero `value` addresses a live object's header
///   word, as every value a stuck or unmatched exit returns does.
///
/// # Adequacy
/// - hypothesis: L3 — forcing, applying and casing on an owed constant name it
///   on each tier as the machine's stuck answer does, and a sum in hand names
///   none.
/// - witness: `tests::agreement::an_observed_opaque_constant_is_named_on_both_executors`
#[inline]
#[must_use]
pub unsafe fn observed(value: Word) -> Option<ConstantIndex>
{
    if value == Word::ZERO {
        return None;
    }
    // SAFETY: the caller's invariant.
    let header = Header::from_word(unsafe { value.to_pointer::<Word>().read() });
    if !matches!(header.kind(), Ok(Kind::Opaque)) {
        return None;
    }
    usize::try_from(header.family())
        .ok()
        .map(ConstantIndex::from)
}
