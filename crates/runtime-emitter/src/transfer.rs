//! A run's value moved into a [`Store`], so readback reads it: the answer a
//! run halts with, a value it stopped stuck at, a payload offered to the
//! host.
//!
//! A value is a graph of heap objects and constants, acyclic because every
//! object is allocated after the objects it holds. It is walked once,
//! children before parents, each object allocated once however many objects
//! hold it — across every value one run moves — so sharing survives the move:
//!
//! | object | store value |
//! | --- | --- |
//! | an integer | a literal |
//! | a literal object | the literal its run's literal table holds |
//! | a tuple, an injection, a datatype's constructor | a constructed value of the same head, the family named |
//! | a head object | a constructed value of the head its function's head table holds |
//! | an opaque object | the opaque constant its family names |
//! | a closure of a thunk | a thunk over the site's body |
//! | a closure of a fixpoint | a fixpoint over the site's body and its evidence |
//! | a closure of a copattern object | a closure over the site's producer |
//! | a reified stack | a literal stack, innermost frame first |
//!
//! A closure's environment binds the captures its site names — the visible
//! producer binders where it was created — outermost first, so de Bruijn
//! index zero is the innermost, as readback's environments bind. A
//! covariable or a slot the lowering held a temporary in is not bound:
//! readback closes a suspended command over producer bindings alone. A
//! stack's frames move by their code words: an application stub's argument,
//! a projection stub's side, and a reified bind frame's command closed over
//! the captures its window copy holds, as a closure's are. A captured stack
//! holds the run's own frames — a delimiter, a handler, a pending match —
//! which no store value spells, and is refused as a host object.

use alloc::collections::BTreeMap;

use gandr_core_sequent::ClosedCommand;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Environment;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Store;
use gandr_core_sequent::StoreFault;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Word;

use crate::function::Stub;
use crate::host::Codes;
use crate::host::STACK_PREFIX;
use crate::host::integer_literal;
use crate::lower::Bound;
use crate::lower::Lowered;
use crate::lower::Site;
use crate::lower::Slot;

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
    /// A cell, or a stack holding a frame no store value spells, reached the
    /// answer: only the host reads it.
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

/// What a frame of a stack resumes as, by its code word.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Resumed<'lowered>
{
    /// The application stub: the frame's word is the argument.
    Apply,
    /// A projection stub, taking this side.
    Project(Side),
    /// A reified bind frame: the frame's word is its window copy.
    Bind(&'lowered Bound),
}

/// The closure sites and the literal frames of one function, by the code
/// word a closure or a frame of each carries.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub struct Sites<'lowered>
{
    /// Each closure site, by its entry's code word.
    by_code: BTreeMap<Word, &'lowered Site>,
    /// What each literal frame resumes as, by its code word.
    frames: BTreeMap<Word, Resumed<'lowered>>,
}

impl<'lowered> Sites<'lowered>
{
    /// Index `lowered`'s closure sites and reified bind frames, and the
    /// application and projection stubs, by their code words in `codes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn new(
        lowered: &'lowered Lowered,
        codes: Codes<'_>,
    ) -> Self
    {
        let mut frames: BTreeMap<Word, Resumed<'lowered>> = lowered
            .bounds
            .iter()
            .map(|bound| (codes.label(bound.label), Resumed::Bind(bound)))
            .collect();
        frames.insert(codes.stub(Stub::Apply), Resumed::Apply);
        frames.insert(codes.stub(Stub::ProjectLeft), Resumed::Project(Side::Left));
        frames.insert(
            codes.stub(Stub::ProjectRight),
            Resumed::Project(Side::Right),
        );
        Self {
            by_code: lowered
                .sites
                .iter()
                .map(|site| (codes.label(site.label), site))
                .collect(),
            frames,
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
///   by field, and compared with the answer it states; a wrong offset reads a
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

/// The objects of one run already moved into its store, by the word each
/// lives at.
///
/// # Specification
/// trivial.
pub type Moved = BTreeMap<Word, HeapValueId>;

/// Move the value `value` of a run into `store`, sharing every object `moved`
/// already holds.
///
/// # Specification
/// - requires: `value` is a value of a run still live, over a heap and
///   constants still live, of a function whose closure sites `sites` indexes,
///   whose heads and run's literals `tables` holds and whose IL is `arena`;
///   `moved` holds only objects of that run, moved into `store`.
/// - ensures: the store holds one value per object reachable from `value`, each
///   object's value allocated after its children's and none allocated twice;
///   `moved` gains each; the value's id is returned.
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
///   a pair holding one among them, is moved and compared value by value on
///   both tiers and with the answer each states, environments included; a wrong
///   head, field order or capture differs.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub unsafe fn transfer(
    value: Word,
    sites: &Sites<'_>,
    tables: Tables<'_>,
    arena: &CommandArena,
    store: &mut Store,
    moved: &mut Moved,
) -> Result<HeapValueId, TransferRefusal>
{
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
                let id = allocate(object, sites, tables, arena, store, moved)?;
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
/// [`TransferRefusal::Kind`], [`TransferRefusal::Site`] or
/// [`TransferRefusal::HostObject`] for an object the walk cannot read.
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
        Kind::Cell => Err(TransferRefusal::HostObject(object)),
        Kind::Stack => {
            let mut held = Vec::new();
            for (code, word) in stack_frames(object, Field(arity)) {
                match resumed(sites, code, object)? {
                    Resumed::Apply => held.push(word),
                    Resumed::Project(_) => {},
                    Resumed::Bind(bound) => held.extend(
                        bound
                            .captures
                            .iter()
                            .map(|slot| field(word, slot_field(*slot, Field(0)))),
                    ),
                }
            }
            Ok(held)
        },
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
                .map(|slot| field(object, slot_field(*slot, Field(2))))
                .collect())
        },
    }
}

/// The frames of the stack at `object` holding `count` of them, bottom
/// first: each frame's code word and its word.
///
/// # Specification
/// trivial.
fn stack_frames(
    object: Word,
    count: Field,
) -> impl DoubleEndedIterator<Item = (Word, Word)>
{
    (0 .. count.0).map(move |index| {
        let at = STACK_PREFIX.saturating_add(index.saturating_mul(2));
        (
            field(object, Field(at)),
            field(object, Field(at.saturating_add(1))),
        )
    })
}

/// What the frame whose code word is `code` resumes as.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`TransferRefusal::HostObject`] naming `stack` for a frame no store value
/// spells.
fn resumed<'lowered>(
    sites: &Sites<'lowered>,
    code: Word,
    stack: Word,
) -> Result<Resumed<'lowered>, TransferRefusal>
{
    sites
        .frames
        .get(&code)
        .copied()
        .ok_or(TransferRefusal::HostObject(stack))
}

/// The word offset of `slot` among words that begin `before` words in.
///
/// # Specification
/// trivial.
fn slot_field(
    slot: Slot,
    before: Field,
) -> Field
{
    Field(
        usize::try_from(slot.0)
            .unwrap_or(0)
            .saturating_add(before.0),
    )
}

/// The environment binding the captures `captures` names, read from the
/// words `before` words into `base` and already moved, outermost first, so
/// de Bruijn index zero is the innermost.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`TransferRefusal::Cycle`] for a capture not yet moved;
/// [`TransferRefusal::Store`] for a binding the store refuses.
fn closed_environment(
    (base, before): (Word, Field),
    captures: &[Slot],
    moved: &Moved,
    store: &mut Store,
) -> Result<Environment, TransferRefusal>
{
    let mut environment = Environment::EMPTY;
    for &slot in captures.iter().rev() {
        let capture = field(base, slot_field(slot, before));
        let id = moved
            .get(&capture)
            .copied()
            .ok_or(TransferRefusal::Cycle(capture))?;
        environment = store.bind_value(environment, id)?;
    }
    Ok(environment)
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
        Kind::Cell => return Err(TransferRefusal::HostObject(object)),
        Kind::Stack => {
            let mut frames = Vec::with_capacity(arity);
            for (code, word) in stack_frames(object, Field(arity)).rev() {
                frames.push(match resumed(sites, code, object)? {
                    Resumed::Apply => StackFrame::Apply(lookup(word)?),
                    Resumed::Project(side) => StackFrame::Project(side),
                    Resumed::Bind(bound) => StackFrame::Bind(ClosedCommand {
                        body: bound.body,
                        environment: closed_environment(
                            (word, Field(0)),
                            &bound.captures,
                            moved,
                            store,
                        )?,
                    }),
                });
            }
            HeapValue::Stack {
                frames: frames.into(),
            }
        },
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
            let environment = closed_environment((object, Field(2)), &site.captures, moved, store)?;
            match arena.producer(site.producer) {
                Some(&ProducerNode::Thunk { body }) => HeapValue::Thunk { body, environment },
                Some(&ProducerNode::Fixpoint { body, evidence }) => HeapValue::Fixpoint {
                    body,
                    environment,
                    evidence,
                },
                Some(&(ProducerNode::Cocase { .. } | ProducerNode::Mu { .. })) => {
                    HeapValue::Closure {
                        producer: site.producer,
                        environment,
                    }
                },
                Some(_) | None => return Err(TransferRefusal::Producer),
            }
        },
    };
    Ok(store.allocate(value)?)
}
