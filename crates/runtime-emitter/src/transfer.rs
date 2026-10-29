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
//! A closure's environment binds the captures its site names — the producer
//! bindings its support selects where it was created, and no other —
//! outermost first, so de Bruijn index zero is the innermost capture, as
//! readback pairs an environment with the closure's support. A binding the
//! body never names, a covariable or a slot the lowering held a temporary in
//! is neither moved nor bound: readback closes a suspended command over the
//! producer bindings it names alone. A stack's frames move by their code
//! words: an application stub's argument, a projection stub's side, and a
//! reified bind frame's command closed over the captures its site names, as a
//! closure's are. A captured stack holds the run's own frames — a delimiter, a
//! handler, a pending match — which no store value spells, and is refused as a
//! host object.

use alloc::collections::BTreeMap;

use gandr_core_sequent::Accumulation;
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
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;
use gandr_runtime_stencils::ACCUMULATED_APPLIED;
use gandr_runtime_stencils::ACCUMULATED_FORCED;
use gandr_runtime_stencils::ACCUMULATOR_FREE;
use gandr_runtime_stencils::Flavour;
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
use crate::lower::flavour;

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

/// The tables a run's objects name by their family: the function's heads and
/// codes and the run's literals.
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
    /// The function's codes, by family, in its IL arena's annotations.
    pub codes: &'run [gandr_core_term::ValueId],
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
    /// The projection stub: the frame's word is the component.
    Project,
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
    /// What each frame owns, by its code word.
    owners: BTreeMap<Word, Owners<'lowered>>,
    /// The slots holding each window frame's linear names, by its code word.
    linears: BTreeMap<Word, &'lowered [Slot]>,
    /// Each fold cell closure's owned capture positions, by its entry's code
    /// word.
    cells: BTreeMap<Word, &'lowered [Slot]>,
    /// The code word of the accumulate entry an open root's function holds:
    /// every accumulator's code.
    accumulate: Option<Word>,
}

/// What a frame of a run's stack owns, by its code word: what a replay
/// copies out with an owner of its own and the stack's release drops.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub enum Owners<'lowered>
{
    /// A window frame: the values in these slots of its window, one owner
    /// per entry.
    Window(&'lowered [Slot]),
    /// A stub frame whose word is a value it owns: an application's
    /// argument, a fold cell's closure.
    Word,
    /// A frame that resumes a block midway, whose owners no node names.
    Unplaced,
}

impl<'lowered> Sites<'lowered>
{
    /// Index `lowered`'s closure sites, fold cell closures and reified bind
    /// frames, the application and projection stubs, and what each frame
    /// owns and holds linearly, by their code words in `codes`.
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
        frames.insert(codes.stub(Stub::Project), Resumed::Project);
        let mut owners = BTreeMap::new();
        let mut linears = BTreeMap::new();
        for window in &lowered.windows {
            let code = codes.label(window.label);
            let owned = window
                .owners
                .as_ref()
                .and_then(|run| lowered.owners.get(run.owned.clone()))
                .map_or(Owners::Unplaced, Owners::Window);
            owners.insert(code, owned);
            if let Some(held) = window
                .owners
                .as_ref()
                .and_then(|run| lowered.linears.get(run.linear.clone()))
                .filter(|held| !held.is_empty())
            {
                linears.insert(code, held);
            }
        }
        owners.insert(codes.stub(Stub::Apply), Owners::Word);
        owners.insert(codes.stub(Stub::Argument), Owners::Word);
        Self {
            by_code: lowered
                .sites
                .iter()
                .map(|site| (codes.label(site.label), site))
                .collect(),
            frames,
            owners,
            linears,
            cells: lowered
                .cells
                .iter()
                .map(|cell| (codes.label(cell.label), cell.captures.as_slice()))
                .collect(),
            accumulate: lowered.accumulate.map(|label| codes.label(label)),
        }
    }

    /// The code word every accumulator holds: the accumulate entry of an open
    /// root's function, none for any other function.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn accumulate(&self) -> Option<Word>
    {
        self.accumulate
    }

    /// What the frame resuming at `code` owns; none for a frame that owns
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a captured stack resumed twice answers as it states:
    ///   a frame whose owners are not found gives its copy none, and the second
    ///   resumption reads a freed value.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    #[inline]
    #[must_use]
    pub fn owners(
        &self,
        code: Word,
    ) -> Option<Owners<'lowered>>
    {
        self.owners.get(&code).copied()
    }

    /// The slots of its window holding the linear names the frame resuming
    /// at `code` will consume, each a cell; none for a frame that holds none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn linears(
        &self,
        code: Word,
    ) -> &'lowered [Slot]
    {
        self.linears.get(&code).copied().unwrap_or_default()
    }

    /// The code word, the site and the header's flavour of the closure the
    /// store's `value` is laid out as: a thunk or a fixpoint at a site
    /// suspending its body, a closure at its producer's site. None when
    /// `value` names no code or the function holds no such site.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a thunk a migration answers, forced at its caller,
    ///   answers what forcing it in place answers on both tiers. A recursive
    ///   writer's captured fixpoint and a writer's captured function answer
    ///   what their sequential schedule answers. A site found for another body
    ///   or producer runs other code.
    /// - witness: `tests::world::a_thunk_a_migration_returns_runs_at_the_caller_3265`
    /// - witness: `tests::cut::a_recursive_writer_capturing_its_own_fixpoint_answers_2954`
    /// - witness: `tests::cut::a_writer_over_a_captured_function_answers_as_its_sequential_schedule`
    #[inline]
    #[must_use]
    pub fn closure(
        &self,
        arena: &CommandArena,
        value: &HeapValue,
    ) -> Option<(Word, &'lowered Site, Flavour)>
    {
        self.by_code.iter().find_map(|(&code, &site)| {
            let node = arena.producer(site.producer)?;
            let found = match *value {
                HeapValue::Thunk { body, .. } => {
                    matches!(*node, ProducerNode::Thunk { body: suspended } if suspended == body)
                },
                HeapValue::Fixpoint { body, .. } => {
                    matches!(*node, ProducerNode::Fixpoint { body: suspended, .. } if suspended == body)
                },
                HeapValue::Closure { producer, .. } => producer == site.producer,
                HeapValue::Stack { .. }
                | HeapValue::Literal(_)
                | HeapValue::Constructed { .. }
                | HeapValue::Opaque(_)
                | HeapValue::Code(_)
                | HeapValue::Capability
                | HeapValue::Free { .. }
                | HeapValue::Accumulated { .. } => false,
            };
            if !found {
                return None;
            }
            Some((code, site, flavour(node)?))
        })
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
        Kind::Integer | Kind::Literal | Kind::Opaque | Kind::Capability | Kind::Code => {
            Ok(Vec::new())
        },
        Kind::Cell => Err(TransferRefusal::HostObject(object)),
        Kind::Stack => {
            let mut held = Vec::new();
            for (code, word) in stack_frames(object, Field(arity)) {
                match resumed(sites, code, object)? {
                    Resumed::Apply => held.push(word),
                    Resumed::Project => {},
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
            if sites.accumulate == Some(code) {
                return Ok((2 .. arity.saturating_add(2))
                    .map(|offset| field(object, Field(offset)))
                    .collect());
            }
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

/// The values `object` owns, which its release drops.
///
/// A constructor owns its fields, as [`children`] reads them, and a closure
/// its producer captures, at the positions its site or, for a fold's cell
/// closure, its cell record names. A stack owns what each of its frames owns,
/// as its sites' owner table reads them: the values in a window frame's owned
/// slots of its window copy, one per entry, and the word of an application's
/// or a fold cell's frame. A cell owns none: no code releases one, so the
/// value a held cell holds keeps its owner until the run ends.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a tuple's release gives up both fields it holds and a
///   cell's nothing; L2 — the named programs that free what they drop answer as
///   they state.
/// - witness: `transfer::tests::a_released_tuple_gives_up_its_fields_and_a_cell_none`
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
pub fn owned(
    object: Word,
    sites: &Sites<'_>,
) -> Vec<Word>
{
    let header = Header::from_word(field(object, Field(0)));
    match header.kind() {
        Ok(Kind::Cell) | Err(_) => Vec::new(),
        Ok(Kind::Closure) => {
            let code = field(object, Field(1));
            if sites.accumulate == Some(code) {
                return (2 .. usize::from(header.arity()).saturating_add(2))
                    .map(|offset| field(object, Field(offset)))
                    .collect();
            }
            let captures = sites
                .by_code
                .get(&code)
                .map(|site| site.captures.as_slice())
                .or_else(|| sites.cells.get(&code).copied())
                .unwrap_or_default();
            captures
                .iter()
                .map(|slot| field(object, slot_field(*slot, Field(2))))
                .collect()
        },
        Ok(Kind::Stack) => {
            let mut held = Vec::new();
            for (code, word) in stack_frames(object, Field(usize::from(header.arity()))) {
                match sites.owners(code) {
                    Some(Owners::Window(slots)) => held.extend(
                        slots
                            .iter()
                            .map(|&slot| field(word, slot_field(slot, Field(0)))),
                    ),
                    Some(Owners::Word) => held.push(word),
                    Some(Owners::Unplaced) | None => {},
                }
            }
            held
        },
        Ok(
            Kind::Integer
            | Kind::Tuple
            | Kind::Injection
            | Kind::Data
            | Kind::Head
            | Kind::Literal
            | Kind::Opaque
            | Kind::Capability
            | Kind::Code,
        ) => children(object, sites).unwrap_or_default(),
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
        Kind::Code => HeapValue::Code(
            tables
                .codes
                .get(entry?)
                .copied()
                .ok_or(TransferRefusal::Entry(object))?,
        ),
        Kind::Capability => HeapValue::Capability,
        Kind::Cell => return Err(TransferRefusal::HostObject(object)),
        Kind::Stack => {
            let mut frames = Vec::with_capacity(arity);
            for (code, word) in stack_frames(object, Field(arity)).rev() {
                frames.push(match resumed(sites, code, object)? {
                    Resumed::Apply => StackFrame::Apply(lookup(word)?),
                    Resumed::Project => StackFrame::Project(Component::from(usize::from(word))),
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
            if sites.accumulate == Some(code) {
                let at = |offset: usize| lookup(field(object, Field(offset)));
                return Ok(store.allocate(match entry? {
                    ACCUMULATED_FORCED => HeapValue::Accumulated {
                        of: at(2)?,
                        by: Accumulation::Forced,
                    },
                    ACCUMULATED_APPLIED => HeapValue::Accumulated {
                        of: at(2)?,
                        by: Accumulation::Applied(at(3)?),
                    },
                    position => {
                        let held = position
                            .checked_sub(ACCUMULATOR_FREE)
                            .ok_or(TransferRefusal::Entry(object))?;
                        HeapValue::Free {
                            zone: if held & 1 == 1 {
                                Zone::Linear
                            }
                            else {
                                Zone::Intuitionistic
                            },
                            index: DeBruijnIndex::from(
                                u32::try_from(held.wrapping_shr(1))
                                    .map_err(|_overflow| TransferRefusal::Entry(object))?,
                            ),
                        }
                    },
                })?);
            }
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

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_runtime_stencils::Arity;
    use gandr_runtime_stencils::Family;
    use gandr_runtime_stencils::Header;
    use gandr_runtime_stencils::Kind;
    use gandr_runtime_stencils::Tag;
    use gandr_runtime_stencils::Word;

    use super::Sites;
    use super::owned;

    /// The block of an object of `kind` holding `fields`: its count word,
    /// its header, then the fields.
    ///
    /// # Specification
    /// trivial.
    fn block(
        kind: Kind,
        fields: &[Word],
    ) -> Vec<Word>
    {
        let header = Header::new(
            kind,
            Tag::try_from(0_usize).expect("tag zero fits"),
            Arity::try_from(fields.len()).expect("the arity fits"),
            Family::UNNAMED,
        );
        let mut words = Vec::from([Word::ZERO, header.word()]);
        words.extend_from_slice(fields);
        words
    }

    /// A tuple's release gives up each field it holds, in order, and a
    /// cell's gives up nothing: a held cell's value keeps its owner.
    #[test]
    fn a_released_tuple_gives_up_its_fields_and_a_cell_none()
    {
        let mut first = block(Kind::Tuple, &[]);
        let mut second = block(Kind::Tuple, &[]);
        let fields = [
            Word::from_pointer(first.as_mut_ptr().wrapping_add(1)),
            Word::from_pointer(second.as_mut_ptr().wrapping_add(1)),
        ];
        let mut pair = block(Kind::Tuple, &fields);
        let mut cell = block(Kind::Cell, &fields[.. 1]);
        let sites = Sites::default();
        assert_eq!(
            Vec::from(fields),
            owned(
                Word::from_pointer(pair.as_mut_ptr().wrapping_add(1)),
                &sites
            ),
            "the pair gives up both fields"
        );
        assert_eq!(
            Vec::<Word>::new(),
            owned(
                Word::from_pointer(cell.as_mut_ptr().wrapping_add(1)),
                &sites
            ),
            "the cell gives up nothing"
        );
    }
}
