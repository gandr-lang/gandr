//! Abstract closures and the rewrites over them: closure conversion in
//! little pieces and the closure's β.
//!
//! An abstract closure `{v̄; f}` ([`ProducerNode::Closure`]) is a closure
//! former `f` — a thunk, a recursive thunk or a copattern object — under a
//! delayed substitution `v̄`, its environment. It has `f`'s polarity and
//! answers the frames `f` answers, so a closure stands wherever its former
//! does: converting one changes no type and no context that consumes it. A
//! bare former is the closure over the empty environment.
//!
//! # Closure conversion in little pieces
//!
//! [`convert_step`] adds one free variable to a closure's environment. The
//! greatest context index `k` the code names past its environment becomes a
//! new innermost environment value `xk`, and the code reads that value where
//! it read the context. The step is the derived equality
//! `{σ; f} = {σ, y/y; f}`: η-expand under the environment, then β the inner
//! application over the larger one. A closure is converted when its code
//! names no intuitionistic context variable past its environment.
//! [`convert`] applies the step until then; each step takes the greatest
//! index left, so the normal form is the code strengthened by its support:
//! the environment holds the variables the code selects, outermost first,
//! and the code is closed but for them. [`convert_all`] converts every
//! closure of a term, inner ones first, so an outer conversion renames the
//! environments of the closures inside it. A closure's code and a nominal
//! match's branches run where their parent stands, so the sweep converts
//! inside them and never them.
//!
//! Only intuitionistic variables move. A linear variable a code names stays
//! where it is and the runtime captures it by support as before, so a
//! converted closure is closed over its environment and its linear captures.
//! A capture a negative cut hands its binder by name keeps its support
//! capture too: its body is no closure former.
//!
//! # The closure's β
//!
//! [`beta`] enters a closure cut against a frame its code answers: an
//! application or projection a copattern object has an arm for, or a force
//! of a thunk or a recursive thunk. It substitutes the environment and the
//! frame's arguments together, as bindings over the arm's body: each
//! continuation bound by a `μ`, outermost first, then each environment
//! value, the recursive thunk's own closure and each argument bound by a
//! `μ̃`, in the order the body counts them. The body is reused as written;
//! only the values and continuations bound are renamed, past the binders
//! above them.
//!
//! # Renaming
//!
//! Both rewrites rename a term's free variables: the step moves the captured
//! index to the innermost environment binder and every other index past it,
//! and β shifts what it binds past the binders above it. A renaming rebuilds
//! only the nodes whose carried support it moves and keeps every other node,
//! so a closed subterm is shared and the cost is the part of the term the
//! moved variables reach. Annotations are core types the renaming does not
//! rebuild, so a node whose annotation names a moved variable is refused by
//! name.
//!
//! A refused rewrite truncates the arena to the mark it took on entry.
//!
//! # References
//!
//! - `Sullivan-2023-reflections_closures` — lineage: Zachary J. Sullivan,
//!   "Reflections of Closures", thesis, University of Oregon, 2023, chapter 4 —
//!   the abstract closure `{σ, λx.M}` that keeps its function's type, its β
//!   substituting environment and argument together, and the conversion rule
//!   adding one free variable at a time, whose normal forms are unique up to
//!   the order of the substitution.
//! - `Sullivan-2023-closure_conversion_little_pieces` — lineage: Zachary J.
//!   Sullivan, Paul Downen and Zena M. Ariola, "Closure Conversion in Little
//!   Pieces", PPDP 2023, `doi:10.1145/3610612.3610622` — closure conversion as
//!   provable equalities local to the intermediate language.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: abstract closures
//!   in the sequent IL, conversion as rewrites with unique normal forms (§
//!   kernel-reassessment-design item 4).

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Zone;
use gandr_core_term::session::ChildOrder;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::Polarity;

use crate::check::consumer_polarity;
use crate::check::producer_polarity;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CopatternArm;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::MintRefusal;
use crate::il::NodeAddress;
use crate::il::Opens;
use crate::il::PatternArm;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::Route;
use crate::il::command_children;
use crate::il::command_signature;
use crate::il::consumer_annotations;
use crate::il::consumer_children;
use crate::il::producer_children;

/// Why a closure rewrite was refused.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClosureRefusal
{
    /// A node the arena does not hold.
    Dangling(NodeAddress),
    /// A producer that is neither a closure former nor an abstract closure.
    NotAClosure(ProducerId),
    /// A node whose annotation names a variable the rewrite renames.
    Annotation(NodeAddress),
    /// A renamed index past the largest a variable carries.
    Overflow,
    /// The arena refused a node the rewrite mints.
    Mint(MintRefusal),
}

impl From<MintRefusal> for ClosureRefusal
{
    /// Wraps the arena's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MintRefusal) -> Self
    {
        Self::Mint(refusal)
    }
}

impl fmt::Display for ClosureRefusal
{
    /// Names the node or the bound the rewrite stopped at.
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
            Self::Dangling(node) => write!(f, "{node} is not in the arena"),
            Self::NotAClosure(id) => {
                write!(f, "producer {id} is neither a closure former nor a closure")
            },
            Self::Annotation(node) => {
                write!(f, "{node} carries an annotation naming a renamed variable")
            },
            Self::Overflow => f.write_str("a renamed index passes the index space"),
            Self::Mint(refusal) => write!(f, "the arena refused a node: {refusal}"),
        }
    }
}

impl core::error::Error for ClosureRefusal
{
}

/// Add one free variable to a closure's environment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a closure former or an abstract closure whose code names an
///   intuitionistic context variable past its environment, `Some` of a new
///   closure: the old environment then the greatest such variable `k`, read
///   where the closure stands, and the code renamed to read `k` from that new
///   innermost value; `None` for one whose code names none, the arena then
///   unchanged.
/// - provides: the closure-conversion rule, one variable at a time.
/// - fails: [`ClosureRefusal::NotAClosure`] for any other producer,
///   [`ClosureRefusal::Annotation`] for a code whose annotation names a renamed
///   variable, and a dangling node or a mint the arena refuses; the arena is
///   then at its entry mark.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a function naming two context variables steps to the
///   greater, then the lesser, then stops, each step's code rendered exactly; a
///   closed former and an operation are separated from a closure.
/// - witness: `closure::tests::a_step_captures_the_greatest_context_variable`
/// - witness: `closure::tests::only_closures_convert`
#[spec(
    captures: [entry = arena.watermark()],
    ensures: |ret| match ret {
        | Ok(Some(converted)) => matches!(arena.producer(converted), Some(&ProducerNode::Closure { .. })),
        | Ok(None) | Err(_) => arena.watermark() == entry,
    },
)]
#[inline]
pub fn convert_step(
    arena: &mut CommandArena,
    closure: ProducerId,
) -> Result<Option<ProducerId>, ClosureRefusal>
{
    let entry = arena.watermark();
    let stepped = step(arena, closure);
    if stepped.is_err() {
        arena.truncate_to(entry);
    }
    stepped
}

/// Convert a closure: add free variables to its environment until its code
/// names none past it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the closure [`convert_step`] reaches when it stops: `closure`
///   itself when its code names no context variable, a converted abstract
///   closure otherwise, whose code names no intuitionistic variable past its
///   environment.
/// - provides: closure conversion to its normal form.
/// - fails: as [`convert_step`]; the arena is then at its entry mark.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the two-variable function converts to the closure over
///   both, rendered exactly, and a converted closure converts to itself.
/// - witness: `closure::tests::a_step_captures_the_greatest_context_variable`
/// - witness: `closure::tests::conversion_is_idempotent`
#[spec(
    captures: [entry = arena.watermark()],
    ensures: |ret| match ret {
        | Ok(converted) => converted_at(arena, converted) == Conversion::Converted,
        | Err(_) => arena.watermark() == entry,
    },
)]
#[inline]
pub fn convert(
    arena: &mut CommandArena,
    closure: ProducerId,
) -> Result<ProducerId, ClosureRefusal>
{
    let entry = arena.watermark();
    let mut current = closure;
    loop {
        match step(arena, current) {
            Ok(Some(next)) => current = next,
            Ok(None) => return Ok(current),
            Err(refusal) => {
                arena.truncate_to(entry);
                return Err(refusal);
            },
        }
    }
}

/// Convert every closure of a term, inner ones first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a term of `root`'s family whose every thunk, recursive thunk,
///   copattern object and abstract closure is converted, but a closure's own
///   code and a nominal match's branches, which run where their parent stands
///   and are converted inside only; the rest of the term is rebuilt only where
///   a converted node lies below it, so a term with no closure naming a context
///   variable is answered as itself.
/// - provides: the conversion sweep over a program.
/// - fails: as [`convert_step`]; the arena is then at its entry mark.
/// - panics: none.
/// - executable: none — converted means every closure below the answer, and a
///   predicate would repeat the walk the sweep is.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — every generated program runs converted to the answer it
///   runs to unconverted, node for node, on every tier the host has, and checks
///   with the free variables it had; L3 — a function nested in a thunk converts
///   inner first, the outer conversion renames the inner environment, and a
///   converted command converts to itself.
/// - witness: `closure::tests::a_nested_function_converts_inside_out`
/// - witness: `tests::closures::converted_programs_answer_as_written`
#[inline]
pub fn convert_all(
    arena: &mut CommandArena,
    root: NodeAddress,
) -> Result<NodeAddress, ClosureRefusal>
{
    sweep(arena, root, Sweep::Convert)
}

/// Enter every closure redex of a term once, inner ones first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a term of `root`'s family whose every cut that [`beta`] enters,
///   once its children are swept, is replaced by its bindings; a redex the
///   bindings make is left for another sweep.
/// - provides: the closure's β over a program.
/// - fails: as [`beta`]; the arena is then at its entry mark.
/// - panics: none.
/// - executable: none — a predicate would repeat the walk the sweep is.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — every generated program, converted or not, checks with
///   its redexes entered and runs to the answer it runs to as written, once
///   both readings are normalised, on every tier the host has.
/// - witness: `tests::closures::an_entered_closure_answers_as_the_cut_did`
#[inline]
pub fn enter_all(
    arena: &mut CommandArena,
    root: NodeAddress,
) -> Result<NodeAddress, ClosureRefusal>
{
    sweep(arena, root, Sweep::Enter)
}

/// Run a sweep from `root`, truncating the arena on a refusal.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`convert_all`] and [`enter_all`].
fn sweep(
    arena: &mut CommandArena,
    root: NodeAddress,
    sweep: Sweep,
) -> Result<NodeAddress, ClosureRefusal>
{
    let entry = arena.watermark();
    let swept = Pass::new(arena, sweep).run(root);
    if swept.is_err() {
        arena.truncate_to(entry);
    }
    swept
}

/// Enter a closure cut against a frame its code answers.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a cut of an abstract closure or a closure former against an
///   application or projection frame its copattern object answers, or a force
///   frame against its thunk or recursive thunk, `Some` of the bindings over
///   the answering body: each frame continuation bound by a `μ`, then each
///   environment value, a recursive thunk's own closure and each frame argument
///   bound by a `μ̃`, each renamed past the binders above it; `None` for any
///   other command, the arena then unchanged.
/// - provides: the closure's β, the environment and the arguments substituted
///   together.
/// - fails: [`ClosureRefusal::Annotation`] for a bound value whose annotation
///   names a renamed variable, a dangling node or a mint the arena refuses; the
///   arena is then at its entry mark.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — every redex of a converted generated program runs, once
///   entered, to the answer it ran to; L3 — the converted constant function
///   applied renders its bindings exactly, and a cut of a value against a match
///   is no redex.
/// - witness: `closure::tests::beta_binds_the_environment_and_the_argument_together`
/// - witness: `tests::closures::an_entered_closure_answers_as_the_cut_did`
#[spec(
    captures: [entry = arena.watermark()],
    ensures: |ret| match ret {
        | Ok(Some(entered)) => arena.command(entered).is_some(),
        | Ok(None) | Err(_) => arena.watermark() == entry,
    },
)]
#[inline]
pub fn beta(
    arena: &mut CommandArena,
    cut: CommandId,
) -> Result<Option<CommandId>, ClosureRefusal>
{
    let entry = arena.watermark();
    let entered = enter(arena, cut);
    if entered.is_err() {
        arena.truncate_to(entry);
    }
    entered
}

/// Whether a closure is converted.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Conversion
{
    /// No closure, or one whose code names no intuitionistic variable past
    /// its environment.
    Converted,
    /// A closure whose code names a context variable past its environment.
    Open,
}

/// Whether `closure` is converted.
///
/// # Specification
/// trivial.
fn converted_at(
    arena: &CommandArena,
    closure: ProducerId,
) -> Conversion
{
    let open =
        match framed(arena, closure) {
            Ok(Some((environment, code))) => arena
                .node_scope(NodeAddress::Producer(code))
                .is_none_or(|scope| {
                    scope
                        .producers()
                        .outside(Zone::Intuitionistic, BinderDepth::from(environment.len()))
                        .next()
                        .is_some()
                }),
            Ok(None) | Err(_) => false,
        };
    if open {
        Conversion::Open
    }
    else {
        Conversion::Converted
    }
}

/// A closure's environment and code: a closure former's own, under the empty
/// environment; `None` for any other producer.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Dangling`] for a producer the arena does not hold.
fn framed(
    arena: &CommandArena,
    closure: ProducerId,
) -> Result<Option<(&[ProducerId], ProducerId)>, ClosureRefusal>
{
    let node = arena
        .producer(closure)
        .ok_or(ClosureRefusal::Dangling(NodeAddress::Producer(closure)))?;
    Ok(match *node {
        ProducerNode::Closure {
            ref environment,
            code,
        } => Some((&**environment, code)),
        ProducerNode::Thunk { .. }
        | ProducerNode::Fixpoint { .. }
        | ProducerNode::Cocase { .. } => Some((&[], closure)),
        ProducerNode::Reify(_)
        | ProducerNode::Primitive { .. }
        | ProducerNode::Decompose(_)
        | ProducerNode::Variable { .. }
        | ProducerNode::Constant(_)
        | ProducerNode::Literal(_)
        | ProducerNode::Code(_)
        | ProducerNode::Constructor { .. }
        | ProducerNode::Mu { .. } => None,
    })
}

/// One conversion step, leaving a refusal's partial nodes for the caller to
/// truncate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`convert_step`].
fn step(
    arena: &mut CommandArena,
    closure: ProducerId,
) -> Result<Option<ProducerId>, ClosureRefusal>
{
    let (environment, code) =
        framed(arena, closure)?.ok_or(ClosureRefusal::NotAClosure(closure))?;
    let mut environment = environment.to_vec();
    let bound = environment.len();
    let Some(free) = arena
        .node_scope(NodeAddress::Producer(code))
        .ok_or(ClosureRefusal::Dangling(NodeAddress::Producer(code)))?
        .producers()
        .outside(Zone::Intuitionistic, BinderDepth::from(bound))
        .next_back()
    else {
        return Ok(None);
    };
    let free = usize::try_from(u32::from(free)).map_err(|_overflow| ClosureRefusal::Overflow)?;
    let captured = free.checked_sub(bound).ok_or(ClosureRefusal::Overflow)?;
    let renamed = rename(arena, NodeAddress::Producer(code), Renaming::Capture {
        bound,
        captured,
    })?;
    let NodeAddress::Producer(code) = renamed
    else {
        return Err(ClosureRefusal::Dangling(renamed));
    };
    let value = arena.mint_producer(ProducerNode::Variable {
        zone: Zone::Intuitionistic,
        index: counted(BinderDepth::from(captured))?,
    })?;
    environment.push(value);
    let closure = arena.mint_producer(ProducerNode::Closure {
        environment: environment.into_boxed_slice(),
        code,
    })?;
    Ok(Some(closure))
}

/// The index a count of binders names.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Overflow`] past the `u32` index space.
fn counted(count: BinderDepth) -> Result<DeBruijnIndex, ClosureRefusal>
{
    u32::try_from(usize::from(count))
        .map(DeBruijnIndex::from)
        .map_err(|_overflow| ClosureRefusal::Overflow)
}

/// How a renaming moves a term's free variables, each counted from the term
/// it renames.
#[derive(Clone, Copy, Debug)]
enum Renaming
{
    /// Every producer variable past `producers` binders and every covariable
    /// past `covariables`.
    Shift
    {
        /// The producer binders added above the term.
        producers: usize,
        /// The covariable binders added above the term.
        covariables: usize,
    },
    /// The context variable `captured` past `bound` environment binders moves
    /// to a new innermost binder, and every other producer variable past it.
    Capture
    {
        /// The environment binders the code stands under.
        bound: usize,
        /// The captured context variable, counted past them.
        captured: usize,
    },
}

/// A binder count in each index space a renaming moves.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Depth
{
    /// Intuitionistic producer binders.
    producers: usize,
    /// Covariable binders.
    covariables: usize,
}

impl Depth
{
    /// This depth under the binders `opens` counts.
    ///
    /// # Specification
    /// trivial.
    fn under(
        self,
        opens: Opens,
    ) -> Self
    {
        Self {
            producers: self
                .producers
                .saturating_add(usize::from(opens.producers.depth(Zone::Intuitionistic))),
            covariables: self
                .covariables
                .saturating_add(usize::from(opens.covariables.depth(Zone::Intuitionistic))),
        }
    }
}

/// Which index space an index counts in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Space
{
    /// Intuitionistic producer variables.
    Producers,
    /// Covariables.
    Covariables,
}

impl Renaming
{
    /// The index `index` reads after the renaming, standing under `depth`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`ClosureRefusal::Overflow`] past the `u32` index space.
    fn moved(
        self,
        space: Space,
        index: DeBruijnIndex,
        depth: Depth,
    ) -> Result<DeBruijnIndex, ClosureRefusal>
    {
        let at = usize::try_from(u32::from(index)).map_err(|_overflow| ClosureRefusal::Overflow)?;
        let below = match space {
            Space::Producers => depth.producers,
            Space::Covariables => depth.covariables,
        };
        let Some(free) = at.checked_sub(below)
        else {
            return Ok(index);
        };
        let free = match (self, space) {
            (Self::Shift { producers: by, .. }, Space::Producers)
            | (
                Self::Shift {
                    covariables: by, ..
                },
                Space::Covariables,
            ) => free.checked_add(by),
            (Self::Capture { bound, captured }, Space::Producers) => {
                if Some(free) == bound.checked_add(captured) {
                    Some(0)
                }
                else {
                    free.checked_add(1)
                }
            },
            (Self::Capture { .. }, Space::Covariables) => Some(free),
        };
        counted(BinderDepth::from(
            free.and_then(|moved| moved.checked_add(below))
                .ok_or(ClosureRefusal::Overflow)?,
        ))
    }

    /// Whether the renaming moves an index `node`'s carried support selects,
    /// the node standing under `depth`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`ClosureRefusal::Dangling`] for a node the arena does not hold;
    /// [`ClosureRefusal::Overflow`] as [`Self::moved`].
    fn moves(
        self,
        arena: &CommandArena,
        node: NodeAddress,
        depth: Depth,
    ) -> Result<Change, ClosureRefusal>
    {
        let scope = arena
            .node_scope(node)
            .ok_or(ClosureRefusal::Dangling(node))?;
        for (space, support) in [
            (Space::Producers, scope.producers()),
            (Space::Covariables, scope.covariables()),
        ] {
            for index in support.indices(Zone::Intuitionistic) {
                if self.moved(space, index, depth)? != index {
                    return Ok(Change::Moves);
                }
            }
        }
        Ok(Change::Keeps)
    }
}

/// Whether a renaming moves a node's free variables.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Change
{
    /// The node names a variable the renaming moves.
    Moves,
    /// The node names none.
    Keeps,
}

/// Rename the free variables of the term at `root`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`convert_step`]: an annotation naming a moved variable, a dangling
/// node, an overflow or a refused mint.
fn rename(
    arena: &mut CommandArena,
    root: NodeAddress,
    renaming: Renaming,
) -> Result<NodeAddress, ClosureRefusal>
{
    let mut done: BTreeMap<(NodeAddress, Depth), NodeAddress> = BTreeMap::new();
    let mut stack = Vec::from([Visit::Enter(root, Depth::default())]);
    while let Some(visit) = stack.pop() {
        match visit {
            Visit::Enter(node, depth) => {
                if done.contains_key(&(node, depth)) {
                    continue;
                }
                if renaming.moves(arena, node, depth)? == Change::Keeps {
                    done.insert((node, depth), node);
                    continue;
                }
                stack.push(Visit::Exit(node, depth));
                let work = stack.len();
                children(arena, node, |child, opens| {
                    stack.push(Visit::Enter(child, depth.under(opens)));
                    Ok(())
                })?;
                if let Some(pushed) = stack.get_mut(work ..) {
                    pushed.reverse();
                }
            },
            Visit::Exit(node, depth) => {
                let mut fresh = Vec::new();
                children(arena, node, |child, opens| {
                    let renamed = done
                        .get(&(child, depth.under(opens)))
                        .ok_or(ClosureRefusal::Dangling(child))?;
                    fresh.push(*renamed);
                    Ok(())
                })?;
                let renamed = rebuild(arena, node, fresh, |space, index| {
                    renaming.moved(space, index, depth)
                })?;
                if renamed != node {
                    annotated(arena, node, renaming, depth)?;
                }
                done.insert((node, depth), renamed);
            },
        }
    }
    done.get(&(root, Depth::default()))
        .copied()
        .ok_or(ClosureRefusal::Dangling(root))
}

/// Refuse `node` when an annotation it carries names a variable `renaming`
/// moves, the node standing under `depth`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Annotation`] naming `node`; a dangling node or
/// annotation.
fn annotated(
    arena: &CommandArena,
    node: NodeAddress,
    renaming: Renaming,
    depth: Depth,
) -> Result<(), ClosureRefusal>
{
    let types = arena.annotations();
    let dangling = ClosureRefusal::Dangling(node);
    let mut check = |annotation| -> Result<(), ClosureRefusal> {
        let support = types.value_type_support(annotation).ok_or(dangling)?;
        for index in support.indices(Zone::Intuitionistic) {
            if renaming.moved(Space::Producers, index, depth)? != index {
                return Err(ClosureRefusal::Annotation(node));
            }
        }
        Ok(())
    };
    match node {
        NodeAddress::Producer(_) => Ok(()),
        NodeAddress::Consumer(id) => {
            consumer_annotations(arena.consumer(id).ok_or(dangling)?).try_for_each(&mut check)
        },
        NodeAddress::Command(id) => command_signature(arena.command(id).ok_or(dangling)?)
            .map_or(Ok(()), |signature| {
                signature.types().try_for_each(&mut check)
            }),
    }
}

/// One step of a post-order walk.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// Schedule the node's children.
    Enter(NodeAddress, Depth),
    /// Rebuild the node over its children's images.
    Exit(NodeAddress, Depth),
}

/// Visit `node`'s children in edge order, each beside the binders `node`
/// opens over it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Dangling`] for a node the arena does not hold; the
/// first refusal `each` answers.
fn children<Each>(
    arena: &CommandArena,
    node: NodeAddress,
    each: Each,
) -> Result<(), ClosureRefusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), ClosureRefusal>,
{
    let dangling = ClosureRefusal::Dangling(node);
    match node {
        NodeAddress::Producer(id) => producer_children(arena.producer(id).ok_or(dangling)?, each),
        NodeAddress::Consumer(id) => consumer_children(arena.consumer(id).ok_or(dangling)?, each),
        NodeAddress::Command(id) => command_children(arena.command(id).ok_or(dangling)?, each),
    }
}

/// The images of a node's children, taken in edge order.
struct Fresh
{
    /// The images, the next one first.
    images: alloc::vec::IntoIter<NodeAddress>,
    /// The node rebuilt, named by a refusal.
    node: NodeAddress,
}

impl Fresh
{
    /// The next image, a producer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`ClosureRefusal::Dangling`] naming the node when the images run out
    /// or the next is of another family.
    fn producer(&mut self) -> Result<ProducerId, ClosureRefusal>
    {
        match self.images.next() {
            Some(NodeAddress::Producer(id)) => Ok(id),
            Some(NodeAddress::Consumer(_) | NodeAddress::Command(_)) | None => {
                Err(ClosureRefusal::Dangling(self.node))
            },
        }
    }

    /// The next image, a consumer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::producer`].
    fn consumer(&mut self) -> Result<ConsumerId, ClosureRefusal>
    {
        match self.images.next() {
            Some(NodeAddress::Consumer(id)) => Ok(id),
            Some(NodeAddress::Producer(_) | NodeAddress::Command(_)) | None => {
                Err(ClosureRefusal::Dangling(self.node))
            },
        }
    }

    /// The next image, a command.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::producer`].
    fn command(&mut self) -> Result<CommandId, ClosureRefusal>
    {
        match self.images.next() {
            Some(NodeAddress::Command(id)) => Ok(id),
            Some(NodeAddress::Producer(_) | NodeAddress::Consumer(_)) | None => {
                Err(ClosureRefusal::Dangling(self.node))
            },
        }
    }

    /// One image per old child in `old`, producers.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::producer`].
    fn producers(
        &mut self,
        old: &[ProducerId],
    ) -> Result<alloc::boxed::Box<[ProducerId]>, ClosureRefusal>
    {
        old.iter().map(|_| self.producer()).collect()
    }

    /// One image per old child in `old`, consumers.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::producer`].
    fn consumers(
        &mut self,
        old: &[ConsumerId],
    ) -> Result<alloc::boxed::Box<[ConsumerId]>, ClosureRefusal>
    {
        old.iter().map(|_| self.consumer()).collect()
    }
}

/// `node` rebuilt over `images`, its children's images in edge order, with
/// each variable and covariable it names moved by `moved`; `node` itself
/// when nothing changes.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A dangling node, an image list that does not match the node's children, a
/// refusal of `moved`, or a refused mint.
fn rebuild<Moved>(
    arena: &mut CommandArena,
    node: NodeAddress,
    images: Vec<NodeAddress>,
    moved: Moved,
) -> Result<NodeAddress, ClosureRefusal>
where
    Moved: Fn(Space, DeBruijnIndex) -> Result<DeBruijnIndex, ClosureRefusal>,
{
    let dangling = ClosureRefusal::Dangling(node);
    let mut fresh = Fresh {
        images: images.into_iter(),
        node,
    };
    Ok(match node {
        NodeAddress::Producer(id) => {
            let old = arena.producer(id).ok_or(dangling)?;
            let new = rebuild_producer(old, &mut fresh, &moved)?;
            if new == *old {
                node
            }
            else {
                NodeAddress::Producer(arena.mint_producer(new)?)
            }
        },
        NodeAddress::Consumer(id) => {
            let old = arena.consumer(id).ok_or(dangling)?;
            let new = rebuild_consumer(old, &mut fresh, &moved)?;
            if new == *old {
                node
            }
            else {
                NodeAddress::Consumer(arena.mint_consumer(new)?)
            }
        },
        NodeAddress::Command(id) => {
            let old = arena.command(id).ok_or(dangling)?;
            let new = rebuild_command(old, &mut fresh)?;
            if new == *old {
                node
            }
            else {
                NodeAddress::Command(arena.mint_command(new)?)
            }
        },
    })
}

/// A producer over fresh children, its variable moved.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`rebuild`].
fn rebuild_producer<Moved>(
    node: &ProducerNode,
    fresh: &mut Fresh,
    moved: &Moved,
) -> Result<ProducerNode, ClosureRefusal>
where
    Moved: Fn(Space, DeBruijnIndex) -> Result<DeBruijnIndex, ClosureRefusal>,
{
    Ok(match *node {
        ProducerNode::Reify(ref frames) => {
            let mut rebuilt = Vec::with_capacity(frames.len());
            for frame in frames.iter() {
                rebuilt.push(match *frame {
                    gandr_core_term::control::StackFrame::Apply(_) => {
                        gandr_core_term::control::StackFrame::Apply(fresh.producer()?)
                    },
                    gandr_core_term::control::StackFrame::Bind(_) => {
                        gandr_core_term::control::StackFrame::Bind(fresh.command()?)
                    },
                    gandr_core_term::control::StackFrame::Project(component) => {
                        gandr_core_term::control::StackFrame::Project(component)
                    },
                });
            }
            ProducerNode::Reify(alloc::sync::Arc::from(rebuilt))
        },
        ProducerNode::Primitive {
            primitive,
            mut arguments,
        } => {
            for argument in arguments.iter_mut() {
                *argument = fresh.producer()?;
            }
            ProducerNode::Primitive {
                primitive,
                arguments,
            }
        },
        ProducerNode::Decompose(_) => ProducerNode::Decompose(fresh.producer()?),
        ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index,
        } => ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: moved(Space::Producers, index)?,
        },
        ProducerNode::Variable {
            zone: Zone::Linear, ..
        }
        | ProducerNode::Constant(_)
        | ProducerNode::Literal(_)
        | ProducerNode::Code(_) => node.clone(),
        ProducerNode::Constructor {
            ref tag,
            ref producers,
            ref consumers,
        } => ProducerNode::Constructor {
            tag: tag.clone(),
            producers: fresh.producers(producers)?,
            consumers: fresh.consumers(consumers)?,
        },
        ProducerNode::Thunk { .. } => ProducerNode::Thunk {
            body: fresh.command()?,
        },
        ProducerNode::Fixpoint { evidence, .. } => ProducerNode::Fixpoint {
            body: fresh.command()?,
            evidence,
        },
        ProducerNode::Cocase { ref arms } => ProducerNode::Cocase {
            arms: arms
                .iter()
                .map(|arm| {
                    Ok(CopatternArm {
                        destructor: arm.destructor,
                        body: fresh.command()?,
                    })
                })
                .collect::<Result<_, ClosureRefusal>>()?,
        },
        ProducerNode::Closure {
            ref environment, ..
        } => ProducerNode::Closure {
            environment: fresh.producers(environment)?,
            code: fresh.producer()?,
        },
        ProducerNode::Mu { .. } => ProducerNode::Mu {
            body: fresh.command()?,
        },
    })
}

/// A consumer over fresh children, its covariable moved.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`rebuild`].
fn rebuild_consumer<Moved>(
    node: &ConsumerNode,
    fresh: &mut Fresh,
    moved: &Moved,
) -> Result<ConsumerNode, ClosureRefusal>
where
    Moved: Fn(Space, DeBruijnIndex) -> Result<DeBruijnIndex, ClosureRefusal>,
{
    Ok(match *node {
        ConsumerNode::Covariable(index) => {
            ConsumerNode::Covariable(CovariableIndex::from(u32::from(moved(
                Space::Covariables,
                DeBruijnIndex::from(u32::from(index)),
            )?)))
        },
        ConsumerNode::MuTilde { .. } => ConsumerNode::MuTilde {
            body: fresh.command()?,
        },
        ConsumerNode::Destructor {
            tag,
            ref producers,
            ref consumers,
        } => ConsumerNode::Destructor {
            tag,
            producers: fresh.producers(producers)?,
            consumers: fresh.consumers(consumers)?,
        },
        ConsumerNode::Case { ref arms } => ConsumerNode::Case {
            arms: arms
                .iter()
                .map(|arm| {
                    Ok(PatternArm {
                        constructor: arm.constructor.clone(),
                        body: fresh.command()?,
                    })
                })
                .collect::<Result<_, ClosureRefusal>>()?,
        },
        ConsumerNode::DataCase {
            ref branches,
            ref arities,
            ..
        } => ConsumerNode::DataCase {
            branches: fresh.producers(branches)?,
            arities: arities.clone(),
            then: fresh.consumer()?,
        },
        ConsumerNode::Select { ref selector, .. } => ConsumerNode::Select {
            selector: selector.clone(),
            then: fresh.consumer()?,
        },
        ConsumerNode::ListFold {
            element, result, ..
        } => ConsumerNode::ListFold {
            element,
            result,
            on_nil: fresh.command()?,
            on_cons: fresh.command()?,
            continuation: fresh.consumer()?,
        },
        ConsumerNode::Top => ConsumerNode::Top,
    })
}

/// A command over fresh children.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`rebuild`].
fn rebuild_command(
    node: &CommandNode,
    fresh: &mut Fresh,
) -> Result<CommandNode, ClosureRefusal>
{
    Ok(match *node {
        CommandNode::Perform {
            ref signature,
            ref operation,
            route,
            ..
        } => {
            let route = match route {
                Route::Nearest => Route::Nearest,
                Route::Capability(_) => Route::Capability(fresh.producer()?),
            };
            CommandNode::Perform {
                signature: signature.clone(),
                operation: operation.clone(),
                route,
                payload: fresh.producer()?,
                continuation: fresh.consumer()?,
            }
        },
        CommandNode::Handle {
            ref signature,
            introduces,
            ref clauses,
            ..
        } => {
            let subject = fresh.command()?;
            let on_return = fresh.command()?;
            let clauses = clauses
                .iter()
                .map(|clause| {
                    Ok(gandr_core_term::control::EffectClause {
                        operation: clause.operation.clone(),
                        body: fresh.command()?,
                    })
                })
                .collect::<Result<Vec<_>, ClosureRefusal>>()?;
            CommandNode::Handle {
                signature: signature.clone(),
                introduces,
                subject,
                on_return,
                clauses: alloc::sync::Arc::from(clauses),
                continuation: fresh.consumer()?,
            }
        },
        CommandNode::Resume { .. } => CommandNode::Resume {
            stack: fresh.producer()?,
            body: fresh.command()?,
            continuation: fresh.consumer()?,
        },
        CommandNode::Abandon { .. } => CommandNode::Abandon {
            stack: fresh.producer()?,
            continuation: fresh.consumer()?,
        },
        CommandNode::Reset { .. } => CommandNode::Reset {
            body: fresh.command()?,
            continuation: fresh.consumer()?,
        },
        CommandNode::Shift { .. } => CommandNode::Shift {
            body: fresh.command()?,
            continuation: fresh.consumer()?,
        },
        CommandNode::Cut { polarity, .. } => CommandNode::Cut {
            polarity,
            producer: fresh.producer()?,
            consumer: fresh.consumer()?,
        },
        CommandNode::Memory { ref form, .. } => {
            let form = form.try_map(
                ChildOrder::Forward,
                fresh,
                |fresh, _| fresh.producer(),
                |fresh, _| fresh.command(),
            )?;
            CommandNode::Memory {
                form,
                continuation: fresh.consumer()?,
            }
        },
    })
}

/// What a sweep does at a node once its children are rebuilt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sweep
{
    /// Convert each closure.
    Convert,
    /// Enter each closure redex.
    Enter,
}

/// A node's place under its parent.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Role
{
    /// A closure in its own right, where it is a closure former.
    Free,
    /// A closure's code or a nominal match's branch: entered where its
    /// parent stands, never a closure of its own.
    Held,
}

/// The role `child` takes under `parent`.
///
/// # Specification
/// trivial.
fn role(
    arena: &CommandArena,
    parent: NodeAddress,
    child: NodeAddress,
) -> Role
{
    let held = match (parent, child) {
        (NodeAddress::Producer(parent), NodeAddress::Producer(child)) => matches!(
            arena.producer(parent),
            Some(&ProducerNode::Closure { code, .. }) if code == child
        ),
        (NodeAddress::Consumer(parent), NodeAddress::Producer(child)) => matches!(
            arena.consumer(parent),
            Some(ConsumerNode::DataCase { branches, .. }) if branches.contains(&child)
        ),
        (
            NodeAddress::Producer(_) | NodeAddress::Consumer(_) | NodeAddress::Command(_),
            NodeAddress::Producer(_) | NodeAddress::Consumer(_) | NodeAddress::Command(_),
        ) => false,
    };
    if held { Role::Held } else { Role::Free }
}

/// One step of a sweep's post-order walk.
#[derive(Clone, Copy, Debug)]
enum Swept
{
    /// Schedule the node's children.
    Enter(NodeAddress, Role),
    /// Rebuild the node over its children's images and rewrite it.
    Exit(NodeAddress, Role),
}

/// A sweep over a term.
struct Pass<'arena>
{
    /// The arena swept in.
    arena: &'arena mut CommandArena,
    /// The rewrite applied at each node.
    sweep: Sweep,
    /// Each node visited in its role, beside its image.
    done: BTreeMap<(NodeAddress, Role), NodeAddress>,
}

impl<'arena> Pass<'arena>
{
    /// A sweep of `sweep` over `arena`.
    ///
    /// # Specification
    /// trivial.
    fn new(
        arena: &'arena mut CommandArena,
        sweep: Sweep,
    ) -> Self
    {
        Self {
            arena,
            sweep,
            done: BTreeMap::new(),
        }
    }

    /// The image of `root`: every node below it rebuilt over its children's
    /// images and rewritten once they are.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`convert_step`] and [`beta`].
    fn run(
        mut self,
        root: NodeAddress,
    ) -> Result<NodeAddress, ClosureRefusal>
    {
        let mut stack = Vec::from([Swept::Enter(root, Role::Free)]);
        while let Some(visit) = stack.pop() {
            match visit {
                Swept::Enter(node, role) => {
                    if self.done.contains_key(&(node, role)) {
                        continue;
                    }
                    stack.push(Swept::Exit(node, role));
                    let work = stack.len();
                    let arena = &*self.arena;
                    children(arena, node, |child, _| {
                        stack.push(Swept::Enter(child, self::role(arena, node, child)));
                        Ok(())
                    })?;
                    if let Some(pushed) = stack.get_mut(work ..) {
                        pushed.reverse();
                    }
                },
                Swept::Exit(node, role) => {
                    if self.done.contains_key(&(node, role)) {
                        continue;
                    }
                    let mut images = Vec::new();
                    let arena = &*self.arena;
                    children(arena, node, |child, _| {
                        let key = (child, self::role(arena, node, child));
                        images.push(*self.done.get(&key).ok_or(ClosureRefusal::Dangling(child))?);
                        Ok(())
                    })?;
                    let image = rebuild(self.arena, node, images, |_, index| Ok(index))?;
                    let image = self.rewrite(image, role)?;
                    self.done.insert((node, role), image);
                },
            }
        }
        self.done
            .get(&(root, Role::Free))
            .copied()
            .ok_or(ClosureRefusal::Dangling(root))
    }

    /// `image` rewritten by the sweep in `role`: a free closure converted, a
    /// closure redex entered, any other node kept.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`convert_step`] and [`beta`].
    fn rewrite(
        &mut self,
        image: NodeAddress,
        role: Role,
    ) -> Result<NodeAddress, ClosureRefusal>
    {
        match (self.sweep, image, role) {
            (Sweep::Convert, NodeAddress::Producer(id), Role::Free) => {
                if framed(self.arena, id)?.is_none() {
                    return Ok(image);
                }
                let mut current = id;
                while let Some(next) = step(self.arena, current)? {
                    current = next;
                }
                Ok(NodeAddress::Producer(current))
            },
            (Sweep::Enter, NodeAddress::Command(id), _) => {
                Ok(enter(self.arena, id)?.map_or(image, NodeAddress::Command))
            },
            (Sweep::Convert, NodeAddress::Producer(_), Role::Held)
            | (Sweep::Convert, NodeAddress::Consumer(_) | NodeAddress::Command(_), _)
            | (Sweep::Enter, NodeAddress::Producer(_) | NodeAddress::Consumer(_), _) => Ok(image),
        }
    }
}

/// The bindings entering a closure cut against a frame its code answers,
/// leaving a refusal's partial nodes for the caller to truncate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`beta`].
fn enter(
    arena: &mut CommandArena,
    cut: CommandId,
) -> Result<Option<CommandId>, ClosureRefusal>
{
    let &CommandNode::Cut {
        producer, consumer, ..
    } = arena
        .command(cut)
        .ok_or(ClosureRefusal::Dangling(NodeAddress::Command(cut)))?
    else {
        return Ok(None);
    };
    let Some((environment, code)) = framed(arena, producer)?
    else {
        return Ok(None);
    };
    let environment = environment.to_vec();
    let ConsumerNode::Destructor {
        tag,
        producers: ref arguments,
        consumers: ref continuations,
    } = *arena
        .consumer(consumer)
        .ok_or(ClosureRefusal::Dangling(NodeAddress::Consumer(consumer)))?
    else {
        return Ok(None);
    };
    let (arguments, continuations) = (arguments.to_vec(), continuations.to_vec());
    let (body, recursive) = match *arena
        .producer(code)
        .ok_or(ClosureRefusal::Dangling(NodeAddress::Producer(code)))?
    {
        ProducerNode::Cocase { ref arms } => match arms.iter().find(|arm| arm.destructor == tag) {
            Some(arm) => (arm.body, false),
            None => return Ok(None),
        },
        ProducerNode::Thunk { body } if tag == DestructorTag::Force => (body, false),
        ProducerNode::Fixpoint { body, .. } if tag == DestructorTag::Force => (body, true),
        ProducerNode::Reify(_)
        | ProducerNode::Primitive { .. }
        | ProducerNode::Decompose(_)
        | ProducerNode::Variable { .. }
        | ProducerNode::Constant(_)
        | ProducerNode::Literal(_)
        | ProducerNode::Code(_)
        | ProducerNode::Constructor { .. }
        | ProducerNode::Thunk { .. }
        | ProducerNode::Fixpoint { .. }
        | ProducerNode::Closure { .. }
        | ProducerNode::Mu { .. } => return Ok(None),
    };
    // The values the body binds, outermost first: the environment, the
    // closure itself for a recursive thunk, then the frame's arguments.
    let mut values = environment;
    if recursive {
        values.push(producer);
    }
    values.extend(arguments);
    let bound = continuations.len();
    let mut command = body;
    for (position, &value) in values.iter().enumerate().rev() {
        let shifted = rename(arena, NodeAddress::Producer(value), Renaming::Shift {
            producers: position,
            covariables: bound,
        })?;
        let NodeAddress::Producer(shifted) = shifted
        else {
            return Err(ClosureRefusal::Dangling(shifted));
        };
        let polarity = value_polarity(arena, shifted)?;
        let binder = arena.mint_consumer(ConsumerNode::MuTilde { body: command })?;
        command = arena.mint_cut(polarity, shifted, binder)?;
    }
    for (position, &continuation) in continuations.iter().enumerate().rev() {
        let shifted = rename(
            arena,
            NodeAddress::Consumer(continuation),
            Renaming::Shift {
                producers: 0,
                covariables: position,
            },
        )?;
        let NodeAddress::Consumer(shifted) = shifted
        else {
            return Err(ClosureRefusal::Dangling(shifted));
        };
        let polarity = consumer_polarity(
            arena
                .consumer(shifted)
                .ok_or(ClosureRefusal::Dangling(NodeAddress::Consumer(shifted)))?,
        )
        .unwrap_or(Polarity::Positive);
        let capture = arena.mint_producer(ProducerNode::Mu { body: command })?;
        command = arena.mint_cut(polarity, capture, shifted)?;
    }
    Ok(Some(command))
}

/// The polarity a cut binding the value `value` takes: the one it observes,
/// its code's for a closure, positive for one that takes the cut's.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Dangling`] for a value or code the arena does not hold.
fn value_polarity(
    arena: &CommandArena,
    value: ProducerId,
) -> Result<Polarity, ClosureRefusal>
{
    let mut node = arena
        .producer(value)
        .ok_or(ClosureRefusal::Dangling(NodeAddress::Producer(value)))?;
    if let ProducerNode::Closure { code, .. } = *node {
        node = arena
            .producer(code)
            .ok_or(ClosureRefusal::Dangling(NodeAddress::Producer(code)))?;
    }
    Ok(producer_polarity(node).unwrap_or(Polarity::Positive))
}

#[cfg(test)]
mod tests;
