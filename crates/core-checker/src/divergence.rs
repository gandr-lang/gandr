//! Divergence as a row entry: a partial fixpoint states that it may run
//! forever.
//!
//! A fixpoint with partial evidence is a loop the checker cannot see out of.
//! It checks only at a type each returner of which holds [`PARTIAL`], the host
//! interface with no operation: the returners its arrows and dependent arrows
//! end in, and those of each component of a lazy product. A returner whose
//! row lacks it refuses the fixpoint as a [`CheckRefusal::TypeMismatch`]
//! whose synthesised type is the expected one with `Partial` added to every
//! such row, which is the row the declaration has to write. Nothing eliminates
//! the entry: a caller of a diverging function holds it in its own row, as it
//! holds any interface its callee performs, and a handler or a capability
//! scope of `Partial` has no operation to answer and leaves it in the row it
//! answers at. The empty row is the row of a computation that returns, and a
//! conversion drops an unread call of a variable whose type ends in empty rows
//! alone ([`returning`]): it runs to its end and nothing observes it.
//!
//! # Boundaries
//!
//! - A fixpoint whose body never names its own binder passes: it does not
//!   recurse, so it runs its body once.
//! - The unknown type passes: it is consistent with every row.
//! - A codata type passes: its observations answer one at a time, and the
//!   lowering admits a recursive call only as the whole of an observation's
//!   arm, so each observation yields before the function runs again.
//! - The fixpoint of a ruled operation passes: its rules are oriented, which
//!   the kernel decides when it admits them, so its recursion terminates.
//! - A loop that follows a protocol passes: each pass opens with the placement
//!   of an endpoint the loop threads, and every path to the next pass acts on
//!   that endpoint first, so each pass waits on its peer or makes a move of the
//!   protocol before it runs again ([`follows`]). A path that runs again with
//!   the endpoint untouched owes the entry, as any loop does.
//! - A decode of a computation code no definition unfolds is refused as a
//!   [`CheckRefusal::ShapeMismatch`] wanting a returner: its row is not seen,
//!   so it cannot state the entry.

#[cfg(test)]
mod tests;

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::Calls;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectPresence;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::Purity;
use gandr_core_term::effect::host::PARTIAL;
use gandr_core_term::effect::host::partiality;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::row::Label;
use gandr_core_term::session::SessionAction;
use gandr_core_term::support::Crossing;
use gandr_core_term::support::ThinningRef;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// What a partial fixpoint's type says about divergence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Divergence
{
    /// Every returner the type ends in holds [`PARTIAL`], or none is seen.
    Stated,
    /// Some returner lacks it: the type with [`PARTIAL`] added to each that
    /// does.
    Unstated(CompTypeId),
}

/// Refuse the partial fixpoint `at` over `body` unless `expected` states that
/// it may run forever, its body never names its own binder, it follows a
/// protocol, or the declaration under judgement is a ruled operation.
///
/// # Specification
/// - requires: `expected` is formed; `body` is the body of the fixpoint `at`.
/// - ensures: success exactly when the admitted declaration carries operation
///   rules, `body`'s support omits its innermost variable, [`follows`] answers
///   that every pass acts on an endpoint it threads, or [`stated`] answers
///   [`Divergence::Stated`].
/// - fails: [`CheckRefusal::TypeMismatch`] at `at`, synthesising the type
///   [`stated`] rebuilt and expecting `expected`; as [`follows`] and
///   [`stated`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a loop at a returner with and without the entry, a
///   fixpoint that never names itself at the empty row, and a ruled operation's
///   fixpoint at the empty row, each asserted as the exact verdict; the loops
///   [`follows`] reads, through the corpus's protocol loops at the empty row.
/// - witness: `divergence::tests::a_partial_fixpoint_states_partial_in_every_row_it_ends_in`
/// - witness: `divergence::tests::a_fixpoint_that_never_recurses_needs_no_entry`
/// - witness: `divergence::tests::a_ruled_operation_terminates_by_its_rules`
/// - witness: `divergence::tests::a_loop_follows_its_protocol_only_when_every_pass_acts_first`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::TypeMismatch(Mismatch::Computation { at: site, expected: wanted, .. })) => site == at && wanted == expected,
    | Ok(()) | Err(_) => true,
})]
pub fn require(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    body: ComputationId,
    expected: CompTypeId,
) -> Result<(), CheckRefusal>
{
    if !context.admitted_rules().is_empty() {
        return Ok(());
    }
    let support = context
        .arena()
        .computation_support(body)
        .ok_or(CheckRefusal::DanglingNode {
            node: CoreNode::Term(TermNode::Computation(body)),
        })?;
    if let Maybe::Absent(_) = support.rank(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) {
        return Ok(());
    }
    if follows(context.arena(), body)? == Protocol::Followed {
        return Ok(());
    }
    match stated(context, at, expected)? {
        Divergence::Stated => Ok(()),
        Divergence::Unstated(synthesised) => {
            Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
                at,
                synthesised,
                expected,
            }))
        },
    }
}

/// The children of one computation, each with the binders its former opens
/// over it.
#[derive(Default)]
struct Opened
{
    /// The value children.
    values: Vec<(ValueId, Crossing)>,
    /// The computation children.
    computations: Vec<(ComputationId, Crossing)>,
}

impl gandr_core_term::children::Visit for Opened
{
    /// Keep a value child.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        child: ValueId,
        crossing: Crossing,
    )
    {
        self.values.push((child, crossing));
    }

    /// Keep a computation child.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        child: ComputationId,
        crossing: Crossing,
    )
    {
        self.computations.push((child, crossing));
    }

    /// Pass a value-type child: a type runs no pass.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        _child: ValueTypeId,
        _crossing: Crossing,
    )
    {
    }

    /// Pass a computation-type child: a type runs no pass.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        _child: CompTypeId,
        _crossing: Crossing,
    )
    {
    }
}

/// A computation of a loop's pass, with the names the walk reads it by.
#[derive(Clone, Debug)]
struct Pass
{
    /// The computation.
    at: ComputationId,
    /// The loop's own binder, by its intuitionistic index where `at` stands.
    own: DeBruijnIndex,
    /// The endpoints the loop threads, by their linear indices where `at`
    /// stands.
    ends: Vec<DeBruijnIndex>,
}

impl Pass
{
    /// The same pass at `child`, past the binders `crossing` opens.
    ///
    /// # Specification
    /// trivial.
    fn under(
        &self,
        child: ComputationId,
        crossing: Crossing,
    ) -> Self
    {
        let past = |index: DeBruijnIndex, zone: Zone| {
            let crossed = u32::try_from(usize::from(crossing.depth(zone))).unwrap_or(u32::MAX);
            DeBruijnIndex::from(u32::from(index).saturating_add(crossed))
        };
        Self {
            at: child,
            own: past(self.own, Zone::Intuitionistic),
            ends: self
                .ends
                .iter()
                .map(|&end| past(end, Zone::Linear))
                .collect(),
        }
    }
}

/// The node `at` and its children.
///
/// # Specification
/// - ensures: the node the arena holds at `at`, and each of its children with
///   the binders its former opens over it, as
///   [`gandr_core_term::children::of_computation`] lists them.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold.
/// - panics: none.
/// - executable: none — the children are the visitor's, which a predicate would
///   list again.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`follows`], which reads every node through it.
/// - witness: `divergence::tests::a_loop_follows_its_protocol_only_when_every_pass_acts_first`
fn opened(
    arena: &CoreArena,
    at: ComputationId,
) -> Result<(&Computation, Opened), CheckRefusal>
{
    let node = arena.computation(at).ok_or(CheckRefusal::DanglingNode {
        node: CoreNode::Term(TermNode::Computation(at)),
    })?;
    let mut children = Opened::default();
    gandr_core_term::children::of_computation(node, &mut children);
    Ok((node, children))
}

/// Whether a support reads a loop's own binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// It reads the binder, or the arena holds no support to tell.
    Own,
    /// It reads other variables only.
    Other,
}

/// Whether `support` reads the intuitionistic variable `own`.
///
/// # Specification
/// trivial.
fn reading(
    support: Option<ThinningRef<'_>>,
    own: DeBruijnIndex,
) -> Reading
{
    match support.map(|support| support.rank(Zone::Intuitionistic, own)) {
        None | Some(Maybe::Present(_)) => Reading::Own,
        Some(Maybe::Absent(_)) => Reading::Other,
    }
}

/// Whether a computation moves on a loop's endpoint before it returns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Acting
{
    /// Every path through it moves on one of the endpoints.
    Moves,
    /// Some path returns without a move.
    Idles,
}

/// Whether `action` is a move on one of the endpoints `ends`: a send, a
/// receive, a selection, an offer or a close.
///
/// # Specification
/// trivial.
fn moving(
    action: &SessionAction,
    ends: &[DeBruijnIndex],
) -> Acting
{
    match (action.kind(), action.endpoint()) {
        (Maybe::Present(_), Maybe::Present(end)) if ends.contains(&end) => Acting::Moves,
        _ => Acting::Idles,
    }
}

/// Whether a loop follows its protocol.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Protocol
{
    /// Every pass moves on an endpoint the loop threads before the next pass.
    Followed,
    /// The loop threads no endpoint, or a pass can run the next one untouched.
    Unfollowed,
}

/// Whether every pass of the loop whose fixpoint body is `body` acts on an
/// endpoint the loop threads before it runs the next pass.
///
/// # Specification
/// - requires: `body` is the body of a fixpoint, its own binder innermost.
/// - ensures: [`Protocol::Followed`] exactly when the pass opens, past its
///   parameter and the slots it splits and holds, with the placement of at
///   least one endpoint, and every occurrence of the fixpoint's own binder in
///   the pass stands after a move on one of the endpoints placed there: under a
///   move's body or arms, or in a bind's rest once [`acts`] answers its first
///   part. An occurrence in a value, or under any other former before a move,
///   answers [`Protocol::Unfollowed`].
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold.
/// - panics: none.
/// - executable: none — the verdict is the walk, which a predicate would
///   restate.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `loop` reads one child per turn, and the `while let` pops a
///   worklist each turn pushes only children onto.
/// - measure: the nodes under `body`, each minted after its children.
///
/// # Adequacy
/// - hypothesis: L3 — a pass that moves before it runs again, one with a path
///   that runs again untouched, one that acts in a bind's first part, one that
///   returns before it runs again, and a loop that threads no endpoint, each
///   asserted as the exact verdict.
/// - witness: `divergence::tests::a_loop_follows_its_protocol_only_when_every_pass_acts_first`
pub fn follows(
    arena: &CoreArena,
    body: ComputationId,
) -> Result<Protocol, CheckRefusal>
{
    let mut entry = Pass {
        at: body,
        own: DeBruijnIndex::from(0_u32),
        ends: Vec::new(),
    };
    loop {
        let (node, children) = opened(arena, entry.at)?;
        let placed = matches!(*node, Computation::Session(SessionAction::Place { .. }));
        let threads = placed
            || matches!(
                *node,
                Computation::Lambda(_)
                    | Computation::Split { .. }
                    | Computation::Memory(MemoryForm::Hold { .. })
            );
        let (true, &[(inner, crossing)]) = (threads, children.computations.as_slice())
        else {
            break;
        };
        entry = entry.under(inner, crossing);
        if placed {
            entry.ends.push(DeBruijnIndex::from(0_u32));
        }
    }
    if entry.ends.is_empty() {
        return Ok(Protocol::Unfollowed);
    }
    let mut pending = vec![entry];
    while let Some(pass) = pending.pop() {
        if reading(arena.computation_support(pass.at), pass.own) == Reading::Other {
            continue;
        }
        let (node, children) = opened(arena, pass.at)?;
        for &(value, crossing) in &children.values {
            let own = pass.under(pass.at, crossing).own;
            if reading(arena.value_support(value), own) == Reading::Own {
                return Ok(Protocol::Unfollowed);
            }
        }
        if let Computation::Session(ref action) = *node
            && moving(action, &pass.ends) == Acting::Moves
        {
            continue;
        }
        if let (&Computation::Bind(..), &[(first, before), (rest, after)]) =
            (node, children.computations.as_slice())
        {
            if acts(arena, &pass.under(first, before))? == Acting::Idles {
                pending.push(pass.under(rest, after));
            }
            pending.push(pass.under(first, before));
            continue;
        }
        pending.extend(
            children
                .computations
                .iter()
                .map(|&(child, crossing)| pass.under(child, crossing)),
        );
    }
    Ok(Protocol::Followed)
}

/// How a former's answer joins its children's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Join
{
    /// It moves when every child does: a case's arms, a scope's body.
    Every,
    /// It moves when one child does: a bind's first part or its rest.
    Any,
}

/// A former whose answer waits on the children not yet read.
#[derive(Debug)]
struct Frame
{
    /// How the children's answers join.
    join: Join,
    /// The children still to read.
    children: Vec<Pass>,
}

/// The answer of `pass`'s node alone, or the frame its children owe it,
/// pushed onto `frames`.
///
/// # Specification
/// - ensures: [`Acting::Moves`] for a move on one of the endpoints; a frame
///   joining [`Join::Any`] for a bind, and [`Join::Every`] for an ascription, a
///   case, a split, a data case, a list case, another session action or a
///   memory form, each pushed with its children and answering nothing;
///   [`Acting::Idles`] for such a former with no computation child and for
///   every other former.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold.
/// - panics: none.
/// - executable: none — the answer is the former's reading, which a predicate
///   would restate.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`acts`].
/// - witness: `divergence::tests::a_loop_follows_its_protocol_only_when_every_pass_acts_first`
fn step(
    arena: &CoreArena,
    pass: &Pass,
    frames: &mut Vec<Frame>,
) -> Result<Option<Acting>, CheckRefusal>
{
    let (node, children) = opened(arena, pass.at)?;
    let join = match *node {
        Computation::Session(ref action) if moving(action, &pass.ends) == Acting::Moves => {
            return Ok(Some(Acting::Moves));
        },
        Computation::Bind(..) => Join::Any,
        Computation::Ascribe { .. }
        | Computation::Case { .. }
        | Computation::Split { .. }
        | Computation::DataCase { .. }
        | Computation::ListCase { .. }
        | Computation::Session(_)
        | Computation::Memory(_) => Join::Every,
        Computation::Primitive { .. }
        | Computation::Transport(..)
        | Computation::PathTransport { .. }
        | Computation::Ride { .. }
        | Computation::Decompose(_)
        | Computation::TelescopeTransport { .. }
        | Computation::Lambda(_)
        | Computation::Fixpoint { .. }
        | Computation::Application(..)
        | Computation::Return(_)
        | Computation::Force(_)
        | Computation::RecordProjection(..)
        | Computation::TupleProjection(..)
        | Computation::Hole(_)
        | Computation::Mark { .. }
        | Computation::ListFold { .. }
        | Computation::Perform { .. }
        | Computation::Handle { .. }
        | Computation::Exercise { .. }
        | Computation::Scope { .. }
        | Computation::Resume(..)
        | Computation::Abandon { .. }
        | Computation::Reset { .. }
        | Computation::Shift(_)
        | Computation::With(_)
        | Computation::Project(..)
        | Computation::World(_) => return Ok(Some(Acting::Idles)),
    };
    if children.computations.is_empty() {
        return Ok(Some(Acting::Idles));
    }
    frames.push(Frame {
        join,
        children: children
            .computations
            .iter()
            .map(|&(child, crossing)| pass.under(child, crossing))
            .collect(),
    });
    Ok(None)
}

/// Whether every path through `pass` moves on one of its endpoints before it
/// returns.
///
/// # Specification
/// - ensures: [`Acting::Moves`] for a move on one of the endpoints; for a bind
///   whose first part or rest moves; and for an ascription, a case, a split, a
///   data case, a list case, another session action or a memory form that holds
///   at least one computation and every one of which moves. [`Acting::Idles`]
///   for every other former.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold.
/// - panics: none.
/// - executable: none — the verdict is the walk, which a predicate would
///   restate.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: each turn reads one child a frame holds, or pops a frame, and a
///   frame is pushed only for a node's children.
/// - measure: the nodes under `pass`, each minted after its children.
///
/// # Adequacy
/// - hypothesis: L3 — as [`follows`], whose bind reads this answer.
/// - witness: `divergence::tests::a_loop_follows_its_protocol_only_when_every_pass_acts_first`
fn acts(
    arena: &CoreArena,
    pass: &Pass,
) -> Result<Acting, CheckRefusal>
{
    let mut frames: Vec<Frame> = Vec::new();
    let mut answer = step(arena, pass, &mut frames)?;
    loop {
        let Some(frame) = frames.last_mut()
        else {
            return Ok(answer.unwrap_or(Acting::Idles));
        };
        if let Some(acting) = answer {
            let settled = match (frame.join, acting) {
                (Join::Every, Acting::Idles) | (Join::Any, Acting::Moves) => Some(acting),
                (Join::Every, Acting::Moves) | (Join::Any, Acting::Idles) => None,
            };
            if let Some(settled) = settled {
                let _settled = frames.pop();
                answer = Some(settled);
                continue;
            }
        }
        let Some(child) = frame.children.pop()
        else {
            let join = frame.join;
            let _done = frames.pop();
            answer = Some(match join {
                Join::Every => Acting::Moves,
                Join::Any => Acting::Idles,
            });
            continue;
        };
        answer = step(arena, &child, &mut frames)?;
    }
}

/// Whether every returner `expected` ends in holds [`PARTIAL`], and the type
/// with it added where one does not.
///
/// # Specification
/// - requires: `expected` is formed.
/// - ensures: [`Divergence::Stated`] when each returner reached through arrows,
///   dependent arrows, lazy-product components and decodes that unfold holds
///   [`PARTIAL`]; otherwise [`Divergence::Unstated`] with the type whose every
///   such returner holds it, the rest unchanged.
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at` wanting a returner for a
///   decode no definition unfolds; [`CheckRefusal::EffectSignatureConflict`] at
///   `at` for a row whose own `Partial` performs an operation; the weak-head
///   reading's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a returner, an arrow to one, a lazy product with one
///   component stating the entry and one not, and a returner already holding
///   it, each asserted as the exact answer.
/// - witness: `divergence::tests::a_partial_fixpoint_states_partial_in_every_row_it_ends_in`
/// - witness: `divergence::tests::a_dependent_arrow_states_partial_in_its_codomain_and_a_stuck_decode_is_refused`
#[spec(ensures: |ret| match ret {
    | Ok(Divergence::Unstated(rebuilt)) => rebuilt != expected,
    | Ok(Divergence::Stated) | Err(_) => true,
})]
pub fn stated(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    expected: CompTypeId,
) -> Result<Divergence, CheckRefusal>
{
    // Walk down first: each node is read at its weak head and recorded after
    // the node it stands under, so the rebuild below meets children first.
    let mut order: Vec<(CompTypeId, CompTypeId)> = Vec::new();
    let mut pending = vec![expected];
    while let Some(shape) = pending.pop() {
        let head = context.whnf_comp_type(shape)?;
        order.push((shape, head));
        match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { codomain, .. } | CompTypeView::Pi { codomain, .. } => {
                pending.push(codomain);
            },
            CompTypeView::With(components) => pending.extend(components.iter().copied()),
            CompTypeView::Element { .. } => {
                return Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Returner,
                    found: TypeNode::Computation(shape),
                });
            },
            CompTypeView::Returner { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. } => {
            },
        }
    }
    let entry = EffectRow::singleton(partiality());
    let name = gandr_core_term::effect::EffectLabel::Interface(Label::from(PARTIAL));
    let mut rebuilt: BTreeMap<CompTypeId, CompTypeId> = BTreeMap::new();
    for &(shape, head) in order.iter().rev() {
        let arena = context.arena();
        let replaced = match comp_type_view(arena, head)? {
            CompTypeView::Returner { result, effects } => match effects.contains(&name) {
                EffectPresence::Present => None,
                EffectPresence::Absent => {
                    let row = effects.union(&entry, arena).map_err(|_conflict| {
                        CheckRefusal::EffectSignatureConflict {
                            at,
                            first: head,
                            second: expected,
                        }
                    })?;
                    Some(
                        context
                            .arena_mut()
                            .comp_type_returner_with_effects(result, row),
                    )
                },
            },
            CompTypeView::Arrow { domain, codomain } => rebuilt
                .get(&codomain)
                .copied()
                .map(|codomain| context.arena_mut().comp_type_arrow(domain, codomain)),
            CompTypeView::Pi { domain, codomain } => rebuilt
                .get(&codomain)
                .copied()
                .map(|codomain| context.arena_mut().comp_type_pi(domain, codomain)),
            CompTypeView::With(components) => components
                .iter()
                .any(|part| rebuilt.contains_key(part))
                .then(|| {
                    components
                        .iter()
                        .map(|part| rebuilt.get(part).copied().unwrap_or(*part))
                        .collect::<Vec<CompTypeId>>()
                })
                .map(|parts| context.arena_mut().comp_type_with(&parts)),
            CompTypeView::Element { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. } => {
                None
            },
        };
        if let Some(replaced) = replaced {
            let _previous = rebuilt.insert(shape, replaced);
        }
    }
    Ok(rebuilt
        .get(&expected)
        .copied()
        .map_or(Divergence::Stated, Divergence::Unstated))
}

/// Whether every call of a variable of type `bound` returns.
///
/// # Specification
/// - requires: `bound` is formed.
/// - ensures: [`Calls::Return`] exactly when `bound`'s weak head is a thunk
///   type each returner of which, reached through arrows, dependent arrows and
///   lazy-product components at their weak heads, has the empty row;
///   [`Calls::Unknown`] for any other type, and for one that reaches a decode
///   no definition unfolds, a codata type or the unknown type.
/// - fails: the weak-head reading's refusal.
/// - panics: none.
/// - executable: none — the answer reads the arena's types at their weak heads,
///   which the witness holds to stated types.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loop over an explicit worklist, not recursion.
/// - measure: the computation types under the thunk, each read once: a node is
///   replaced by its codomain or its components, minted before it.
///
/// # Adequacy
/// - hypothesis: L3 — a function to a returner at the empty row, the same at a
///   row holding `Partial`, a lazy product with one such component, and a value
///   type that is no thunk, each asserted as the exact answer.
/// - witness: `divergence::tests::a_call_returns_only_where_every_row_is_empty`
pub fn calls(
    context: &mut CheckingContext<'_>,
    bound: ValueTypeId,
) -> Result<Calls, CheckRefusal>
{
    let head = context.whnf_value_type(bound)?;
    let ValueTypeView::Thunk(computation) = value_type_view(context.arena(), head)?
    else {
        return Ok(Calls::Unknown);
    };
    let mut pending = vec![computation];
    while let Some(shape) = pending.pop() {
        let head = context.whnf_comp_type(shape)?;
        match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { codomain, .. } | CompTypeView::Pi { codomain, .. } => {
                pending.push(codomain);
            },
            CompTypeView::With(components) => pending.extend(components.iter().copied()),
            CompTypeView::Returner { effects, .. } => {
                if effects.purity() != Purity::Pure {
                    return Ok(Calls::Unknown);
                }
            },
            CompTypeView::Element { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. } => {
                return Ok(Calls::Unknown);
            },
        }
    }
    Ok(Calls::Return)
}

/// The intuitionistic variables of the judgement's binders whose calls
/// return, by index, innermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each index whose declared type [`calls`] answers
///   [`Calls::Return`] for, ascending.
/// - provides: the variables a reflexivity's endpoint conversion discards an
///   unread call of.
/// - fails: as [`calls`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`calls`], read at every binder.
/// - witness: `divergence::tests::an_unread_call_converts_only_where_its_row_is_empty`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |indices| indices.is_sorted()))]
pub fn returning(context: &mut CheckingContext<'_>) -> Result<Vec<DeBruijnIndex>, CheckRefusal>
{
    let depth = u32::try_from(usize::from(context.binders().depth(Zone::Intuitionistic)))
        .map_err(|_overflow| CheckRefusal::MachineInvariant)?;
    let mut indices = Vec::new();
    for index in (0 .. depth).map(DeBruijnIndex::from) {
        let declared = context
            .binders()
            .declared(Zone::Intuitionistic, index)
            .map_err(|_unbound| CheckRefusal::MachineInvariant)?;
        if calls(context, declared)? == Calls::Return {
            indices.push(index);
        }
    }
    Ok(indices)
}
