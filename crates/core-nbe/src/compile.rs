//! The compilation of a core term into an overlay root.
//!
//! # One share for each node reached twice
//!
//! [`compile_value`] and [`compile_computation`] read a core term as the DAG
//! that the core arena holds. A node of a former that the overlay grafts
//! becomes that graft over its compiled children. Each other node becomes an
//! opaque leaf, and the walk does not go below it. A node that the walk reaches
//! more than once becomes one share, and each reach becomes one occurrence of
//! it. So the compiled root erases to its input, node for node: erasure names
//! the leg of a share once, as the arena names the node once.
//!
//! The shares stand in one chain at the root. A shared node that another shared
//! node holds finishes first in the walk, and its share stands outside. So a
//! leg reads only the shares outside it, which validation requires. The overlay
//! copies indices and never shifts them: an occurrence reads the free indices
//! of its leg where it stands, and that is what the shared core node means at
//! each of its parents. A share for each binder that a side reads more than
//! once needs a shift at erasure, which `overlay` names as its reversal; the
//! compilation shares only what the arena already shares.
//!
//! The compilation grafts 14 of the 16 formers that the overlay grafts. A
//! quote stays an opaque leaf, read whole wherever it stands, because the
//! duplication walk has no rule to distribute a type inside a term and refuses
//! a grafted quote (`DuplicationFault::Quote`). The compilation mints no share
//! below an opaque former: a share inside a data case, a record, a fixpoint, a
//! list or a word needs a graft for that former first.
//!
//! # Cost
//!
//! The walk reads each node that the root reaches through grafted formers
//! once to count its parents, and once more to mint it, so the work and the
//! overlay nodes it mints are linear in those nodes and their parent edges.
//! The counts live in an ordered map, which adds a log factor; the arena ids
//! are dense, and a table sized to the reached ids is the upgrade when the
//! sweep of the checker's path shows the map in its profile.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::Side;

use crate::overlay::Bound;
use crate::overlay::CompGraft;
use crate::overlay::CompNode;
use crate::overlay::Overlay;
use crate::overlay::OverlayCompId;
use crate::overlay::OverlayFault;
use crate::overlay::OverlayId;
use crate::overlay::OverlayValueId;
use crate::overlay::ShareArity;
use crate::overlay::ShareDistance;
use crate::overlay::SharePosition;
use crate::overlay::Sharing;
use crate::overlay::ValueGraft;
use crate::overlay::ValueNode;

/// Why a core term could not be compiled into an overlay root.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompileFault
{
    /// A node that the walk reaches names nothing in the core arena.
    Dangling,
    /// The overlay refused a mint, in its own vocabulary.
    Overlay(OverlayFault),
    /// A count of parents, a position or a distance passed what its counter
    /// holds.
    Overflow,
    /// The walk's own pairing broke. No input term reaches it while the walk's
    /// own pushes are the only source of tasks; it is reported rather than
    /// asserted.
    MachineInvariant,
}

/// One term node of the core arena.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
}

/// What the overlay makes of one core node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Former
{
    /// A graft with no child.
    Leaf,
    /// An opaque leaf: a former that the overlay does not graft.
    Opaque,
    /// A graft over its children, in the order that the graft lists them.
    Grafted
    {
        /// The children.
        children: [Option<Node>; 3],
    },
}

/// One step of a walk.
#[derive(Clone, Copy, Debug)]
enum Step
{
    /// Reach a node from its parent.
    Enter(Node),
    /// Mint a graft over the children that the steps before it left.
    Exit(Node),
}

/// What the overlay makes of `node`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a graft for each of the 14 formers that the compilation grafts —
///   the unit and the pair as the tuples of no and two components, an injection
///   on the first or the second summand, a case of two branches — with its
///   children in the order the graft lists them; an opaque leaf for every other
///   node, a quote among them.
/// - provides: the one reading of a core former that the count and the mint
///   share.
/// - fails: [`CompileFault::Dangling`] when `node` names nothing in `core`.
/// - panics: none.
/// - executable: none — the clause is the table the body states.
///
/// # Errors
/// - [`CompileFault::Dangling`] — `node` names nothing in `core`.
fn former(
    core: &CoreArena,
    node: Node,
) -> Result<Former, CompileFault>
{
    let grafted = |first: Node, second: Option<Node>, third: Option<Node>| Former::Grafted {
        children: [Some(first), second, third],
    };
    match node {
        Node::Value(id) => {
            let value = core.value(id).ok_or(CompileFault::Dangling)?;
            Ok(match *value {
                Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) => Former::Leaf,
                Value::Tuple(ref components) => match **components {
                    [] => Former::Leaf,
                    [first, second] => grafted(Node::Value(first), Some(Node::Value(second)), None),
                    _ => Former::Opaque,
                },
                Value::Injection(summand, body) if Side::try_from(summand).is_ok() => {
                    grafted(Node::Value(body), None, None)
                },
                Value::Thunk(body) => grafted(Node::Computation(body), None, None),
                Value::Lift { body, .. } => grafted(Node::Value(body), None, None),
                _ => Former::Opaque,
            })
        },
        Node::Computation(id) => {
            let computation = core.computation(id).ok_or(CompileFault::Dangling)?;
            Ok(match *computation {
                Computation::Lambda(body) => grafted(Node::Computation(body), None, None),
                Computation::Application(head, argument) => {
                    grafted(Node::Computation(head), Some(Node::Value(argument)), None)
                },
                Computation::Return(value) | Computation::Force(value) => {
                    grafted(Node::Value(value), None, None)
                },
                Computation::Bind(bound, body) => grafted(
                    Node::Computation(bound),
                    Some(Node::Computation(body)),
                    None,
                ),
                Computation::Case {
                    scrutinee,
                    ref branches,
                } => match **branches {
                    [on_left, on_right] => grafted(
                        Node::Value(scrutinee),
                        Some(Node::Computation(on_left)),
                        Some(Node::Computation(on_right)),
                    ),
                    _ => Former::Opaque,
                },
                _ => Former::Opaque,
            })
        },
    }
}

/// The compilation of one root: the shares it mints, by node, and the next
/// position of each.
struct Compiler<'run>
{
    /// The overlay the compilation mints into.
    overlay: &'run mut Overlay,
    /// The arena the input lives in.
    core: &'run CoreArena,
    /// The share of each node reached more than once, the outermost first.
    shares: BTreeMap<Node, usize>,
    /// The next position of each share, by share.
    next: Vec<u32>,
}

impl Compiler<'_>
{
    /// Count the parents of each node that `root` reaches through grafted
    /// formers, and list those nodes in the order the walk finishes them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each node reached once in the list, a node after every node
    ///   it holds; beside each, the count of its parent edges, the root's one.
    /// - provides: the shares and their order.
    /// - fails: [`CompileFault::Dangling`] for a node that names nothing;
    ///   [`CompileFault::Overflow`] past a counter.
    /// - panics: none.
    /// - executable: none — the clause is a relation over the whole walk.
    ///
    /// # Errors
    /// - [`CompileFault::Dangling`] — a reached node names nothing.
    /// - [`CompileFault::Overflow`] — a count passes its counter.
    ///
    /// # Termination
    /// - reason: the arena is acyclic, and each node is expanded once.
    /// - measure: the nodes not yet expanded, then the steps on the stack.
    fn counted(
        &self,
        root: Node,
    ) -> Result<(Vec<Node>, BTreeMap<Node, u32>), CompileFault>
    {
        let mut parents: BTreeMap<Node, u32> = BTreeMap::from([(root, 1_u32)]);
        let mut finished = Vec::new();
        let mut expanded = BTreeMap::new();
        let mut steps = Vec::from([Step::Enter(root)]);
        while let Some(step) = steps.pop() {
            match step {
                Step::Enter(node) => {
                    if expanded.insert(node, ()).is_some() {
                        continue;
                    }
                    steps.push(Step::Exit(node));
                    if let Former::Grafted { children } = former(self.core, node)? {
                        for child in children.into_iter().rev().flatten() {
                            let count = parents.entry(child).or_insert(0);
                            *count = count.checked_add(1).ok_or(CompileFault::Overflow)?;
                            steps.push(Step::Enter(child));
                        }
                    }
                },
                Step::Exit(node) => finished.push(node),
            }
        }
        Ok((finished, parents))
    }

    /// Mint `node` as an opaque leaf or as a graft over `children`, the
    /// overlay nodes of its children in the order the graft lists them.
    ///
    /// # Specification
    /// - requires: `children` are the compiled children of `node`, as
    ///   [`former`] lists them.
    /// - ensures: the overlay node of `node`: its graft over `children`, or an
    ///   opaque leaf holding it.
    /// - provides: the one mint of a compiled node.
    /// - fails: [`CompileFault::Overlay`] when the overlay refuses the mint;
    ///   [`CompileFault::MachineInvariant`] when a child is of another family
    ///   than its slot.
    /// - panics: none.
    /// - executable: none — the clause is the table the body states.
    ///
    /// # Errors
    /// - [`CompileFault::Overlay`] — the overlay refuses the mint.
    /// - [`CompileFault::Dangling`] — `node` names nothing.
    /// - [`CompileFault::MachineInvariant`] — a child is of another family.
    fn minted(
        &mut self,
        node: Node,
        children: &[OverlayId],
    ) -> Result<OverlayId, CompileFault>
    {
        let value = |at: usize| match children.get(at) {
            Some(&OverlayId::Value(id)) => Ok(id),
            _ => Err(CompileFault::MachineInvariant),
        };
        let computation = |at: usize| match children.get(at) {
            Some(&OverlayId::Computation(id)) => Ok(id),
            _ => Err(CompileFault::MachineInvariant),
        };
        let opaque = former(self.core, node)? == Former::Opaque;
        let minted = match node {
            Node::Value(id) if opaque => self
                .overlay
                .mint_value(ValueNode::Opaque(id))
                .map(OverlayId::Value),
            Node::Computation(id) if opaque => self
                .overlay
                .mint_computation(CompNode::Opaque(id))
                .map(OverlayId::Computation),
            Node::Value(id) => {
                let graft = match *self.core.value(id).ok_or(CompileFault::Dangling)? {
                    Value::Variable { zone, index } => ValueGraft::Variable { zone, index },
                    Value::Constant(index) => ValueGraft::Constant(index),
                    Value::Literal(ref literal) => ValueGraft::Literal(literal.clone()),
                    Value::Tuple(ref components) if components.is_empty() => ValueGraft::Unit,
                    Value::Tuple(_) => ValueGraft::Pair(value(0)?, value(1)?),
                    Value::Injection(summand, _) => {
                        let side = Side::try_from(summand)
                            .map_err(|_wide| CompileFault::MachineInvariant)?;
                        ValueGraft::Injection(side, value(0)?)
                    },
                    Value::Thunk(_) => ValueGraft::Thunk(computation(0)?),
                    Value::Lift { ref target, .. } => ValueGraft::Lift {
                        target: target.clone(),
                        body: value(0)?,
                    },
                    _ => return Err(CompileFault::MachineInvariant),
                };
                self.overlay
                    .mint_value(ValueNode::Grafted(graft))
                    .map(OverlayId::Value)
            },
            Node::Computation(id) => {
                let graft = match *self.core.computation(id).ok_or(CompileFault::Dangling)? {
                    Computation::Lambda(_) => CompGraft::Lambda(computation(0)?),
                    Computation::Application(..) => {
                        CompGraft::Application(computation(0)?, value(1)?)
                    },
                    Computation::Return(_) => CompGraft::Return(value(0)?),
                    Computation::Force(_) => CompGraft::Force(value(0)?),
                    Computation::Bind(..) => CompGraft::Bind(computation(0)?, computation(1)?),
                    Computation::Case { .. } => CompGraft::Case {
                        scrutinee: value(0)?,
                        on_left: computation(1)?,
                        on_right: computation(2)?,
                    },
                    _ => return Err(CompileFault::MachineInvariant),
                };
                self.overlay
                    .mint_computation(CompNode::Grafted(graft))
                    .map(OverlayId::Computation)
            },
        };
        minted.map_err(CompileFault::Overlay)
    }

    /// Mint an occurrence of share `share` in the family of `node`, standing
    /// under `open` shares.
    ///
    /// # Specification
    /// - requires: `share` is one of the `open` shares around the occurrence,
    ///   counted from the outermost.
    /// - ensures: a bound node at the distance from the innermost open share to
    ///   `share`, at the share's next position, which then moves on by one.
    /// - provides: each reach of a shared node.
    /// - fails: [`CompileFault::MachineInvariant`] when `share` is not open;
    ///   [`CompileFault::Overflow`] past a counter; [`CompileFault::Overlay`]
    ///   when the overlay refuses the mint.
    /// - panics: none.
    /// - executable: none — the position is state the walk threads.
    ///
    /// # Errors
    /// - [`CompileFault::MachineInvariant`] — `share` is not open.
    /// - [`CompileFault::Overflow`] — a counter passes its width.
    /// - [`CompileFault::Overlay`] — the overlay refuses the mint.
    fn occurrence(
        &mut self,
        node: Node,
        share: usize,
        open: usize,
    ) -> Result<OverlayId, CompileFault>
    {
        let distance = open
            .checked_sub(1)
            .and_then(|innermost| innermost.checked_sub(share))
            .ok_or(CompileFault::MachineInvariant)?;
        let distance = u32::try_from(distance).map_err(|_wide| CompileFault::Overflow)?;
        let next = self
            .next
            .get_mut(share)
            .ok_or(CompileFault::MachineInvariant)?;
        let position = *next;
        *next = next.checked_add(1).ok_or(CompileFault::Overflow)?;
        let bound = Bound {
            distance: ShareDistance::from(distance),
            position: SharePosition::from(position),
        };
        let minted = match node {
            Node::Value(_) => self
                .overlay
                .mint_value(ValueNode::Bound(bound))
                .map(OverlayId::Value),
            Node::Computation(_) => self
                .overlay
                .mint_computation(CompNode::Bound(bound))
                .map(OverlayId::Computation),
        };
        minted.map_err(CompileFault::Overlay)
    }

    /// Mint the tree that `root` stands for under `open` shares: each shared
    /// node below `root` an occurrence, each other node its overlay node.
    ///
    /// # Specification
    /// - requires: the shares of every shared node below `root` are among the
    ///   `open` shares around it.
    /// - ensures: the overlay node of `root`, `root` itself expanded even when
    ///   it is shared; each occurrence at the next position of its share, in
    ///   the preorder that validation reads.
    /// - provides: a leg, and the body below every share.
    /// - fails: as [`Compiler::minted`] and [`Compiler::occurrence`] fail.
    /// - panics: none.
    /// - executable: none — the positions are state the walk threads.
    ///
    /// # Errors
    /// As [`Compiler::minted`] and [`Compiler::occurrence`].
    ///
    /// # Termination
    /// - reason: the arena is acyclic, and the walk stops at each shared node
    ///   below `root` and at each opaque leaf.
    /// - measure: the steps on the stack, each a node of the finite tree.
    fn tree(
        &mut self,
        root: Node,
        open: usize,
    ) -> Result<OverlayId, CompileFault>
    {
        let mut results: Vec<OverlayId> = Vec::new();
        let mut steps = Vec::from([Step::Enter(root)]);
        let mut entered_root = false;
        while let Some(step) = steps.pop() {
            match step {
                Step::Enter(node) => {
                    let share = if entered_root {
                        self.shares.get(&node).copied()
                    }
                    else {
                        None
                    };
                    entered_root = true;
                    if let Some(share) = share {
                        let occurrence = self.occurrence(node, share, open)?;
                        results.push(occurrence);
                        continue;
                    }
                    match former(self.core, node)? {
                        Former::Leaf | Former::Opaque => {
                            let leaf = self.minted(node, &[])?;
                            results.push(leaf);
                        },
                        Former::Grafted { children } => {
                            steps.push(Step::Exit(node));
                            steps.extend(children.into_iter().rev().flatten().map(Step::Enter));
                        },
                    }
                },
                Step::Exit(node) => {
                    let Former::Grafted { children } = former(self.core, node)?
                    else {
                        return Err(CompileFault::MachineInvariant);
                    };
                    let arity = children.iter().flatten().count();
                    let first = results
                        .len()
                        .checked_sub(arity)
                        .ok_or(CompileFault::MachineInvariant)?;
                    let compiled: Vec<OverlayId> = results.drain(first ..).collect();
                    let graft = self.minted(node, &compiled)?;
                    results.push(graft);
                },
            }
        }
        match (results.pop(), results.is_empty()) {
            (Some(compiled), true) => Ok(compiled),
            _ => Err(CompileFault::MachineInvariant),
        }
    }

    /// Compile `root`: its shares in one chain, the outermost first, over its
    /// tree.
    ///
    /// # Specification
    /// - requires: `root` is a value or a computation.
    /// - ensures: the overlay root of `root`, in its family.
    /// - provides: the body of [`compile_value`] and [`compile_computation`].
    /// - fails: as [`Compiler::counted`] and [`Compiler::tree`] fail.
    /// - panics: none.
    /// - executable: none — the clause is the composition the body states.
    ///
    /// # Errors
    /// As [`Compiler::counted`] and [`Compiler::tree`].
    fn compiled(
        &mut self,
        root: Node,
    ) -> Result<OverlayId, CompileFault>
    {
        let (finished, parents) = self.counted(root)?;
        let shared: Vec<Node> = finished
            .into_iter()
            .filter(|node| parents.get(node).is_some_and(|&count| count > 1))
            .collect();
        self.shares = shared
            .iter()
            .enumerate()
            .map(|(share, &node)| (node, share))
            .collect();
        self.next = alloc::vec![0_u32; shared.len()];
        let mut legs = Vec::with_capacity(shared.len());
        for (share, &node) in shared.iter().enumerate() {
            legs.push(self.tree(node, share)?);
        }
        let mut body = self.tree(root, shared.len())?;
        for (share, leg) in legs.into_iter().enumerate().rev() {
            let arity =
                ShareArity::from(*self.next.get(share).ok_or(CompileFault::MachineInvariant)?);
            let minted = match body {
                OverlayId::Value(inner) => self
                    .overlay
                    .mint_value(ValueNode::Shared(Sharing {
                        arity,
                        leg,
                        body: inner,
                    }))
                    .map(OverlayId::Value),
                OverlayId::Computation(inner) => self
                    .overlay
                    .mint_computation(CompNode::Shared(Sharing {
                        arity,
                        leg,
                        body: inner,
                    }))
                    .map(OverlayId::Computation),
                OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                    return Err(CompileFault::MachineInvariant);
                },
            };
            body = minted.map_err(CompileFault::Overlay)?;
        }
        Ok(body)
    }
}

/// Compile a core value into an overlay root, with one share for each node it
/// reaches more than once.
///
/// # Specification
/// - requires: nothing; a node that names nothing is refused.
/// - ensures: on success a value root that validates and erases to `root`, node
///   for node, holding one share for each node that `root` reaches more than
///   once through grafted formers; on a refusal the overlay is at its entry
///   watermark.
/// - provides: the producer of shares for a side of the checker's path: the
///   overlay that a duplication stance evaluates.
/// - fails: [`CompileFault::Dangling`] for a node that names nothing;
///   [`CompileFault::Overlay`] when the overlay is full;
///   [`CompileFault::Overflow`] past a counter.
/// - panics: none.
///
/// # Errors
/// - [`CompileFault::Dangling`] — a reached node names nothing.
/// - [`CompileFault::Overlay`] — the overlay refuses a mint.
/// - [`CompileFault::Overflow`] — a count passes its counter.
///
/// # Adequacy
/// - hypothesis: L3 — the erasures of generated overlay roots, which share
///   their legs, compile back to roots that validate, erase to the same tree
///   and hold one share for each node reached twice; a hand-built pair of one
///   node holds one share of arity two. A compilation that drops a share,
///   misplaces a position or grafts a former erasure does not invert changes
///   those observations.
/// - witness: `tests::duplication::a_compiled_erasure_erases_to_itself`
/// - witness: `compile::tests::a_node_reached_twice_is_one_share_of_two_occurrences`
#[spec(
    captures: [entry = overlay.watermark()],
    ensures: |ret| ret.is_ok() || overlay.watermark() == entry,
)]
pub fn compile_value(
    overlay: &mut Overlay,
    core: &CoreArena,
    root: ValueId,
) -> Result<OverlayValueId, CompileFault>
{
    match compile(overlay, core, Node::Value(root))? {
        OverlayId::Value(compiled) => Ok(compiled),
        _ => Err(CompileFault::MachineInvariant),
    }
}

/// Compile a core computation into an overlay root, with one share for each
/// node it reaches more than once.
///
/// # Specification
/// - requires: as [`compile_value`].
/// - ensures: as [`compile_value`], for a computation root.
/// - provides: the computation half of the producer of shares.
/// - fails: as [`compile_value`] fails.
/// - panics: none.
///
/// # Errors
/// As [`compile_value`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`compile_value`], over generated computation roots.
/// - witness: `tests::duplication::a_compiled_erasure_erases_to_itself`
#[spec(
    captures: [entry = overlay.watermark()],
    ensures: |ret| ret.is_ok() || overlay.watermark() == entry,
)]
pub fn compile_computation(
    overlay: &mut Overlay,
    core: &CoreArena,
    root: ComputationId,
) -> Result<OverlayCompId, CompileFault>
{
    match compile(overlay, core, Node::Computation(root))? {
        OverlayId::Computation(compiled) => Ok(compiled),
        _ => Err(CompileFault::MachineInvariant),
    }
}

/// Compile `root`, and leave the overlay at its entry watermark on a refusal.
///
/// # Specification
/// trivial.
fn compile(
    overlay: &mut Overlay,
    core: &CoreArena,
    root: Node,
) -> Result<OverlayId, CompileFault>
{
    let entry = overlay.watermark();
    let mut compiler = Compiler {
        overlay,
        core,
        shares: BTreeMap::new(),
        next: Vec::new(),
    };
    let compiled = compiler.compiled(root);
    if compiled.is_err() {
        compiler.overlay.truncate_to(entry);
    }
    compiled
}

#[cfg(test)]
mod tests;
