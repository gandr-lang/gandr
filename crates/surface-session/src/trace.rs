//! The trace layer: the tree of each judged declaration's judgement nodes,
//! folded from the steps of the checker's machine and kept by the
//! declaration's content key.
//!
//! # The fold rebuilds an item's tree at the end of the item
//!
//! **Choice.** [`Trace`] is the sink of the trace layer. Its [`TraceColumn`]
//! makes one [`StepBuffer`] of [`SLOTS`] steps the first time a pass asks,
//! and lends it to each incremental pass the job runs. The pass clears the
//! buffer before each item, so the buffer holds the steps of one item. At the
//! end of each item that the pass judges, the column folds the item's steps
//! into a [`DerivationTree`]: one [`DerivationNode`] for each goal, in the
//! order the machine met the goals, each at its depth. A node keeps the
//! goal's node and its type by their arena ids, the memo's mark, the cover,
//! the count of the nodes under it and itself, and the wall from its start to
//! its finish. An item that the pass adopts runs no judgement, and its key
//! keeps the tree it holds from before. The account keeps each tree beside
//! the program of the revision that judged it and the names of its
//! constants, so a face prints a goal and its type on demand at the width it
//! asks. The index stores no text.
//!
//! The kernel's replay of a declaration marks each node of its tree: a node
//! reads [`Warrant::Replayed`] while its row's kernel tier is
//! [`KernelTier::Replayed`].
//!
//! **Alternatives.** A fold at the end of the recheck holds the steps of each
//! item until then, so the buffer grows with the recheck and not with the
//! largest item. A record that held the rule's name would read the arena at
//! each step; [`Derivation::rule`] reads the node's former on demand. A tree
//! whose goals the fold spelled would store text that no face asked for.
//!
//! **Reversal.** When the kernel's replay marks single nodes (#6589), a node's
//! warrant reads its own mark and not the declaration's tier.
//!
//! # What it does not cover
//!
//! An item whose steps overflow the buffer keeps no tree, and its key says
//! so. A goal under binders is printed with the names of the constants and
//! with no names for the binders. A goal that the memo answered keeps no type
//! that its rule handed, because the machine hands the memo's answer and not
//! a rule's.
//!
//! # References
//!
//! - `engine-surface.md` § engine-surface-derivation (vault reference
//!   `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e`): the columns of a derivation
//!   node, which the index keeps, and the warrant that the kernel's replay
//!   gives a node.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::num::NonZeroUsize;

use gandr_core_checker::CoreNode;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::judged;
use gandr_core_checker::trace::Cover;
use gandr_core_checker::trace::Handed;
use gandr_core_checker::trace::Step;
use gandr_core_checker::trace::StepBuffer;
use gandr_core_checker::trace::unanswered;
use gandr_core_checker::trace::unkept;
use gandr_core_checker::trace::untraced;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Slots;
use gandr_core_incremental::Program;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_dispatcher::KernelTier;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Style;
use quenchant_shape::shape::Maybe;

use crate::account::KernelState;
use crate::instrument::Instrument;

quenchant_shape::reason_enum! {
    /// Why the index holds no tree for a declaration.
    pub mod underived {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The latest judged revision has no declaration of its own text
            /// with a content key at that position.
            Unkeyed,
            /// No judgement of the declaration's content ran at a sink that
            /// traces.
            Untraced,
            /// The steps of the declaration's judgement overflowed the
            /// buffer, so the fold built no tree.
            Overflowed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node's goal or type is not printed.
    pub mod unprinted {
        /// The reason none is printed.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node holds no type: a check whose rule handed no type, a
            /// formation, or a goal the memo answered by synthesis.
            Untyped,
            /// The printer refused the layout.
            Unpresentable,
        }
    }
}

/// How many steps the buffer of a [`TraceColumn`] holds: the steps of the
/// largest item the trace keeps a tree for.
pub const SLOTS: NonZeroUsize = NonZeroUsize::new(1_usize << 16_u32).expect("a nonzero count");

/// The depth of a node in its tree: zero at a root.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Depth(u32);

impl From<usize> for Depth
{
    /// The depth of a node with `above` goals under way above it, up to the
    /// representation's ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(above: usize) -> Self
    {
        Self(u32::try_from(above).unwrap_or(u32::MAX))
    }
}

impl From<Depth> for u32
{
    /// The depth as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: Depth) -> Self
    {
        depth.0
    }
}

/// How many nodes a node's subtree holds, the node included: the nodes the
/// check visited.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Visited(u32);

impl From<Visited> for u32
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(visited: Visited) -> Self
    {
        visited.0
    }
}

/// What the goal memo did for a node.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MemoMark
{
    /// The memo held the goal's answer.
    Hit,
    /// The memo keyed the goal and held no answer.
    Miss,
    /// The memo cannot key the goal.
    Unkeyed,
    /// The run's memo neither answers nor records.
    Closed,
}

/// The standing of a node.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Warrant
{
    /// The checker finished the node's goal.
    Checked,
    /// The checker finished the node's goal, and the kernel replayed the
    /// declaration.
    Replayed,
    /// A rule refused inside the node's goal.
    Refused,
}

/// One judgement node: a goal that the machine started, or one that the memo
/// answered.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DerivationNode
{
    /// The node the goal judges or forms.
    node: CoreNode,
    /// The type the node is checked against, or why it has none.
    against: Maybe<TypeNode, judged::Absent>,
    /// What the goal's rule handed, when it finished.
    handed: Option<Handed>,
    /// The depth in the tree.
    depth: Depth,
    /// What the memo did for the goal.
    memo: MemoMark,
    /// The binders the goal's memo key reads.
    cover: Cover,
    /// The nodes the subtree holds.
    visited: Visited,
    /// The clock when the goal started.
    started: Nanos,
    /// The clock when the goal finished, or when its run closed.
    finished: Nanos,
    /// Whether a rule refused inside the goal.
    refused: bool,
}

impl DerivationNode
{
    /// The node the goal judges or forms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(&self) -> CoreNode
    {
        self.node
    }

    /// The type the node is checked against: absent with
    /// [`judged::Absent::Synthesised`] for a synthesis, and with
    /// [`judged::Absent::Formed`] for a formation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn against(&self) -> Maybe<TypeNode, judged::Absent>
    {
        self.against
    }

    /// The depth in the tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn depth(&self) -> Depth
    {
        self.depth
    }

    /// What the memo did for the goal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn memo(&self) -> MemoMark
    {
        self.memo
    }

    /// The binders the goal's memo key reads: zero for a goal the memo
    /// cannot key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cover(&self) -> Cover
    {
        self.cover
    }

    /// The nodes the check visited: the node and each node under it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn visited(&self) -> Visited
    {
        self.visited
    }

    /// The wall of the goal, from its start to its finish.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn wall(&self) -> Nanos
    {
        Nanos::from(u64::from(self.finished).saturating_sub(u64::from(self.started)))
    }
}

/// The tree of one declaration's judgement nodes, in the order the machine
/// met them: each node is followed by the nodes under it, then by its
/// siblings.
///
/// # Specification
/// - requires: built by the fold of a [`TraceColumn`].
/// - ensures: the first node is at depth zero, and each node is at most one
///   deeper than the node before it; each node's count of visited nodes is one
///   more than the sum of its children's.
/// - provides: the nodes of the derivation pane, in its order.
/// - panics: none.
/// - executable: none — a data declaration; the fold builds it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Trace`].
/// - witness: `tests::trace::each_judged_declaration_keeps_the_tree_its_judgement_visited`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DerivationTree
{
    /// The nodes, in pre-order.
    nodes: Vec<DerivationNode>,
}

impl DerivationTree
{
    /// The nodes, in the order the machine met them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[DerivationNode]
    {
        &self.nodes
    }
}

/// A goal under way while the fold reads a run's steps.
#[derive(Clone, Copy, Debug)]
struct Open
{
    /// The node's place in the tree.
    at: usize,
    /// The height of the frame stack where the goal started.
    height: u32,
}

/// The column of the trace layer for one job: the buffer it lends each pass,
/// and the tree of each item that the job's passes judged.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry for each item that a pass judged while the column lent
///   its buffer, in the order the pass judged them.
/// - provides: the trees the account keys by each declaration's content.
/// - panics: none.
/// - executable: none — a column's state; [`Trace`] states its behaviour.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Trace`].
/// - witness: `tests::trace::each_judged_declaration_keeps_the_tree_its_judgement_visited`
#[derive(Clone, Debug)]
pub struct TraceColumn
{
    /// The buffer, while no pass holds it, once a pass asked for one.
    buffer: Option<StepBuffer>,
    /// The tree of each judged item, by its admission position.
    folded: Vec<(ConstantIndex, Maybe<DerivationTree, underived::Absent>)>,
    /// The goals under way, innermost last.
    open: Vec<Open>,
    /// The count of goals under way when each run under way opened,
    /// innermost last.
    runs: Vec<usize>,
}

impl Default for TraceColumn
{
    /// A column that has lent no buffer and folded nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            buffer: None,
            folded: Vec::new(),
            open: Vec::new(),
            runs: Vec::new(),
        }
    }
}

impl TraceColumn
{
    /// The buffer that a pass's runs write their steps into: the one the
    /// column holds, or a new one of [`SLOTS`] steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn lend(&mut self) -> StepBuffer
    {
        self.buffer.take().unwrap_or_else(|| {
            StepBuffer::new(Slots::from(SLOTS), gandr_surface_dispatcher::activity_clock)
        })
    }

    /// Take back `buffer`, which [`Self::lend`] lent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn restore(
        &mut self,
        buffer: StepBuffer,
    )
    {
        self.buffer = Some(buffer);
    }

    /// Take the tree of each item that the job's passes judged, by its
    /// admission position, in the order the passes judged them. The column
    /// then holds none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn take(&mut self)
    -> Vec<(ConstantIndex, Maybe<DerivationTree, underived::Absent>)>
    {
        core::mem::take(&mut self.folded)
    }

    /// Fold `buffer`, the steps of the item at `constant`, into the item's
    /// tree.
    ///
    /// # Specification
    /// - requires: `buffer` holds the steps of one item, from its first run's
    ///   opening.
    /// - ensures: the column's last entry is the item's: a tree with one node
    ///   for each started or answered step, in their order, or
    ///   [`underived::Absent::Overflowed`] when the buffer overflowed.
    /// - panics: none.
    /// - economy: one read of each step, and one push for each node; the stacks
    ///   of the goals and the runs under way keep their buffers across items.
    ///   The pass folds the items the edit reaches, and #4369 bounds them by
    ///   the edit.
    /// - executable: none — the tree is a projection of the steps, which a
    ///   predicate would fold again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Trace`].
    /// - witness: `tests::trace::each_judged_declaration_keeps_the_tree_its_judgement_visited`
    pub(crate) fn fold(
        &mut self,
        constant: ConstantIndex,
        buffer: &StepBuffer,
    )
    {
        let steps = match buffer.steps() {
            Maybe::Present(steps) => steps,
            Maybe::Absent(unkept::Absent::Overflowed) => {
                self.folded
                    .push((constant, Maybe::Absent(underived::Absent::Overflowed)));
                return;
            },
        };
        self.open.clear();
        self.runs.clear();
        let mut nodes: Vec<DerivationNode> = Vec::new();
        let mut last = Nanos::default();
        for &step in steps {
            match step {
                Step::Opened { clock } => {
                    last = clock;
                    self.runs.push(self.open.len());
                },
                Step::Started {
                    node,
                    against,
                    memo,
                    cover,
                    height,
                    clock,
                } => {
                    last = clock;
                    self.open.push(Open {
                        at: nodes.len(),
                        height: u32::from(height),
                    });
                    nodes.push(started(
                        (node, against),
                        match memo {
                            unanswered::Absent::Missed => MemoMark::Miss,
                            unanswered::Absent::Unkeyed => MemoMark::Unkeyed,
                            unanswered::Absent::Closed => MemoMark::Closed,
                        },
                        (cover, Depth::from(self.open.len().saturating_sub(1))),
                        clock,
                    ));
                },
                Step::Answered {
                    node,
                    against,
                    cover,
                    height: _,
                    clock,
                } => {
                    last = clock;
                    let mut answered = started(
                        (node, against),
                        MemoMark::Hit,
                        (cover, Depth::from(self.open.len())),
                        clock,
                    );
                    answered.visited = Visited(1);
                    nodes.push(answered);
                },
                Step::Finished {
                    handed,
                    height,
                    clock,
                } => {
                    last = clock;
                    let base = self.runs.last().copied().unwrap_or(0);
                    while self.open.len() > base
                        && self
                            .open
                            .last()
                            .is_some_and(|open| open.height >= u32::from(height))
                    {
                        if let Some(open) = self.open.pop() {
                            close(&mut nodes, open, clock, Some(handed));
                        }
                    }
                },
                Step::Refused { clock } => {
                    last = clock;
                    let base = self.runs.last().copied().unwrap_or(0);
                    if self.open.len() > base
                        && let Some(open) = self.open.last()
                        && let Some(node) = nodes.get_mut(open.at)
                    {
                        node.refused = true;
                    }
                },
                Step::Closed { clock } => {
                    last = clock;
                    let base = self.runs.pop().unwrap_or(0);
                    while self.open.len() > base {
                        if let Some(open) = self.open.pop() {
                            if let Some(node) = nodes.get_mut(open.at) {
                                node.refused = true;
                            }
                            close(&mut nodes, open, clock, None);
                        }
                    }
                },
            }
        }
        while let Some(open) = self.open.pop() {
            close(&mut nodes, open, last, None);
        }
        self.folded
            .push((constant, Maybe::Present(DerivationTree { nodes })));
    }
}

/// A node for a goal on `node` against `against`, which met `memo` with
/// `cover` at `depth` and started at `clock`; it visited itself and finished
/// where it started.
///
/// # Specification
/// trivial.
const fn started(
    (node, against): (CoreNode, Maybe<TypeNode, judged::Absent>),
    memo: MemoMark,
    (cover, depth): (Cover, Depth),
    clock: Nanos,
) -> DerivationNode
{
    DerivationNode {
        node,
        against,
        handed: None,
        depth,
        memo,
        cover,
        visited: Visited(1),
        started: clock,
        finished: clock,
        refused: false,
    }
}

/// Close the goal `open` of `nodes` at `clock`, which handed `handed`: it
/// visited each node pushed since it started.
///
/// # Specification
/// trivial.
fn close(
    nodes: &mut [DerivationNode],
    open: Open,
    clock: Nanos,
    handed: Option<Handed>,
)
{
    let visited = Visited(u32::try_from(nodes.len().saturating_sub(open.at)).unwrap_or(u32::MAX));
    if let Some(node) = nodes.get_mut(open.at) {
        node.visited = visited;
        node.finished = clock;
        node.handed = handed;
    }
}

/// What a face reads to print the goals of the trees one revision built: the
/// program the revision's pass judged and the names of its constants, by
/// admission position.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Printing
{
    /// The program whose arena each node's id names.
    program: Program,
    /// The name the printer writes for each constant, by admission position.
    names: Vec<String>,
}

/// A shared [`Printing`], equal to another only when both are the same
/// revision's.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Printed(Arc<Printing>);

impl Printed
{
    /// The printing of the revision that judged `program`, its constants
    /// named by `names`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn new(
        program: Program,
        names: Vec<String>,
    ) -> Self
    {
        Self(Arc::new(Printing { program, names }))
    }
}

impl PartialEq for Printed
{
    /// Whether both are the printing of one revision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Printed
{
}

/// What the account keeps for one declaration's content: its tree, or why it
/// has none, beside the printing of the revision that judged it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Derived
{
    /// The tree, or why the fold built none.
    tree: Maybe<DerivationTree, underived::Absent>,
    /// The printing of the revision that judged the declaration.
    printed: Printed,
}

impl Derived
{
    /// The tree `tree`, or why the fold built none, printed through
    /// `printed`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        tree: Maybe<DerivationTree, underived::Absent>,
        printed: Printed,
    ) -> Self
    {
        Self { tree, printed }
    }

    /// The derivation a face reads, under `kernel`, the kernel's standing on
    /// the declaration; or why the fold built no tree.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn read(
        &self,
        kernel: KernelState,
    ) -> Maybe<Derivation<'_>, underived::Absent>
    {
        match self.tree {
            Maybe::Present(ref tree) => Maybe::Present(Derivation {
                tree,
                printing: &self.printed.0,
                kernel,
            }),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// One declaration's derivation as a face reads it: the tree, the printing
/// of the revision that built it, and the kernel's standing on the
/// declaration.
///
/// # Specification
/// - requires: built by [`crate::Account::derivation_at`].
/// - ensures: the tree that the account keeps for the declaration's content
///   key, with the kernel tier of its row.
/// - provides: the nodes, their warrants, and their goals, types and rules
///   printed on demand.
/// - panics: none.
/// - executable: none — a borrow of the account's state.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Trace`].
/// - witness: `tests::trace::each_judged_declaration_keeps_the_tree_its_judgement_visited`
#[derive(Clone, Copy, Debug)]
pub struct Derivation<'account>
{
    /// The tree.
    tree: &'account DerivationTree,
    /// The printing of the revision that built it.
    printing: &'account Printing,
    /// The kernel's standing on the declaration.
    kernel: KernelState,
}

impl<'account> Derivation<'account>
{
    /// The nodes, in the order the machine met them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &'account [DerivationNode]
    {
        self.tree.nodes()
    }

    /// The standing of `node`: refused when a rule refused inside it, else
    /// replayed while the kernel's tier of the declaration is
    /// [`KernelTier::Replayed`], else checked.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn warrant(
        &self,
        node: &DerivationNode,
    ) -> Warrant
    {
        if node.refused {
            Warrant::Refused
        }
        else if matches!(self.kernel, KernelState::Settled(KernelTier::Replayed)) {
            Warrant::Replayed
        }
        else {
            Warrant::Checked
        }
    }

    /// The goal of `node`, printed at `page`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn goal(
        &self,
        node: &DerivationNode,
        page: PageWidth,
    ) -> Maybe<Presentation, unprinted::Absent>
    {
        let names = self.names();
        let source = CoreSource::new(self.printing.program.arena(), &names);
        let style = Style::from(Form::Sugared);
        let printed = match node.node {
            CoreNode::Term(TermNode::Value(id)) => gandr_surface_pretty::present_value(
                &source,
                gandr_surface_pretty::CoreNode::Value(id),
                page,
                style,
            ),
            CoreNode::Term(TermNode::Computation(id)) => gandr_surface_pretty::present_computation(
                &source,
                gandr_surface_pretty::CoreNode::Computation(id),
                page,
                style,
            ),
            CoreNode::Type(ty) => {
                gandr_surface_pretty::present_type(&source, printed(ty), page, style)
            },
        };
        printed.map_or(
            Maybe::Absent(unprinted::Absent::Unpresentable),
            Maybe::Present,
        )
    }

    /// The type of `node`, printed at `page`: the type it is checked against,
    /// or the type its rule synthesised.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn ty(
        &self,
        node: &DerivationNode,
        page: PageWidth,
    ) -> Maybe<Presentation, unprinted::Absent>
    {
        let ty = match (node.against, node.handed) {
            (Maybe::Present(ty), _) => printed(ty),
            (Maybe::Absent(_), Some(Handed::Value(ty))) => {
                gandr_surface_pretty::CoreNode::ValueType(ty.node())
            },
            (Maybe::Absent(_), Some(Handed::Computation(ty))) => {
                gandr_surface_pretty::CoreNode::CompType(ty)
            },
            (Maybe::Absent(_), Some(Handed::Checked) | None) => {
                return Maybe::Absent(unprinted::Absent::Untyped);
            },
        };
        let names = self.names();
        let source = CoreSource::new(self.printing.program.arena(), &names);
        gandr_surface_pretty::present_type(&source, ty, page, Style::from(Form::Sugared)).map_or(
            Maybe::Absent(unprinted::Absent::Unpresentable),
            Maybe::Present,
        )
    }

    /// The short name of the rule that judged `node`: the name of the node's
    /// former, or `form` for a formation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rule(
        &self,
        node: &DerivationNode,
    ) -> Rule
    {
        let arena = self.printing.program.arena();
        let spelled = match node.node {
            CoreNode::Term(TermNode::Value(id)) => {
                arena.value(id).map(|value| alloc::format!("{value:?}"))
            },
            CoreNode::Term(TermNode::Computation(id)) => arena
                .computation(id)
                .map(|computation| alloc::format!("{computation:?}")),
            CoreNode::Type(_) => Some(String::from("form")),
        };
        let mut name = spelled.unwrap_or_default();
        let end = name
            .find(|character: char| !character.is_alphanumeric())
            .unwrap_or(name.len());
        name.truncate(end);
        Rule(name)
    }

    /// The constants' names as the printer reads them.
    ///
    /// # Specification
    /// trivial.
    fn names(&self) -> Vec<Name<'account>>
    {
        self.printing
            .names
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect()
    }
}

/// The printer's node for the type node `ty`.
///
/// # Specification
/// trivial.
const fn printed(ty: TypeNode) -> gandr_surface_pretty::CoreNode
{
    match ty {
        TypeNode::Value(id) => gandr_surface_pretty::CoreNode::ValueType(id),
        TypeNode::Computation(id) => gandr_surface_pretty::CoreNode::CompType(id),
    }
}

/// The short name of a rule, as [`Derivation::rule`] reads it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rule(String);

impl AsRef<str> for Rule
{
    /// The name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// The sink of the trace layer: it lends each incremental pass a buffer of
/// steps, and folds each item the pass judges into its tree.
///
/// # Specification
/// - requires: nothing.
/// - ensures: after a recheck at this sink, each declaration that the judgement
///   judged holds the tree of its goals in the account, and each declaration
///   that it adopted keeps the tree its key held.
/// - provides: the trace layer of the instrument.
/// - panics: none.
/// - executable: none — a sink; its effects are the account's trees.
///
/// # Adequacy
/// - hypothesis: L3 — a recheck of a corpus source at this sink keeps, for each
///   declaration, a tree whose memo marks count the hits and the misses the
///   counts layer counts; the tree's nodes nest in the order the machine met
///   them, and each node is replayed once the admission replays the
///   declaration. A second recheck of the same text keeps each tree.
/// - witness: `tests::trace::each_judged_declaration_keeps_the_tree_its_judgement_visited`
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Trace
{
    /// The column of the job.
    column: TraceColumn,
}

impl Instrument for Trace
{
    /// The column that folds each judged item's steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn trace(&mut self) -> Maybe<&mut TraceColumn, untraced::Absent>
    {
        Maybe::Present(&mut self.column)
    }
}
