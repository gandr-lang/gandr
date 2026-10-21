//! Sort inference for a model signature: the free sort variables of a clause
//! and the variables of a law, found by first-order unification over index
//! terms, and the telescope order they bind in.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec::Vec;

use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use super::Binder;
use super::ModelFault;
use super::ModelForm;
use super::Port;
use super::PresentedLaw;
use super::SortTerm;
use crate::resolve::OperandCount;

quenchant_shape::reason_enum! {
    /// Why a variable or a metavariable has no sort yet.
    pub mod unsorted {
        /// The reason no sort is known.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No occurrence of the variable has given it one.
            Unoccurred,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a metavariable has no solution.
    pub mod unsolved {
        /// The reason no solution is recorded.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No unification has met it against another node.
            Open,
        }
    }
}

/// The derived heads, by name: a sort's or an operation's telescope, or the
/// fault its derivation met.
///
/// # Specification
/// trivial.
pub(super) type Heads = BTreeMap<Name, Result<Head, ModelFault>>;

/// Whether a head is a sort or an operation.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum HeadKind
{
    /// A sort, applied in sort position.
    Sort,
    /// An operation, applied in term position.
    Operation,
}

/// A sort's or an operation's derived telescope: what an application of it
/// instantiates.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Head
{
    /// Sort or operation.
    kind: HeadKind,
    /// Every binder, implicit ones first.
    pub binders: Vec<Binder>,
    /// How many trailing binders an application writes.
    explicit: usize,
    /// An operation's result sorts over the binders; none for a sort.
    pub results: Vec<SortTerm>,
}

/// A node of the inference graph.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct NodeId(usize);

/// A metavariable: an implicit argument not yet determined.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct MetaId(usize);

/// A variable the source wrote, or one a port binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct VariableId(usize);

/// A term under inference.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Node
{
    /// A metavariable.
    Meta(MetaId),
    /// A variable.
    Variable(VariableId),
    /// An operation applied to every argument it binds.
    Apply(Name, Vec<NodeId>),
}

/// A sort under inference: a sort name over index nodes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Sorted
{
    /// The sort's name.
    sort: Name,
    /// Its index nodes, implicit ones first.
    indices: Vec<NodeId>,
}

/// A variable under inference.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Variable
{
    /// Its written name.
    name: Name,
    /// Its sort, once an occurrence gives it one.
    sort: Maybe<Sorted, unsorted::Absent>,
}

/// An item a telescope binds: a variable or an undetermined metavariable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Item
{
    /// A written variable.
    Variable(VariableId),
    /// A metavariable no unification determined.
    Meta(MetaId),
}

/// Whether a walk emits an item it reaches.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admission
{
    /// The item is bound where the walk reaches it.
    Bound,
    /// The item is bound later, or not by this walk.
    Deferred,
}

/// Whether a node contains a metavariable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Occurrence
{
    /// The metavariable occurs in the node.
    Contains,
    /// It does not.
    Free,
}

/// The inference state of one component: its graph, its variables, its
/// metavariables' sorts and solutions, and the scope written names resolve
/// in.
///
/// # Specification
/// trivial.
#[derive(Default)]
struct Engine
{
    /// Every node, by [`NodeId`].
    nodes: Vec<Node>,
    /// Every variable, by [`VariableId`].
    variables: Vec<Variable>,
    /// Each metavariable's sort, by [`MetaId`].
    metas: Vec<Sorted>,
    /// Each metavariable's solution, once unification finds one.
    solved: Vec<Maybe<NodeId, unsolved::Absent>>,
    /// Each application node's sort.
    applied: BTreeMap<NodeId, Sorted>,
    /// The written names in scope.
    scope: BTreeMap<Name, NodeId>,
}

/// An environment of instantiated binders: its place in a walk's table.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EnvId(usize);

/// How an elaboration walk reads a variable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode
{
    /// Through a derived head's binders, every name bound in the environment.
    Instance(EnvId),
    /// Through the engine's scope, an unbound name a fresh unsorted variable.
    Written,
}

/// A written application whose binders are instantiated one at a time.
///
/// # Specification
/// trivial.
struct Instantiation<'input>
{
    /// The head's name.
    name: &'input Name,
    /// Its derived telescope.
    head: &'input Head,
    /// The arguments the source wrote, in order.
    written: Vec<NodeId>,
    /// The binders instantiated so far, in order.
    arguments: Vec<NodeId>,
    /// The environment naming them.
    env: EnvId,
}

/// One pending step of an elaboration walk.
///
/// # Specification
/// trivial.
enum Task<'input>
{
    /// Elaborate a term, pushing its node.
    Read(TermNode<'input>, Mode),
    /// Apply the head of the kind to the nodes last pushed.
    Apply(&'input Name, HeadKind, OperandCount, Mode),
    /// Instantiate a sort term under the environment, pushing its sort.
    Sort(&'input SortTerm, EnvId),
    /// Gather the nodes last pushed as the named sort's indices.
    Gather(&'input Name, OperandCount),
    /// Instantiate the next binder of a written application, or finish it.
    Binder(Instantiation<'input>),
    /// Bind the next binder at the sort last pushed.
    Bound(Instantiation<'input>),
    /// Build the application, its result sort last pushed.
    Applied(&'input Name, Vec<NodeId>),
}

/// What an elaboration walk has built and not yet consumed.
///
/// # Specification
/// trivial.
#[derive(Default)]
struct Built
{
    /// Elaborated nodes, innermost last.
    nodes: Vec<NodeId>,
    /// Instantiated sorts, innermost last.
    sorts: Vec<Sorted>,
    /// Every environment the walk opened, by [`EnvId`].
    envs: Vec<BTreeMap<Name, NodeId>>,
}

impl Built
{
    /// The last `count` nodes pushed, in push order, removed.
    ///
    /// # Specification
    /// - ensures: `count` nodes, the stack shorter by them.
    /// - fails: [`ModelFault::Arity`] when fewer were pushed.
    /// - executable: none — the nodes are the stack's.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every application pops exactly its arguments.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    ///
    /// # Errors
    /// [`ModelFault::Arity`] when fewer than `count` nodes are pushed.
    fn take(
        &mut self,
        count: OperandCount,
    ) -> Result<Vec<NodeId>, ModelFault>
    {
        let start = self
            .nodes
            .len()
            .checked_sub(usize::from(count))
            .ok_or(ModelFault::Arity)?;
        Ok(self.nodes.drain(start ..).collect())
    }

    /// Open an environment binding `bindings`.
    ///
    /// # Specification
    /// trivial.
    fn open(
        &mut self,
        bindings: BTreeMap<Name, NodeId>,
    ) -> EnvId
    {
        self.envs.push(bindings);
        EnvId(self.envs.len().saturating_sub(1))
    }
}

impl Engine
{
    /// Add a node.
    ///
    /// # Specification
    /// trivial.
    fn node(
        &mut self,
        node: Node,
    ) -> NodeId
    {
        self.nodes.push(node);
        NodeId(self.nodes.len().saturating_sub(1))
    }

    /// A fresh metavariable of `sort`.
    ///
    /// # Specification
    /// trivial.
    fn meta(
        &mut self,
        sort: Sorted,
    ) -> NodeId
    {
        let meta = MetaId(self.metas.len());
        self.metas.push(sort);
        self.solved.push(Maybe::Absent(unsolved::Absent::Open));
        self.node(Node::Meta(meta))
    }

    /// A fresh variable named `name`, of `sort` when it is known.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        &mut self,
        name: Name,
        sort: Maybe<Sorted, unsorted::Absent>,
    ) -> NodeId
    {
        let variable = VariableId(self.variables.len());
        self.variables.push(Variable { name, sort });
        self.node(Node::Variable(variable))
    }

    /// `node` with every solved metavariable it stands for followed.
    ///
    /// # Specification
    /// - ensures: a node that is no solved metavariable.
    /// - executable: none — the chain followed is the solution table's.
    ///
    /// # Termination
    /// A solution is recorded only for a node the occurs check found free of
    /// the metavariable, so the chain visits each metavariable at most once,
    /// and the loop is bounded by their count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a law's implicit objects read back as the variables
    ///   their solutions name.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    fn resolve(
        &self,
        node: NodeId,
    ) -> NodeId
    {
        let mut current = node;
        for _step in 0 ..= self.solved.len() {
            let Some(&Node::Meta(meta)) = self.nodes.get(current.0)
            else {
                return current;
            };
            match self.solved.get(meta.0) {
                Some(&Maybe::Present(solution)) => current = solution,
                Some(&Maybe::Absent(_)) | None => return current,
            }
        }
        current
    }

    /// The sort of `node`, when one is known.
    ///
    /// # Specification
    /// trivial.
    fn sort_of(
        &self,
        node: NodeId,
    ) -> Maybe<Sorted, unsorted::Absent>
    {
        let resolved = self.resolve(node);
        let known = match self.nodes.get(resolved.0) {
            Some(&Node::Meta(meta)) => self.metas.get(meta.0).cloned(),
            Some(&Node::Variable(variable)) => {
                return self
                    .variables
                    .get(variable.0)
                    .map_or(Maybe::Absent(unsorted::Absent::Unoccurred), |known| {
                        known.sort.clone()
                    });
            },
            Some(&Node::Apply(..)) => self.applied.get(&resolved).cloned(),
            None => None,
        };
        known.map_or(Maybe::Absent(unsorted::Absent::Unoccurred), Maybe::Present)
    }

    /// Elaborate what a theory wrote as a node, through the scope.
    ///
    /// # Specification
    /// - ensures: each variable its node — the scope's, or for a name the scope
    ///   does not hold, a fresh unsorted variable the scope then holds; each
    ///   application the node of its operation applied to every argument it
    ///   binds, its implicit ones fresh metavariables, its written ones checked
    ///   against its binders' sorts, its sort recorded.
    /// - fails: as [`Self::run`].
    /// - executable: none — the node built is the term's image in the graph.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a law's sides elaborate to the operations' nodes and
    ///   sort as the derived heads instantiate.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::an_underivable_component_keeps_its_fault`
    ///
    /// # Errors
    /// The [`ModelFault`] of [`Self::run`].
    fn term(
        &mut self,
        heads: &Heads,
        term: &FreeTerm,
    ) -> Result<NodeId, ModelFault>
    {
        let mut built = Built::default();
        self.run(
            heads,
            Vec::from([Task::Read(term.to_node(), Mode::Written)]),
            &mut built,
        )?;
        built.nodes.pop().ok_or(ModelFault::UnknownHead)
    }

    /// Elaborate a written sort term: its sort applied to its indices.
    ///
    /// # Specification
    /// - ensures: the sort over every index it binds, the written ones
    ///   elaborated and checked against its index telescope.
    /// - fails: as [`Self::run`], the sort's name read as a sort head.
    /// - executable: none — as [`Self::term`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a port's sort instantiates its family's telescope,
    ///   the implicit indices fresh metavariables.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `model::tests::an_underivable_component_keeps_its_fault`
    ///
    /// # Errors
    /// The [`ModelFault`] of [`Self::run`].
    fn elaborate_sort(
        &mut self,
        heads: &Heads,
        sort: &SortTerm,
    ) -> Result<Sorted, ModelFault>
    {
        let mut pending = Vec::with_capacity(sort.indices.len().saturating_add(1));
        pending.push(Task::Apply(
            &sort.sort,
            HeadKind::Sort,
            OperandCount::from(sort.indices.len()),
            Mode::Written,
        ));
        pending.extend(
            sort.indices
                .iter()
                .rev()
                .map(|index| Task::Read(index.to_node(), Mode::Written)),
        );
        let mut built = Built::default();
        self.run(heads, pending, &mut built)?;
        built.sorts.pop().ok_or(ModelFault::UnknownHead)
    }

    /// Run an elaboration walk to completion: one explicit stack of tasks,
    /// each term, instantiation and sort a frame, so a head whose sorts name
    /// earlier operations instantiates without recursion.
    ///
    /// # Specification
    /// - ensures: every task's result pushed on `built`, in task order.
    /// - fails: the faults of [`Self::read`], [`Self::apply`], [`Self::next`]
    ///   and [`Self::bind`]; [`ModelFault::UnknownHead`] or
    ///   [`ModelFault::Inherited`] for a name no derived head of its kind
    ///   answers; [`ModelFault::Arity`] for fewer arguments than an application
    ///   names.
    /// - executable: none — the walk is the elaboration.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — operations, sorts and laws elaborate as the written
    ///   signature states them, and each fault is reported at its component.
    /// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::an_underivable_component_keeps_its_fault`
    ///
    /// # Errors
    /// The first [`ModelFault`] a task meets.
    ///
    /// # Termination
    /// Each task pops once. A read queues reads of its strict subterms; an
    /// instantiation queues one sort per binder of a finite telescope; a sort
    /// queues reads of a head derived strictly earlier, whose sorts name only
    /// heads derived before it, so the heads' order bounds the nesting.
    fn run<'input>(
        &mut self,
        heads: &'input Heads,
        mut pending: Vec<Task<'input>>,
        built: &mut Built,
    ) -> Result<(), ModelFault>
    {
        while let Some(task) = pending.pop() {
            match task {
                Task::Read(node, mode) => self.read(node, mode, &mut pending, built)?,
                Task::Apply(name, kind, count, mode) => {
                    let arguments = built.take(count)?;
                    let head = head_of(heads, kind, name)?;
                    Self::apply(name, head, arguments, mode, &mut pending, built)?;
                },
                Task::Sort(sort, env) => {
                    pending.push(Task::Gather(
                        &sort.sort,
                        OperandCount::from(sort.indices.len()),
                    ));
                    pending.extend(
                        sort.indices
                            .iter()
                            .rev()
                            .map(|index| Task::Read(index.to_node(), Mode::Instance(env))),
                    );
                },
                Task::Gather(name, count) => {
                    let indices = built.take(count)?;
                    built.sorts.push(Sorted {
                        sort: name.clone(),
                        indices,
                    });
                },
                Task::Binder(instantiation) => Self::next(instantiation, &mut pending, built)?,
                Task::Bound(instantiation) => {
                    self.bind(instantiation, &mut pending, built)?;
                },
                Task::Applied(name, arguments) => {
                    let sort = built.sorts.pop().ok_or(ModelFault::Unsorted)?;
                    let applied = self.node(Node::Apply(name.clone(), arguments));
                    let _first = self.applied.insert(applied, sort);
                    built.nodes.push(applied);
                },
            }
        }
        Ok(())
    }

    /// Read one term node: a variable's node pushed, an application's
    /// arguments and then its operation queued.
    ///
    /// # Specification
    /// - ensures: a variable pushes its node — under [`Mode::Instance`] the
    ///   environment's, under [`Mode::Written`] the scope's or a fresh one the
    ///   scope then holds; an application queues its operation after its
    ///   arguments, left to right.
    /// - fails: [`ModelFault::Constructor`] and [`ModelFault::ManyOut`] for a
    ///   constructor term or a results tuple; [`ModelFault::Binding`] for a
    ///   metavariable's instantiation, which only a second-order law writes;
    ///   [`ModelFault::UnknownHead`] for a name the environment does not bind.
    /// - executable: none — the node pushed is the variable's image.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a law's free names become its variables, a head's
    ///   binders its instantiation's arguments.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    ///
    /// # Errors
    /// The [`ModelFault`] the specification names.
    fn read<'input>(
        &mut self,
        node: TermNode<'input>,
        mode: Mode,
        pending: &mut Vec<Task<'input>>,
        built: &mut Built,
    ) -> Result<(), ModelFault>
    {
        match node.view() {
            TermView::Var(name) => {
                let bound = match mode {
                    Mode::Instance(env) => *built
                        .envs
                        .get(env.0)
                        .and_then(|bindings| bindings.get(name))
                        .ok_or(ModelFault::UnknownHead)?,
                    Mode::Written => {
                        if let Some(&bound) = self.scope.get(name) {
                            bound
                        }
                        else {
                            let fresh = self.variable(
                                name.clone(),
                                Maybe::Absent(unsorted::Absent::Unoccurred),
                            );
                            let _first = self.scope.insert(name.clone(), fresh);
                            fresh
                        }
                    },
                };
                built.nodes.push(bound);
            },
            TermView::Op { name, args } => {
                let arguments: Vec<TermNode<'input>> = args.collect();
                pending.push(Task::Apply(
                    name,
                    HeadKind::Operation,
                    OperandCount::from(arguments.len()),
                    mode,
                ));
                pending.extend(
                    arguments
                        .into_iter()
                        .rev()
                        .map(|argument| Task::Read(argument, mode)),
                );
            },
            TermView::Ctor { .. } => return Err(ModelFault::Constructor),
            TermView::Results { .. } => return Err(ModelFault::ManyOut),
            TermView::Inst { .. } => return Err(ModelFault::Binding),
            TermView::Abs { .. } => return Err(ModelFault::Abstraction),
        }
        Ok(())
    }

    /// Queue the application of `head` to `arguments`: under
    /// [`Mode::Instance`] they bind every binder and its result sort is
    /// instantiated over them; under [`Mode::Written`] they are the explicit
    /// ones and the binders are instantiated in order.
    ///
    /// # Specification
    /// - ensures: an instance's result queued over an environment binding each
    ///   binder to its argument; a written application's first binder queued
    ///   over an empty one.
    /// - fails: [`ModelFault::Arity`] for a count other than every binder's
    ///   (instance) or the explicit ones' (written); the faults of
    ///   [`Self::finish`].
    /// - executable: none — the tasks queued are the application's steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an implicit argument is solved from the explicit
    ///   ones' sorts, and an operation's result sort instantiates over them.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `model::tests::a_result_sort_indexed_by_an_operation_instantiates_at_each_use`
    ///
    /// # Errors
    /// The [`ModelFault`] the specification names.
    fn apply<'input>(
        name: &'input Name,
        head: &'input Head,
        arguments: Vec<NodeId>,
        mode: Mode,
        pending: &mut Vec<Task<'input>>,
        built: &mut Built,
    ) -> Result<(), ModelFault>
    {
        match mode {
            Mode::Instance(_) => {
                if arguments.len() != head.binders.len() {
                    return Err(ModelFault::Arity);
                }
                let bindings = head
                    .binders
                    .iter()
                    .map(|binder| binder.name.clone())
                    .zip(arguments.iter().copied())
                    .collect();
                let env = built.open(bindings);
                Self::finish(name, head, arguments, env, pending)
            },
            Mode::Written => {
                if arguments.len() != head.explicit {
                    return Err(ModelFault::Arity);
                }
                let env = built.open(BTreeMap::new());
                pending.push(Task::Binder(Instantiation {
                    name,
                    head,
                    written: arguments,
                    arguments: Vec::with_capacity(head.binders.len()),
                    env,
                }));
                Ok(())
            },
        }
    }

    /// Queue the next binder of a written application, or finish it once
    /// every binder is instantiated.
    ///
    /// # Specification
    /// - ensures: the next binder's sort queued before its binding; with none
    ///   left, a sort head's arguments pushed as its sort, an operation's
    ///   application finished.
    /// - fails: the faults of [`Self::finish`].
    /// - executable: none — the tasks queued are the instantiation's steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every binder is instantiated in telescope order, a
    ///   later binder's sort over the earlier ones.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    ///
    /// # Errors
    /// The [`ModelFault`] of [`Self::finish`].
    fn next<'input>(
        instantiation: Instantiation<'input>,
        pending: &mut Vec<Task<'input>>,
        built: &mut Built,
    ) -> Result<(), ModelFault>
    {
        let head = instantiation.head;
        if let Some(binder) = head.binders.get(instantiation.arguments.len()) {
            let env = instantiation.env;
            pending.push(Task::Bound(instantiation));
            pending.push(Task::Sort(&binder.sort, env));
            return Ok(());
        }
        match head.kind {
            HeadKind::Sort => {
                built.sorts.push(Sorted {
                    sort: instantiation.name.clone(),
                    indices: instantiation.arguments,
                });
                Ok(())
            },
            HeadKind::Operation => Self::finish(
                instantiation.name,
                head,
                instantiation.arguments,
                instantiation.env,
                pending,
            ),
        }
    }

    /// Bind the next binder of a written application at the sort last
    /// pushed: an implicit binder a fresh metavariable of it, an explicit one
    /// the next written argument checked against it.
    ///
    /// # Specification
    /// - ensures: the binder's argument appended and named in the environment,
    ///   the instantiation queued again.
    /// - fails: [`ModelFault::Arity`] for a written argument missing;
    ///   [`ModelFault::Unsorted`] for no sort pushed; the faults of
    ///   [`Self::expect`].
    /// - executable: none — the check is the unification.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a written argument of the wrong sort is refused, and
    ///   an implicit one is solved by the explicit ones' sorts.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::an_underivable_component_keeps_its_fault`
    ///
    /// # Errors
    /// The [`ModelFault`] the specification names.
    fn bind<'input>(
        &mut self,
        mut instantiation: Instantiation<'input>,
        pending: &mut Vec<Task<'input>>,
        built: &mut Built,
    ) -> Result<(), ModelFault>
    {
        let expected = built.sorts.pop().ok_or(ModelFault::Unsorted)?;
        let head = instantiation.head;
        let position = instantiation.arguments.len();
        let binder = head.binders.get(position).ok_or(ModelFault::Arity)?;
        let implicit = head.binders.len().saturating_sub(head.explicit);
        let argument = match position.checked_sub(implicit) {
            Some(written) => {
                let argument = *instantiation
                    .written
                    .get(written)
                    .ok_or(ModelFault::Arity)?;
                self.expect(argument, expected)?;
                argument
            },
            None => self.meta(expected),
        };
        if let Some(bindings) = built.envs.get_mut(instantiation.env.0) {
            let _first = bindings.insert(binder.name.clone(), argument);
        }
        instantiation.arguments.push(argument);
        pending.push(Task::Binder(instantiation));
        Ok(())
    }

    /// Queue an operation's application node over `arguments`, after its one
    /// result sort instantiated over `env`.
    ///
    /// # Specification
    /// - ensures: the result sort queued before the node that records it.
    /// - fails: [`ModelFault::ManyOut`] for an operation of several results.
    /// - executable: none — the tasks queued are the node's steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an application's sort is its operation's result over
    ///   its arguments.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    ///
    /// # Errors
    /// [`ModelFault::ManyOut`] for an operation of several results.
    fn finish<'input>(
        name: &'input Name,
        head: &'input Head,
        arguments: Vec<NodeId>,
        env: EnvId,
        pending: &mut Vec<Task<'input>>,
    ) -> Result<(), ModelFault>
    {
        let [ref result] = *head.results.as_slice()
        else {
            return Err(ModelFault::ManyOut);
        };
        pending.push(Task::Applied(name, arguments));
        pending.push(Task::Sort(result, env));
        Ok(())
    }

    /// Require `node` to inhabit `expected`: a variable of unknown sort takes
    /// it, any other node's sort is unified with it.
    ///
    /// # Specification
    /// - ensures: the node's sort and `expected` agree under the solutions
    ///   recorded.
    /// - fails: [`ModelFault::IllSorted`] when they cannot.
    /// - executable: none — agreement is the unification's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a free name takes the sort of its first port, and an
    ///   argument of another sort is refused.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `model::tests::an_underivable_component_keeps_its_fault`
    fn expect(
        &mut self,
        node: NodeId,
        expected: Sorted,
    ) -> Result<(), ModelFault>
    {
        let resolved = self.resolve(node);
        if let Some(&Node::Variable(variable)) = self.nodes.get(resolved.0)
            && let Some(entry) = self.variables.get_mut(variable.0)
            && let Maybe::Absent(_) = entry.sort
        {
            entry.sort = Maybe::Present(expected);
            return Ok(());
        }
        let Maybe::Present(actual) = self.sort_of(resolved)
        else {
            return Err(ModelFault::Unsorted);
        };
        self.unify_sorts(&expected, &actual)
    }

    /// Unify two sorts: equal names, then each index pair.
    ///
    /// # Specification
    /// - ensures: as [`Self::unify`] over the index pairs.
    /// - fails: [`ModelFault::IllSorted`] for distinct names or index counts.
    /// - executable: none — as [`Self::unify`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a law's two sides agree on one carrier sort.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::a_term_at_another_sort_or_inside_its_own_index_is_ill_sorted`
    fn unify_sorts(
        &mut self,
        first: &Sorted,
        second: &Sorted,
    ) -> Result<(), ModelFault>
    {
        if first.sort != second.sort || first.indices.len() != second.indices.len() {
            return Err(ModelFault::IllSorted);
        }
        self.unify(
            first
                .indices
                .iter()
                .copied()
                .zip(second.indices.iter().copied())
                .collect(),
        )
    }

    /// Unify every pair of `work`, one explicit worklist, solving a
    /// metavariable against the node it meets and unifying their sorts.
    ///
    /// # Specification
    /// - ensures: each pair resolves to one node under the solutions recorded,
    ///   and a solved metavariable's sort agrees with its solution's.
    /// - fails: [`ModelFault::IllSorted`] for two distinct variables, two
    ///   distinct operations, a variable against an application, or a
    ///   metavariable whose solution contains it.
    /// - executable: none — the solutions are the unifier.
    ///
    /// # Termination
    /// Each pair either closes, solves one of the finitely many unsolved
    /// metavariables, or replaces itself by the pairs of its arguments, nodes
    /// built strictly before it; a solved metavariable's sort pairs are
    /// nodes built before the metavariable.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `comp`'s middle object is solved by its arguments'
    ///   sorts, and two distinct variables do not unify.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::an_underivable_component_keeps_its_fault`
    /// - witness: `model::tests::a_result_sort_indexed_by_an_operation_instantiates_at_each_use`
    fn unify(
        &mut self,
        mut work: Vec<(NodeId, NodeId)>,
    ) -> Result<(), ModelFault>
    {
        while let Some((left, right)) = work.pop() {
            let (left, right) = (self.resolve(left), self.resolve(right));
            if left == right {
                continue;
            }
            let (Some(left_node), Some(right_node)) = (
                self.nodes.get(left.0).cloned(),
                self.nodes.get(right.0).cloned(),
            )
            else {
                return Err(ModelFault::IllSorted);
            };
            match (left_node, right_node) {
                (Node::Meta(meta), _) => self.solve(meta, right, &mut work)?,
                (_, Node::Meta(meta)) => self.solve(meta, left, &mut work)?,
                (Node::Apply(first, first_arguments), Node::Apply(second, second_arguments))
                    if first == second && first_arguments.len() == second_arguments.len() =>
                {
                    work.extend(first_arguments.into_iter().zip(second_arguments));
                },
                (Node::Variable(_) | Node::Apply(..), Node::Variable(_) | Node::Apply(..)) => {
                    return Err(ModelFault::IllSorted);
                },
            }
        }
        Ok(())
    }

    /// Solve `meta` as `solution`, after the occurs check, queueing the pairs
    /// of their sorts.
    ///
    /// # Specification
    /// - ensures: the metavariable resolves to `solution`; a variable of
    ///   unknown sort takes the metavariable's; otherwise their sorts' index
    ///   pairs join `work`.
    /// - fails: [`ModelFault::IllSorted`] when `solution` contains `meta`, or
    ///   their sorts' names differ.
    /// - executable: none — as [`Self::unify`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an implicit object solved by a morphism's sort reads
    ///   back as that sort's index.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    fn solve(
        &mut self,
        meta: MetaId,
        solution: NodeId,
        work: &mut Vec<(NodeId, NodeId)>,
    ) -> Result<(), ModelFault>
    {
        if self.occurs(meta, solution) == Occurrence::Contains {
            return Err(ModelFault::IllSorted);
        }
        let expected = self
            .metas
            .get(meta.0)
            .cloned()
            .ok_or(ModelFault::IllSorted)?;
        if let Some(slot) = self.solved.get_mut(meta.0) {
            *slot = Maybe::Present(solution);
        }
        if let Some(&Node::Variable(variable)) = self.nodes.get(solution.0)
            && let Some(entry) = self.variables.get_mut(variable.0)
            && let Maybe::Absent(_) = entry.sort
        {
            entry.sort = Maybe::Present(expected);
            return Ok(());
        }
        let Maybe::Present(actual) = self.sort_of(solution)
        else {
            return Err(ModelFault::Unsorted);
        };
        if expected.sort != actual.sort || expected.indices.len() != actual.indices.len() {
            return Err(ModelFault::IllSorted);
        }
        work.extend(expected.indices.into_iter().zip(actual.indices));
        Ok(())
    }

    /// Whether `node`, under the solutions recorded, contains `meta`.
    ///
    /// # Specification
    /// - ensures: [`Occurrence::Contains`] exactly when a walk of the resolved
    ///   node's arguments meets the unsolved metavariable.
    /// - executable: none — the walk is the containment.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — no `CatShape` solution contains its own metavariable,
    ///   so every implicit object is solved.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    /// - witness: `model::tests::a_term_at_another_sort_or_inside_its_own_index_is_ill_sorted`
    fn occurs(
        &self,
        meta: MetaId,
        node: NodeId,
    ) -> Occurrence
    {
        let mut pending = Vec::from([node]);
        let mut seen = BTreeSet::new();
        while let Some(current) = pending.pop() {
            let resolved = self.resolve(current);
            if !seen.insert(resolved) {
                continue;
            }
            match self.nodes.get(resolved.0) {
                Some(&Node::Meta(found)) if found == meta => return Occurrence::Contains,
                Some(&Node::Apply(_, ref arguments)) => pending.extend(arguments.iter().copied()),
                Some(&(Node::Meta(_) | Node::Variable(_))) | None => {},
            }
        }
        Occurrence::Free
    }

    /// The items a node mentions, under the solutions recorded, left to right.
    ///
    /// # Specification
    /// - ensures: one entry per variable or unsolved metavariable leaf, in
    ///   left-to-right order with repeats.
    /// - executable: none — the walk is the reading.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `comp`'s free objects are found in its ports' sorts.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    fn leaves(
        &self,
        node: NodeId,
    ) -> Vec<Item>
    {
        let mut pending = Vec::from([node]);
        let mut found = Vec::new();
        while let Some(current) = pending.pop() {
            match self.nodes.get(self.resolve(current).0) {
                Some(&Node::Meta(meta)) => found.push(Item::Meta(meta)),
                Some(&Node::Variable(variable)) => found.push(Item::Variable(variable)),
                Some(&Node::Apply(_, ref arguments)) => {
                    pending.extend(arguments.iter().rev().copied());
                },
                None => {},
            }
        }
        found
    }

    /// The sort of an item, when one is known.
    ///
    /// # Specification
    /// trivial.
    fn item_sort(
        &self,
        item: Item,
    ) -> Maybe<Sorted, unsorted::Absent>
    {
        let known = match item {
            Item::Variable(variable) => {
                return self
                    .variables
                    .get(variable.0)
                    .map_or(Maybe::Absent(unsorted::Absent::Unoccurred), |known| {
                        known.sort.clone()
                    });
            },
            Item::Meta(meta) => self.metas.get(meta.0).cloned(),
        };
        known.map_or(Maybe::Absent(unsorted::Absent::Unoccurred), Maybe::Present)
    }

    /// The items the sort of `item` mentions, left to right.
    ///
    /// # Specification
    /// trivial.
    fn sort_leaves(
        &self,
        item: Item,
    ) -> Vec<Item>
    {
        match self.item_sort(item) {
            Maybe::Present(sort) => sort
                .indices
                .iter()
                .flat_map(|&index| self.leaves(index))
                .collect(),
            Maybe::Absent(_) => Vec::new(),
        }
    }

    /// Append to `order` every item reachable from `roots` that `admit`
    /// binds, each after the items its sort mentions; `placed` holds the items
    /// of `order`.
    ///
    /// # Specification
    /// - requires: `placed` holds exactly the items of `order`.
    /// - ensures: each admitted item reached is appended once, after every
    ///   admitted item its sort mentions, in the order a left-to-right walk of
    ///   `roots` meets them; an item already in `order` is skipped. `placed`
    ///   still holds exactly the items of `order`.
    /// - executable: none — the order is the walk's.
    ///
    /// # Termination
    /// Each item is expanded at most once, and there are finitely many.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `comp` binds `a`, `b`, `c` before `f` and `g`, and
    ///   `assoc` binds the objects before the morphisms over them.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    fn emit(
        &self,
        roots: &[Item],
        admit: &dyn Fn(Item) -> Admission,
        order: &mut Vec<Item>,
        placed: &mut BTreeSet<Item>,
    )
    {
        /// One pending step of the walk.
        enum Step
        {
            /// Expand an item: its sort's items, then itself.
            Expand(Item),
            /// Emit an item whose sort's items are done.
            Finish(Item),
        }
        let mut expanded = BTreeSet::new();
        let mut pending: Vec<Step> = roots.iter().rev().map(|&item| Step::Expand(item)).collect();
        while let Some(step) = pending.pop() {
            match step {
                Step::Finish(item) => {
                    if admit(item) == Admission::Bound && placed.insert(item) {
                        order.push(item);
                    }
                },
                Step::Expand(item) => {
                    if !expanded.insert(item) {
                        continue;
                    }
                    pending.push(Step::Finish(item));
                    pending.extend(self.sort_leaves(item).into_iter().rev().map(Step::Expand));
                },
            }
        }
    }

    /// Read `node` back as a term, each item under the name `names` gives it.
    ///
    /// # Specification
    /// - ensures: each variable and unsolved metavariable its name, each
    ///   application its operation over its read-back arguments.
    /// - fails: [`ModelFault::Unsorted`] for an item no binder names.
    /// - executable: none — the term is the node's image.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `unitL`'s left side reads back with every implicit
    ///   argument written.
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    fn read_back(
        &self,
        node: NodeId,
        names: &BTreeMap<Item, Name>,
    ) -> Result<FreeTerm, ModelFault>
    {
        /// One pending step of a read-back.
        enum Back<'engine>
        {
            /// Read a node.
            Read(NodeId),
            /// Apply an operation to the last `count` terms read.
            Apply(&'engine Name, usize),
        }
        let mut pending = Vec::from([Back::Read(node)]);
        let mut built: Vec<FreeTerm> = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Back::Read(current) => {
                    let item = match self.nodes.get(self.resolve(current).0) {
                        Some(&Node::Meta(meta)) => Item::Meta(meta),
                        Some(&Node::Variable(variable)) => Item::Variable(variable),
                        Some(&Node::Apply(ref name, ref arguments)) => {
                            pending.push(Back::Apply(name, arguments.len()));
                            pending.extend(
                                arguments.iter().rev().map(|&argument| Back::Read(argument)),
                            );
                            continue;
                        },
                        None => return Err(ModelFault::Unsorted),
                    };
                    built.push(FreeTerm::var(names.get(&item).ok_or(ModelFault::Unsorted)?));
                },
                Back::Apply(name, count) => {
                    let start = built.len().checked_sub(count).ok_or(ModelFault::Unsorted)?;
                    let arguments: Vec<FreeTerm> = built.drain(start ..).collect();
                    built.push(FreeTerm::op(name, arguments));
                },
            }
        }
        built.pop().ok_or(ModelFault::Unsorted)
    }

    /// Read a sort back as a sort term.
    ///
    /// # Specification
    /// - ensures: the sort's name over each index read back.
    /// - fails: as [`Self::read_back`].
    /// - executable: none — as [`Self::read_back`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `comp`'s result reads back as `Hom(a, c)`.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    fn read_back_sort(
        &self,
        sort: &Sorted,
        names: &BTreeMap<Item, Name>,
    ) -> Result<SortTerm, ModelFault>
    {
        let mut indices = Vec::with_capacity(sort.indices.len());
        for &index in &sort.indices {
            indices.push(self.read_back(index, names)?);
        }
        Ok(SortTerm {
            sort: sort.sort.clone(),
            indices,
        })
    }

    /// Name every item of `order` — a written variable by its name, a
    /// metavariable by the first letter no written name takes — and read each
    /// one's sort back as its binder.
    ///
    /// # Specification
    /// - ensures: one binder per item, in order, each sort naming only the
    ///   binders before it.
    /// - fails: [`ModelFault::Unsorted`] for an item with no sort, or a sort
    ///   naming an item outside `order` or after it.
    /// - executable: none — the telescope is the order's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `comp`'s and `assoc`'s telescopes spell as the
    ///   written signature's.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
    fn telescope(
        &self,
        order: &[Item],
    ) -> Result<(Vec<Binder>, BTreeMap<Item, Name>), ModelFault>
    {
        let mut taken: BTreeSet<Name> = self
            .variables
            .iter()
            .map(|known| known.name.clone())
            .collect();
        let mut names: BTreeMap<Item, Name> = BTreeMap::new();
        let mut binders = Vec::with_capacity(order.len());
        for &item in order {
            let Maybe::Present(sort) = self.item_sort(item)
            else {
                return Err(ModelFault::Unsorted);
            };
            let bound = self.read_back_sort(&sort, &names)?;
            let name = match item {
                Item::Variable(variable) => self
                    .variables
                    .get(variable.0)
                    .map(|known| known.name.clone())
                    .ok_or(ModelFault::Unsorted)?,
                Item::Meta(_) => fresh(&taken),
            };
            let _fresh = taken.insert(name.clone());
            let _first = names.insert(item, name.clone());
            binders.push(Binder { name, sort: bound });
        }
        Ok((binders, names))
    }

    /// The item a resolved node is, when it is a variable or an unsolved
    /// metavariable.
    ///
    /// # Specification
    /// trivial.
    fn item(
        &self,
        node: NodeId,
    ) -> Maybe<Item, unsorted::Absent>
    {
        match self.nodes.get(self.resolve(node).0) {
            Some(&Node::Variable(variable)) => Maybe::Present(Item::Variable(variable)),
            Some(&Node::Meta(meta)) => Maybe::Present(Item::Meta(meta)),
            Some(&Node::Apply(..)) | None => Maybe::Absent(unsorted::Absent::Unoccurred),
        }
    }
}

/// The first name, `a` to `z` and then `x0`, `x1`, …, that `taken` does not
/// hold.
///
/// # Specification
/// - ensures: a name `taken` does not contain.
/// - executable: none — the candidates are tried in order until one is free,
///   which the finite `taken` guarantees.
///
/// # Termination
/// `taken` is finite, so some candidate past its size is free.
///
/// # Adequacy
/// - hypothesis: L2 — an implicit object no name was written for reads back as
///   the first letter its telescope leaves free.
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
/// - witness: `model::tests::an_implicit_object_past_the_last_free_letter_is_numbered`
fn fresh(taken: &BTreeSet<Name>) -> Name
{
    for letter in 'a' ..= 'z' {
        let candidate = Name::from(format!("{letter}"));
        if !taken.contains(&candidate) {
            return candidate;
        }
    }
    let mut suffix = 0_usize;
    for _step in 0 ..= taken.len() {
        let candidate = Name::from(format!("x{suffix}"));
        if !taken.contains(&candidate) {
            return candidate;
        }
        suffix = suffix.saturating_add(1);
    }
    Name::from(format!("x{suffix}"))
}

/// The derived head `name` names, of `kind`.
///
/// # Specification
/// - ensures: the head when `name` derived as one of `kind`.
/// - fails: [`ModelFault::Inherited`] for a head whose derivation failed;
///   [`ModelFault::UnknownHead`] for a name no head of `kind` answers.
/// - executable: none — the head is the table's.
///
/// # Adequacy
/// - hypothesis: L2 — a component naming a faulted operation inherits its
///   fault.
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
fn head_of<'heads>(
    heads: &'heads Heads,
    kind: HeadKind,
    name: &Name,
) -> Result<&'heads Head, ModelFault>
{
    match heads.get(name) {
        Some(&Ok(ref head)) if head.kind == kind => Ok(head),
        Some(&Err(_)) => Err(ModelFault::Inherited),
        Some(&Ok(_)) | None => Err(ModelFault::UnknownHead),
    }
}

/// Derive a sort's or an operation's head: its ports' and results' sorts
/// elaborated in order, every name a port does not bind a free sort variable
/// whose sort its occurrences infer, bound first.
///
/// # Specification
/// - ensures: the binders are the free sort variables, in the order a walk of
///   the ports' sorts and then the results' meets them, each after the ones its
///   sort mentions, then the ports in written order; `explicit` is the port
///   count; an operation's results read over the binders.
/// - fails: a [`ModelFault`] for a sort naming no earlier sort, an index of the
///   wrong sort, or a free variable no occurrence sorts.
/// - executable: none — the head is the inference.
///
/// # Adequacy
/// - hypothesis: L2 — `Ob`, `Hom`, `id` and `comp` derive the written
///   signature's telescopes.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
pub(super) fn derive_head(
    heads: &Heads,
    kind: HeadKind,
    ports: &[Port],
    outputs: &[Port],
) -> Result<Head, ModelFault>
{
    let mut engine = Engine::default();
    let mut explicit = Vec::with_capacity(ports.len());
    for port in ports {
        let sort = engine.elaborate_sort(heads, &port.sort)?;
        let bound = engine.variable(port.name.clone(), Maybe::Present(sort));
        let _shadowed = engine.scope.insert(port.name.clone(), bound);
        if let Maybe::Present(item) = engine.item(bound) {
            explicit.push(item);
        }
    }
    let mut results = Vec::with_capacity(outputs.len());
    for output in outputs {
        results.push(engine.elaborate_sort(heads, &output.sort)?);
    }
    let ported: BTreeSet<Item> = explicit.iter().copied().collect();
    let mut roots: Vec<Item> = explicit.clone();
    for result in &results {
        for &index in &result.indices {
            roots.extend(engine.leaves(index));
        }
    }
    let mut order = Vec::new();
    let mut placed = BTreeSet::new();
    engine.emit(
        &roots,
        &|item| {
            if ported.contains(&item) {
                Admission::Deferred
            }
            else {
                Admission::Bound
            }
        },
        &mut order,
        &mut placed,
    );
    order.extend(explicit);
    let (binders, names) = engine.telescope(&order)?;
    let mut read = Vec::with_capacity(results.len());
    for result in &results {
        read.push(engine.read_back_sort(result, &names)?);
    }

    Ok(Head {
        kind,
        binders,
        explicit: ports.len(),
        results: read,
    })
}

/// Derive a law: both terms elaborated, their sorts unified, and their
/// variables bound — those in another variable's sort first.
///
/// # Specification
/// - ensures: the telescope binds the variables some variable's sort mentions,
///   in the order a walk of the written variables of the left term and then the
///   right meets them, each after the ones its sort mentions, then any implicit
///   argument nothing determined, then the remaining variables in order of
///   first occurrence; the carrier is the terms' common sort.
/// - fails: a [`ModelFault`] for an ill-sorted term, a variable no occurrence
///   sorts, or a term naming a refused or undeclared head.
/// - executable: none — the law is the inference.
///
/// # Adequacy
/// - hypothesis: L2 — `unitL`, `unitR` and `assoc` derive the written laws, and
///   a law over a faulted operation keeps the inherited fault.
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
pub(super) fn derive_law(
    heads: &Heads,
    law: &PresentedLaw,
) -> Result<ModelForm, ModelFault>
{
    let mut engine = Engine::default();
    let left = engine.term(heads, &law.left)?;
    let right = engine.term(heads, &law.right)?;
    let carrier = match (engine.sort_of(left), engine.sort_of(right)) {
        (Maybe::Present(first), Maybe::Present(second)) => {
            engine.unify_sorts(&first, &second)?;
            first
        },
        (Maybe::Present(known), Maybe::Absent(_)) => {
            engine.expect(right, known.clone())?;
            known
        },
        (Maybe::Absent(_), Maybe::Present(known)) => {
            engine.expect(left, known.clone())?;
            known
        },
        (Maybe::Absent(_), Maybe::Absent(_)) => return Err(ModelFault::Unsorted),
    };
    let mut written: Vec<Item> = Vec::new();
    for name in law.left.to_node().vars().chain(law.right.to_node().vars()) {
        if let Some(&bound) = engine.scope.get(name)
            && let Maybe::Present(item) = engine.item(bound)
        {
            written.push(item);
        }
    }
    let mut indexing = BTreeSet::new();
    for variable in 0 .. engine.variables.len() {
        indexing.extend(engine.sort_leaves(Item::Variable(VariableId(variable))));
    }
    let mut order = Vec::new();
    let mut placed = BTreeSet::new();
    engine.emit(
        &written,
        &|item| {
            if indexing.contains(&item) {
                Admission::Bound
            }
            else {
                Admission::Deferred
            }
        },
        &mut order,
        &mut placed,
    );
    let mut implicit: Vec<Item> = engine.leaves(left);
    implicit.extend(engine.leaves(right));
    engine.emit(
        &implicit,
        &|item| match item {
            Item::Meta(_) => Admission::Bound,
            Item::Variable(_) => Admission::Deferred,
        },
        &mut order,
        &mut placed,
    );
    for item in written {
        if placed.insert(item) {
            order.push(item);
        }
    }
    let (telescope, names) = engine.telescope(&order)?;

    Ok(ModelForm::Law {
        telescope,
        carrier: engine.read_back_sort(&carrier, &names)?,
        left: engine.read_back(left, &names)?,
        right: engine.read_back(right, &names)?,
    })
}
