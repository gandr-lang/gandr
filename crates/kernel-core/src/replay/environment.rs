//! The environments a weak-head reduction reads its binders in, in place of
//! the substitutions it would otherwise walk.
//!
//! [`super::Replay::whnf`] holds its focus and each frame's argument or
//! continuation as a [`Closure`]: a node with the [`Environment`] its free
//! binders are read in. An environment is a linked list of cells in the
//! [`Environments`] store the reduction owns, the innermost binder's first,
//! and each cell holds a value as a closure of its own. A β-step, a bind's
//! continuation, a case's payload, a split's components, a fold's head and
//! tail, a fixpoint's self-reference and an endpoint's read-through push a
//! cell where the substituting reduction walked the reduct.
//!
//! The unload reads a closure back as the term the substituting reduction
//! holds at the same step. It closes each cell the node reads, once however
//! often it occurs, and substitutes them in one walk
//! ([`crate::rewrite::unload_computation`]). A cell holding a variable its own
//! environment binds is an alias of that binder's cell, so a read takes one
//! hop and an alias closes as its cell does.
//!
//! The alias is how the reduction keeps practical values. It never
//! substitutes a variable for a variable. A pushed variable that its own
//! environment binds becomes an alias of the cell holding that binder's value,
//! and that cell never holds another alias. A chain of variables bound to
//! variables thus aliases its first cell at every link. Each read takes at
//! most one hop, so the reads stay linear in the β-steps.
//!
//! # References
//!
//! - `vault:01a183de-4ab1-7660-a88a-04b9e8d318e3` — exemplar: Accattoli's
//!   habilitation, § 3.9, the value of variables. Practical values disable the
//!   substitution of a variable for a variable. The substitution steps then
//!   stay linear in the β-steps, not quadratic.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;

use super::Frame;
use crate::encoding::ContentTable;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value_type;
use crate::rewrite::unload_computation;
use crate::rewrite::unload_value;

/// The arena, content table and memo the rewrites an unload runs mint into.
pub(super) type Machine<'run> = (
    &'run mut TermArena,
    &'run mut ContentTable,
    &'run mut NullMemo,
);

/// A node with the environment its free binders are read in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Closure<Node>
{
    /// The node.
    pub node: Node,
    /// The environment its innermost free binders are read in; a free index
    /// past it reads a binder of the context the reduction was handed.
    pub environment: Environment,
}

impl<Node> Closure<Node>
where
    Node: Copy,
{
    /// `node` read in the empty environment, as the reduction was handed it.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn closed(node: Node) -> Self
    {
        Self {
            node,
            environment: Environment::EMPTY,
        }
    }

    /// `node` read in this closure's environment.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn with<Other>(
        self,
        node: Other,
    ) -> Closure<Other>
    where
        Other: Copy,
    {
        Closure {
            node,
            environment: self.environment,
        }
    }
}

/// The values a reduction's innermost binders stand for: the innermost
/// binder's cell in an [`Environments`] store, or none.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub(super) struct Environment(Option<CellIndex>);

impl Environment
{
    /// The environment of no binder.
    pub(super) const EMPTY: Self = Self(None);
}

/// A cell's position in its store, in the order the reduction pushed it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct CellIndex(usize);

/// What a cell holds for its binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Held
{
    /// A value, read in its environment, which binds no variable the value
    /// is.
    Value(Closure<ValueId>),
    /// The value another cell holds: the one a pushed variable named.
    Alias(CellIndex),
}

/// One binder's cell.
#[derive(Clone, Copy, Debug)]
struct Cell
{
    /// What the binder stands for.
    held: Held,
    /// The binders outside this one.
    outer: Environment,
    /// How many binders this cell and those outside it stand for.
    width: BinderDepth,
    /// The held value read back outside every binder, once an unload closed
    /// it.
    closed: Option<ValueId>,
}

/// The cells one reduction pushed, oldest first, and the folds it rebuilt to
/// read their list as the innermost binder.
#[derive(Debug, Default)]
pub(super) struct Environments
{
    /// Every cell, each pushed after the cells its environments name.
    cells: Vec<Cell>,
    /// Each fold rebuilt over the innermost binder, by the fold it came from;
    /// a rebuilt fold maps to itself.
    rebuilt: BTreeMap<ComputationId, ComputationId>,
}

impl Environments
{
    /// `outer` with a binder standing for `value` innermost.
    ///
    /// # Specification
    /// - requires: `value`'s environment is this store's.
    /// - ensures: an environment one binder wider than `outer`, whose innermost
    ///   binder reads as `value` reads ([`Self::resolve`]); a value that is a
    ///   variable its own environment binds is held as an alias of that
    ///   binder's cell, and a value read in the empty environment is already
    ///   closed.
    /// - provides: the push each instantiation site makes in place of a
    ///   substitution.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reduction whose arguments are variables of the
    ///   reduction's own binders reads them as the substituting reduction does,
    ///   through one alias each.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    /// - witness: `replay::environment::tests::a_chain_of_variables_aliases_the_cell_that_holds_its_value`
    #[spec(
        captures: before = self.cells.len(),
        ensures: |ret| self.cells.len() == before.saturating_add(1) && ret != Environment::EMPTY,
    )]
    pub(super) fn push(
        &mut self,
        arena: &TermArena,
        outer: Environment,
        value: Closure<ValueId>,
    ) -> Environment
    {
        let (held, closed) = match self.bound(arena, value) {
            Some(cell) => (Held::Alias(cell), None),
            None if value.environment == Environment::EMPTY => {
                (Held::Value(value), Some(value.node))
            },
            None => (Held::Value(value), None),
        };
        let width = self.width(outer).deeper();
        let index = CellIndex(self.cells.len());
        self.cells.push(Cell {
            held,
            outer,
            width,
            closed,
        });
        Environment(Some(index))
    }

    /// The value `value` reads as: the value its variable's binder holds, or
    /// itself.
    ///
    /// # Specification
    /// - requires: `value`'s environment is this store's.
    /// - ensures: the closure the cell of `value`'s variable holds when its
    ///   environment binds that variable, read through an alias; `value` itself
    ///   otherwise. The result is never a variable its own environment binds.
    /// - provides: the scrutinee a reduction rule inspects, as the substituting
    ///   reduction finds it substituted.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — "never a bound variable" holds by every cell's
    ///   construction ([`Self::push`]), which a predicate over one call would
    ///   restate by walking the store.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every rule inspecting a value bound by a β-step, a
    ///   case or a split finds the constructor the substituting reduction
    ///   finds.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    pub(super) fn resolve(
        &self,
        arena: &TermArena,
        value: Closure<ValueId>,
    ) -> Closure<ValueId>
    {
        match self
            .bound(arena, value)
            .and_then(|cell| self.cells.get(cell.0))
        {
            Some(&Cell {
                held: Held::Value(held),
                ..
            }) => held,
            Some(&Cell {
                held: Held::Alias(_),
                ..
            })
            | None => value,
        }
    }

    /// The cell holding the value of `value`'s variable, through an alias,
    /// when `value`'s environment binds it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a cell holding a value, never an alias, exactly when `value`
    ///   is a variable below its environment's width.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the cell's binder is found by walking the
    ///   environment's links, which a predicate would walk again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arguments that are variables of the reduction's own
    ///   binders, several deep, read through one alias each as the substituting
    ///   reduction reads them.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    /// - witness: `replay::environment::tests::a_chain_of_variables_aliases_the_cell_that_holds_its_value`
    fn bound(
        &self,
        arena: &TermArena,
        value: Closure<ValueId>,
    ) -> Option<CellIndex>
    {
        let Some(&Value::Variable(index)) = arena.value(value.node)
        else {
            return None;
        };
        let cell = self.cell_at(value.environment, index)?;
        match self.cells.get(cell.0)?.held {
            Held::Value(_) => Some(cell),
            Held::Alias(target) => Some(target),
        }
    }

    /// The cell of the binder `index` places out in `environment`.
    ///
    /// # Specification
    /// trivial.
    fn cell_at(
        &self,
        environment: Environment,
        index: DeBruijnIndex,
    ) -> Option<CellIndex>
    {
        let mut current = environment.0?;
        for _outward in 0 .. u32::from(index) {
            current = self.cells.get(current.0)?.outer.0?;
        }
        Some(current)
    }

    /// How many binders `environment` stands for.
    ///
    /// # Specification
    /// trivial.
    fn width(
        &self,
        environment: Environment,
    ) -> BinderDepth
    {
        environment
            .0
            .and_then(|cell| self.cells.get(cell.0))
            .map_or(BinderDepth::NONE, |cell| cell.width)
    }

    /// `environment` without its innermost binder.
    ///
    /// # Specification
    /// trivial.
    fn outer(
        &self,
        environment: Environment,
    ) -> Environment
    {
        environment
            .0
            .and_then(|cell| self.cells.get(cell.0))
            .map_or(Environment::EMPTY, |cell| cell.outer)
    }

    /// The fold `fold`'s next turn over `tail`: the fold over the tail, read
    /// where the fold is.
    ///
    /// A tail read in the fold's own environment is the fold's list as it
    /// stands. A tail read elsewhere becomes the innermost binder of a fold
    /// rebuilt once to read its list there, its other parts raised past it;
    /// a rebuilt fold's own turns replace that binder.
    ///
    /// # Specification
    /// - requires: `fold` is a list fold read in this store, and `tail` the
    ///   tail of the cell its list reads as.
    /// - ensures: a list fold whose list reads as `tail` and whose other parts
    ///   read as `fold`'s; it unloads to the fold the substituting reduction
    ///   builds over the tail.
    /// - provides: a fold's tail without a walk of its branches at each turn.
    /// - fails: `None` when `fold` is no list fold.
    /// - panics: none.
    /// - executable: none — "reads as" is the unload's, which a predicate would
    ///   run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold over a list a function receives turns over
    ///   every cell and unloads to the substituting reduction's fold.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    pub(super) fn fold_over(
        &mut self,
        (arena, table, memo): Machine<'_>,
        fold: Closure<ComputationId>,
        tail: Closure<ValueId>,
    ) -> Option<Closure<ComputationId>>
    {
        if self.rebuilt.get(&fold.node) == Some(&fold.node) {
            let outer = self.outer(fold.environment);
            return Some(Closure {
                node: fold.node,
                environment: self.push(arena, outer, tail),
            });
        }
        let &Computation::ListFold {
            element,
            result,
            on_nil,
            on_cons,
            ..
        } = arena.computation(fold.node)?
        else {
            return None;
        };
        if tail.environment == fold.environment {
            return Some(
                fold.with(arena.computation_list_fold(element, result, tail.node, on_nil, on_cons)),
            );
        }
        let rebuilt = if let Some(&rebuilt) = self.rebuilt.get(&fold.node) {
            rebuilt
        }
        else {
            let past = BinderDepth::NONE.deeper();
            let element = shift_value_type(arena, table, memo, element, BinderDepth::NONE, past);
            let result = shift_value_type(arena, table, memo, result, BinderDepth::NONE, past);
            let on_nil = shift_computation(arena, table, memo, on_nil, BinderDepth::NONE, past);
            // The cell branch binds the head outside the folded result: its
            // own two binders stand inside the tail's and stay put.
            let own = past.deeper();
            let on_cons = shift_computation(arena, table, memo, on_cons, own, past);
            let list = arena.value_variable(DeBruijnIndex::from(0_u32));
            let rebuilt = arena.computation_list_fold(element, result, list, on_nil, on_cons);
            self.rebuilt.insert(fold.node, rebuilt);
            self.rebuilt.insert(rebuilt, rebuilt);
            rebuilt
        };
        Some(Closure {
            node: rebuilt,
            environment: self.push(arena, fold.environment, tail),
        })
    }

    /// `computation` read back outside every binder of its environment, the
    /// `depth` innermost binders inside it kept.
    ///
    /// # Specification
    /// - requires: `computation`'s environment is this store's.
    /// - ensures: the term the substituting reduction holds where this closure
    ///   stands: each binder the node reads replaced by its cell's closed
    ///   value, every index past the environment lowered by its width; the node
    ///   itself when it reads no binder at or past `depth`.
    /// - provides: the unload at a weak head and before every closed-term
    ///   helper.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — "the term the substituting reduction holds" is a
    ///   relation between two reductions, observed by the property witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the environment reduction's weak heads are α-equal to
    ///   the substituting reduction's, and reads under a bind's own binder stay
    ///   bound.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    pub(super) fn unload_computation(
        &mut self,
        (arena, table, memo): Machine<'_>,
        computation: Closure<ComputationId>,
        depth: BinderDepth,
    ) -> ComputationId
    {
        let reads = BinderDepth::from(u32::from(
            arena.computation_support(computation.node).depth(),
        ));
        let Some(read) = self.read(computation.environment, reads, depth)
        else {
            return computation.node;
        };
        self.close((arena, table, memo), computation.environment, read);
        let (environment, width) = self.substitution(arena, computation.environment, read);
        unload_computation(
            arena,
            table,
            memo,
            (computation.node, environment),
            (width, depth),
        )
    }

    /// `value` read back outside every binder of its environment.
    ///
    /// # Specification
    /// - requires: as [`Self::unload_computation`].
    /// - ensures: as [`Self::unload_computation`] at depth zero, over a value.
    /// - provides: an application frame's argument read back.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::unload_computation`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::unload_computation`].
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    pub(super) fn unload_value(
        &mut self,
        (arena, table, memo): Machine<'_>,
        value: Closure<ValueId>,
    ) -> ValueId
    {
        let reads = BinderDepth::from(u32::from(arena.value_support(value.node).depth()));
        let Some(read) = self.read(value.environment, reads, BinderDepth::NONE)
        else {
            return value.node;
        };
        self.close((arena, table, memo), value.environment, read);
        let (environment, width) = self.substitution(arena, value.environment, read);
        unload_value(arena, table, memo, (value.node, environment), width)
    }

    /// `frame` read back outside every binder of its environment: an
    /// application's argument, or a bind's continuation under its own binder.
    ///
    /// # Specification
    /// - requires: as [`Self::unload_computation`].
    /// - ensures: the frame of the same kind over the unloaded argument or
    ///   continuation; a projection as it is.
    /// - provides: the head path rebuilt at a weak head.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::unload_computation`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a weak head under application and bind frames read in
    ///   environments rebuilds as the substituting reduction's.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    pub(super) fn unload_frame(
        &mut self,
        (arena, table, memo): Machine<'_>,
        frame: Closure<Frame>,
    ) -> Frame
    {
        match frame.node {
            Frame::Apply(argument) => {
                Frame::Apply(self.unload_value((arena, table, memo), frame.with(argument)))
            },
            Frame::Bind(body) => Frame::Bind(self.unload_computation(
                (arena, table, memo),
                frame.with(body),
                BinderDepth::NONE.deeper(),
            )),
            Frame::Project(component) => Frame::Project(component),
        }
    }

    /// How many of `environment`'s innermost binders a node whose support
    /// reaches `reads` may read past `depth` kept binders, when the node
    /// reads past them at all.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &self,
        environment: Environment,
        reads: BinderDepth,
        depth: BinderDepth,
    ) -> Option<BinderDepth>
    {
        let width = self.width(environment);
        if width == BinderDepth::NONE {
            return None;
        }
        let past = u32::from(reads)
            .checked_sub(u32::from(depth))
            .filter(|&past| past > 0)?;
        Some(BinderDepth::from(past.min(u32::from(width))))
    }

    /// Close every cell among `environment`'s `read` innermost binders, and
    /// first every cell each of them reads.
    ///
    /// # Specification
    /// - requires: `environment` is this store's.
    /// - ensures: each of those cells, through an alias, holds its value read
    ///   back outside every binder; a cell is closed once.
    /// - provides: the closed values an unload substitutes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the closed values are rewrites, which a predicate
    ///   would run again.
    ///
    /// # Termination
    /// - reason: the `while let` loop over an explicit stack of cells, not
    ///   recursion.
    /// - measure: the cells left open. A cell's environment names only cells
    ///   pushed before it, so a cell waits only on older ones, and each turn
    ///   closes the top cell or stacks an older open one.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value read in an environment of its own unloads to
    ///   the substituting reduction's, through cells nested several deep.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    fn close(
        &mut self,
        (arena, table, memo): Machine<'_>,
        environment: Environment,
        read: BinderDepth,
    )
    {
        let mut open = self.open_cells(environment, read);
        while let Some(&top) = open.last() {
            let Some(&Cell {
                held: Held::Value(held),
                closed: None,
                ..
            }) = self.cells.get(top.0)
            else {
                let _closed = open.pop();
                continue;
            };
            let reads = BinderDepth::from(u32::from(arena.value_support(held.node).depth()));
            let inner = self.read(held.environment, reads, BinderDepth::NONE);
            let waiting =
                inner.map_or_else(Vec::new, |inner| self.open_cells(held.environment, inner));
            if !waiting.is_empty() {
                open.extend(waiting);
                continue;
            }
            let value = inner.map_or(held.node, |inner| {
                let (environment, width) = self.substitution(arena, held.environment, inner);
                unload_value(arena, table, memo, (held.node, environment), width)
            });
            if let Some(cell) = self.cells.get_mut(top.0) {
                cell.closed = Some(value);
            }
            let _closed = open.pop();
        }
    }

    /// The open cells among `environment`'s `read` innermost binders, read
    /// through aliases.
    ///
    /// # Specification
    /// trivial.
    fn open_cells(
        &self,
        environment: Environment,
        read: BinderDepth,
    ) -> Vec<CellIndex>
    {
        let mut open = Vec::new();
        let mut current = environment.0;
        for _binder in 0 .. u32::from(read) {
            let Some(index) = current
            else {
                break;
            };
            let Some(cell) = self.cells.get(index.0)
            else {
                break;
            };
            let target = match cell.held {
                Held::Value(_) => index,
                Held::Alias(target) => target,
            };
            if self
                .cells
                .get(target.0)
                .is_some_and(|cell| cell.closed.is_none())
            {
                open.push(target);
            }
            current = cell.outer.0;
        }
        open
    }

    /// The tuple of `environment`'s values, the innermost binder's first, and
    /// how many there are: each of the `read` innermost closed, each past them
    /// a stand-in no read reaches.
    ///
    /// # Specification
    /// - requires: [`Self::close`] has closed the `read` innermost cells.
    /// - ensures: a tuple with one component per binder of `environment`, the
    ///   component of each of the `read` innermost its closed value.
    /// - provides: the replacements [`crate::rewrite::unload_computation`]
    ///   substitutes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the components are read off the store's cells.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — environments whose read binders sit among unread
    ///   ones, and cells aliasing others, unload to the substituting
    ///   reduction's weak heads.
    /// - witness: `replay::tests::the_environment_reduction_agrees_with_the_substituting_one`
    fn substitution(
        &self,
        arena: &mut TermArena,
        environment: Environment,
        read: BinderDepth,
    ) -> (ValueId, BinderDepth)
    {
        let mut components = Vec::new();
        let mut current = environment.0;
        let mut position = 0_u32;
        while let Some(index) = current {
            let Some(cell) = self.cells.get(index.0)
            else {
                break;
            };
            let target = match cell.held {
                Held::Value(_) => cell,
                Held::Alias(target) => self.cells.get(target.0).unwrap_or(cell),
            };
            let stand_in = match target.held {
                Held::Value(held) => held.node,
                Held::Alias(_) => arena.value_unit(),
            };
            let component = if position < u32::from(read) {
                target.closed.unwrap_or(stand_in)
            }
            else {
                stand_in
            };
            components.push(component);
            position = position.saturating_add(1);
            current = cell.outer.0;
        }
        (arena.value_tuple(&components), self.width(environment))
    }
}

#[cfg(test)]
mod tests;
