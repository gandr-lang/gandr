//! Generic evaluation of relation programs, with typed neutral indices.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Clause;
use super::Relation;
use super::RelationError;
use super::RelationId;
use super::check_value;
use crate::conv::Convertibility;
use crate::conv::equal_values;

/// An index-expression address in one fibre computation.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct IndexId(usize);

/// A native value or a typed projection of a neutral product index.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Index
{
    /// An existing value in the term arena.
    Value(ValueId),
    /// First product coordinate; canonical pairs reduce before insertion.
    First(IndexId),
    /// Second product coordinate; canonical pairs reduce before insertion.
    Second(IndexId),
}

/// An address in a computed fibre graph.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FiberId(usize);

/// A relation fibre in normal form, including its uncomputed neutral cases.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fiber
{
    /// The inhabited unit fibre.
    Unit,
    /// The empty fibre, not an error or a negative checker verdict.
    Empty,
    /// Both component fibres, without dropping either coordinate.
    Product(FiberId, FiberId),
    /// Native certified equivalence between the indexed codes, not Unit.
    Universe(IndexId, IndexId),
    /// Four higher obligations between two native equivalence certificates.
    Certificate(IndexId, IndexId),
    /// Discrete equality on neutral base indices remains a type.
    Discrete(IndexId, IndexId),
    /// A case-indexed relation awaiting an injection at an index.
    Suspended(IndexId, IndexId),
    /// The suspended product over two arguments and their relation premise.
    Function
    {
        /// Both argument indices range over this type.
        argument: ValueTypeId,
        /// Returned values are related at this type, in the enclosing mode.
        result: ValueTypeId,
        /// The first function, including neutral projections.
        left: IndexId,
        /// The second function, including neutral projections.
        right: IndexId,
    },
}

/// One evaluated fibre, retaining symbolic indices rather than deciding them.
#[derive(Clone, Debug)]
pub struct Fibers
{
    /// Index expressions in constructor order.
    indices: Vec<Index>,
    /// Fibre expressions in constructor order.
    nodes: Vec<Fiber>,
    /// The result expression.
    root: FiberId,
}

/// A product coordinate selected by the generic evaluator.
#[derive(Clone, Copy)]
enum Coordinate
{
    /// First component.
    First,
    /// Second component.
    Second,
}

/// Explicit evaluator continuations; no Rust call-stack recursion.
#[derive(Clone, Copy)]
enum Task
{
    /// Evaluate a relation combinator at two indices.
    Visit(RelationId, IndexId, IndexId),
    /// Assemble independently computed component fibres.
    Pair,
    /// Retain a completed fibre for this call only.
    Remember(RelationId, IndexId, IndexId),
}

impl Relation
{
    /// Compute the indexed fibre in an ordinary open term context.
    ///
    /// # Specification
    /// - ensures: checks both indices, then interprets relation combinators.
    ///   Cross-injection fibres are Empty; products unfold even at neutral
    ///   indices by projections. Unequal neutral base variables remain a
    ///   discrete relation, never an empty fibre. Sum neutrals remain
    ///   suspended.
    /// - fails: `Typing` for ill-typed indices; `Arena` for unreadable nodes.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed constructors have their mathematical fibres;
    ///   distinct rigid variables cannot be judged unequal merely by syntax.
    /// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
    /// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |fibers| fibers.root.0 < fibers.nodes.len() && fibers.indices.contains(&Index::Value(left)) && fibers.indices.contains(&Index::Value(right))))]
    #[inline]
    pub fn fiber(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        left: ValueId,
        right: ValueId,
    ) -> Result<Fibers, RelationError>
    {
        self.fiber_at(arena, self.root, context, left, right)
    }

    /// Interpret a child relation without copying its program.
    ///
    /// # Specification
    /// - ensures: checks indices at this child and retains all residual fibres.
    /// - fails: index typing errors or unreadable program addresses.
    /// - panics: none.
    ///
    /// # Errors
    /// Typing or Arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — function applications use argument and result
    ///   relations.
    /// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
    #[spec(ensures: |ret| match ret {
        Ok(ref fibers) => fibers.root.0 < fibers.nodes.len()
            && fibers.nodes.iter().enumerate().all(|(id, node)| match *node { Fiber::Product(a, b) => a.0 < id && b.0 < id, _ => true })
            && self.node(relation).is_ok_and(|node| matches!((node.clause, fibers.get(fibers.root)),
                (Clause::Unit, Ok(Fiber::Unit)) | (Clause::Empty, Ok(Fiber::Empty)) | (Clause::Universe, Ok(Fiber::Universe(..))) | (Clause::Certificate, Ok(Fiber::Certificate(..))) | (Clause::Product(..), Ok(Fiber::Product(..))) | (Clause::Function(..), Ok(Fiber::Function { .. }))
                | (Clause::Discrete | Clause::Sum(..) | Clause::CaseLeft(..) | Clause::CaseRight(..), Ok(_)))),
        Err(RelationError::RecursiveObservationRequired) => self.nodes.iter().any(|node| matches!(node.clause, Clause::List(_))),
        Err(_) => true,
    })]
    pub(super) fn fiber_at(
        &self,
        arena: &mut TermArena,
        relation: RelationId,
        context: &[ValueTypeId],
        left: ValueId,
        right: ValueId,
    ) -> Result<Fibers, RelationError>
    {
        let root = self.node(relation)?;
        check_value(arena, context, left, root.source)?;
        check_value(arena, context, right, root.target)?;
        let mut result = Fibers {
            indices: Vec::new(),
            nodes: Vec::new(),
            root: FiberId(0),
        };
        let mut shared = BTreeMap::new();
        let left = result.index(Index::Value(left), &mut shared);
        let right = result.index(Index::Value(right), &mut shared);
        let mut tasks = Vec::from([Task::Visit(relation, left, right)]);
        let mut values = Vec::new();
        let mut completed = BTreeMap::new();
        while let Some(task) = tasks.pop() {
            let fibre = match task {
                | Task::Remember(relation, left, right) => {
                    let value = *values.last().ok_or(RelationError::Arena)?;
                    completed.insert((relation, left, right), value);
                    continue;
                },
                | Task::Pair => {
                    let right = values.pop().ok_or(RelationError::Arena)?;
                    let left = values.pop().ok_or(RelationError::Arena)?;
                    Fiber::Product(left, right)
                },
                | Task::Visit(relation, left, right) => {
                    if let Some(&value) = completed.get(&(relation, left, right)) {
                        values.push(value);
                        continue;
                    }
                    tasks.push(Task::Remember(relation, left, right));
                    let node = self.node(relation)?;
                    match node.clause {
                        | Clause::Unit => Fiber::Unit,
                        | Clause::Empty => Fiber::Empty,
                        | Clause::Universe => Fiber::Universe(left, right),
                        | Clause::Certificate => Fiber::Certificate(left, right),
                        | Clause::Discrete => result.discrete(arena, left, right)?,
                        | Clause::List(_) => {
                            return Err(RelationError::RecursiveObservationRequired);
                        },
                        | Clause::Function(argument, result) => {
                            let argument = self.node(argument)?;
                            let result = self.node(result)?;
                            Fiber::Function {
                                argument: argument.source,
                                result: result.source,
                                left,
                                right,
                            }
                        },
                        | Clause::Product(first, second) => {
                            let first_left =
                                result.project(arena, left, Coordinate::First, &mut shared)?;
                            let first_right =
                                result.project(arena, right, Coordinate::First, &mut shared)?;
                            let second_left =
                                result.project(arena, left, Coordinate::Second, &mut shared)?;
                            let second_right =
                                result.project(arena, right, Coordinate::Second, &mut shared)?;
                            tasks.push(Task::Pair);
                            tasks.push(Task::Visit(second, second_left, second_right));
                            tasks.push(Task::Visit(first, first_left, first_right));
                            continue;
                        },
                        | Clause::Sum(first, second) => {
                            let left_injection = result.injection(arena, left)?;
                            let right_injection = result.injection(arena, right)?;
                            match (left_injection, right_injection) {
                                | (Injection::Known(a, x), Injection::Known(b, y)) => {
                                    if a == b {
                                        let relation = match a {
                                            | Side::Left => first,
                                            | Side::Right => second,
                                        };
                                        let left = result.index(Index::Value(x), &mut shared);
                                        let right = result.index(Index::Value(y), &mut shared);
                                        tasks.push(Task::Visit(relation, left, right));
                                        continue;
                                    }
                                    Fiber::Empty
                                },
                                | _ => Fiber::Suspended(left, right),
                            }
                        },
                        | clause @ (Clause::CaseLeft(first, second)
                        | Clause::CaseRight(first, second)) => {
                            let index = match clause {
                                | Clause::CaseLeft(..) => left,
                                | _ => right,
                            };
                            let injection = result.injection(arena, index)?;
                            match injection {
                                | Injection::Known(side, value) => {
                                    let relation = match side {
                                        | Side::Left => first,
                                        | Side::Right => second,
                                    };
                                    let payload = result.index(Index::Value(value), &mut shared);
                                    let (left, right) = match clause {
                                        | Clause::CaseLeft(..) => (payload, right),
                                        | _ => (left, payload),
                                    };
                                    tasks.push(Task::Visit(relation, left, right));
                                    continue;
                                },
                                | Injection::Neutral => Fiber::Suspended(left, right),
                            }
                        },
                    }
                },
            };
            let id = FiberId(result.nodes.len());
            result.nodes.push(fibre);
            values.push(id);
        }
        result.root = values.pop().ok_or(RelationError::Arena)?;
        Ok(result)
    }
}

/// An injection observation; absence means a neutral, not a malformed value.
enum Injection
{
    /// A visible injection and its payload.
    Known(Side, ValueId),
    /// Case evaluation is suspended on this index.
    Neutral,
}

impl Fibers
{
    /// The fibre graph's root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> FiberId
    {
        self.root
    }

    /// Resolve a fibre expression.
    ///
    /// # Specification
    /// - ensures: the requested fibre, or `Arena` for an unrelated address.
    /// - fails: `Arena` for an unreadable address.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — products preserve both observable component fibres.
    /// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
    #[spec(ensures: |ret| match ret { Ok(node) => self.nodes.get(id.0) == Some(&node), Err(RelationError::Arena) => id.0 >= self.nodes.len(), Err(_) => false })]
    #[inline]
    pub fn get(
        &self,
        id: FiberId,
    ) -> Result<Fiber, RelationError>
    {
        self.nodes.get(id.0).copied().ok_or(RelationError::Arena)
    }

    /// Resolve a symbolic index expression.
    ///
    /// # Specification
    /// - ensures: the requested index, or `Arena` for an unrelated address.
    /// - fails: `Arena` for an unreadable address.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two projections of a neutral pair stay distinct.
    /// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
    #[spec(ensures: |ret| match ret { Ok(index) => self.indices.get(id.0) == Some(&index), Err(RelationError::Arena) => id.0 >= self.indices.len(), Err(_) => false })]
    #[inline]
    pub fn get_index(
        &self,
        id: IndexId,
    ) -> Result<Index, RelationError>
    {
        self.indices.get(id.0).copied().ok_or(RelationError::Arena)
    }

    /// Lower a fully computed fibre to the native value-type vocabulary.
    ///
    /// # Specification
    /// - ensures: Unit, Empty, Product and universe fibres become native types.
    ///   Universe endpoints pass the existing path decoder; residuals are not
    ///   interpreted as either truth or falsity.
    /// - fails: `NeutralFiber` on a residual, `HigherFieldRequired` on a
    ///   certificate identity, `Path` outside native endpoint formation, or
    ///   `Arena` on invalid edges.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — cross injections lower to native Empty, while neutral
    ///   base equality never does.
    /// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
    /// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
    /// - witness: `path_universe::tests::universe_fold_tests::universe_clause_is_native`
    #[spec(ensures: |ret| match ret {
        Ok(ty) => !self.nodes.iter().any(|node| matches!(node, &Fiber::Discrete(..) | &Fiber::Suspended(..) | &Fiber::Function { .. } | &Fiber::Certificate(..)))
            && matches!((self.get(self.root), arena.value_type(ty)),
                (Ok(Fiber::Unit), Some(&gandr_kernel_term::ValueType::Unit)) | (Ok(Fiber::Empty), Some(&gandr_kernel_term::ValueType::Empty))
                | (Ok(Fiber::Product(..)), Some(&gandr_kernel_term::ValueType::Product(..))) | (Ok(Fiber::Universe(..)), Some(&gandr_kernel_term::ValueType::PathUniverse(..)))),
        Err(RelationError::HigherFieldRequired) => self.nodes.iter().any(|node| matches!(node, &Fiber::Certificate(..))),
        Err(_) => true,
    })]
    #[inline]
    pub fn native(
        &self,
        arena: &mut TermArena,
    ) -> Result<ValueTypeId, RelationError>
    {
        if self.nodes.iter().any(|node| {
            matches!(
                node,
                Fiber::Discrete(..) | Fiber::Suspended(..) | Fiber::Function { .. }
            )
        }) {
            return Err(RelationError::NeutralFiber);
        }
        let mut types = Vec::with_capacity(self.nodes.len());
        for &node in &self.nodes {
            let ty = match node {
                | Fiber::Unit => arena.value_type_unit(),
                | Fiber::Empty => arena.value_type_empty(),
                | Fiber::Universe(left, right) => {
                    let (left, right) = self.native_indices(left, right)?;
                    let ty = arena.value_type_path_universe(left, right);
                    crate::path_universe::endpoints(
                        arena,
                        ty,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(|error| RelationError::Path(alloc::boxed::Box::new(error)))?;
                    ty
                },
                | Fiber::Certificate(..) => return Err(RelationError::HigherFieldRequired),
                | Fiber::Product(left, right) => {
                    let left = *types.get(left.0).ok_or(RelationError::Arena)?;
                    let right = *types.get(right.0).ok_or(RelationError::Arena)?;
                    arena.value_type_product(left, right)
                },
                | Fiber::Discrete(..) | Fiber::Suspended(..) | Fiber::Function { .. } => {
                    return Err(RelationError::NeutralFiber);
                },
            };
            types.push(ty);
        }
        types.get(self.root.0).copied().ok_or(RelationError::Arena)
    }

    /// Intern index syntax locally; equality is a positive syntax-sharing step.
    ///
    /// # Specification
    /// - requires: every cached index resolves to its recorded syntax.
    /// - ensures: the returned id holds exactly `index` and is its cached id; a
    ///   repeated index does not append another node.
    /// - provides: local positive sharing without an equality decision on
    ///   values.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reused product coordinates retain their indices,
    ///   while distinct neutral coordinates remain distinct fibres.
    /// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
    #[spec(captures: [before = self.indices.len(), existing = shared.get(&index).copied()], ensures: |ret| self.indices.get(ret.0) == Some(&index) && shared.get(&index) == Some(&ret) && match existing { Some(id) => ret == id && self.indices.len() == before, None => self.indices.len() == before.saturating_add(1) })]
    fn index(
        &mut self,
        index: Index,
        shared: &mut BTreeMap<Index, IndexId>,
    ) -> IndexId
    {
        if let Some(&id) = shared.get(&index) {
            return id;
        }
        let id = IndexId(self.indices.len());
        self.indices.push(index);
        shared.insert(index, id);
        id
    }

    /// Observe a product coordinate, reducing only a visible pair.
    ///
    /// # Specification
    /// - requires: `index` has a product type, established by the relation
    ///   program.
    /// - ensures: selects the requested child or retains a neutral projection.
    /// - fails: `Arena` on an unreadable index.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — neutral products unfold without requiring closed
    ///   pairs.
    /// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
    #[spec(ensures: |ret| match ret {
        Ok(projected) => match self.get_index(index) {
            Ok(Index::Value(value)) if matches!(arena.value(value), Some(&Value::Pair(..))) => matches!((arena.value(value), self.get_index(projected)), (Some(&Value::Pair(left, right)), Ok(Index::Value(found))) if found == match coordinate { Coordinate::First => left, Coordinate::Second => right }),
            Ok(_) => matches!((coordinate, self.get_index(projected)), (Coordinate::First, Ok(Index::First(held))) | (Coordinate::Second, Ok(Index::Second(held))) if held == index),
            Err(_) => false,
        },
        Err(RelationError::Arena) => self.get_index(index).is_err(),
        Err(_) => false,
    })]
    fn project(
        &mut self,
        arena: &TermArena,
        index: IndexId,
        coordinate: Coordinate,
        shared: &mut BTreeMap<Index, IndexId>,
    ) -> Result<IndexId, RelationError>
    {
        let index_term = self.get_index(index)?;
        if let Index::Value(value) = index_term
            && let Some(&Value::Pair(left, right)) = arena.value(value)
        {
            let value = match coordinate {
                | Coordinate::First => left,
                | Coordinate::Second => right,
            };
            return Ok(self.index(Index::Value(value), shared));
        }
        let projection = match coordinate {
            | Coordinate::First => Index::First(index),
            | Coordinate::Second => Index::Second(index),
        };
        Ok(self.index(projection, shared))
    }

    /// Observe an injection without deciding equality of neutral indices.
    ///
    /// # Specification
    /// - ensures: a constructor observation or an explicit suspended case.
    /// - fails: `Arena` on an unreadable index.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a neutral sum index never selects a branch.
    /// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
    #[spec(ensures: |ret| match ret {
        Ok(Injection::Known(side, payload)) => self.get_index(index).is_ok_and(|term| matches!(term, Index::Value(value) if matches!(arena.value(value), Some(&Value::Injection(found, child)) if found == side && child == payload))),
        Ok(Injection::Neutral) => self.get_index(index).is_ok_and(|term| !matches!(term, Index::Value(value) if matches!(arena.value(value), Some(&Value::Injection(..))))),
        Err(RelationError::Arena) => self.get_index(index).is_err(),
        Err(_) => false,
    })]
    fn injection(
        &self,
        arena: &TermArena,
        index: IndexId,
    ) -> Result<Injection, RelationError>
    {
        let index = self.get_index(index)?;
        match index {
            | Index::Value(value) => match arena.value(value) {
                | Some(&Value::Injection(side, payload)) => Ok(Injection::Known(side, payload)),
                | _ => Ok(Injection::Neutral),
            },
            | Index::First(_) | Index::Second(_) => Ok(Injection::Neutral),
        }
    }

    /// Compute discrete base identity, distinguishing syntax from inequality.
    ///
    /// # Specification
    /// - ensures: reflexive syntax yields Unit; unequal canonical literals
    ///   yield Empty; every other pair yields a residual discrete relation.
    /// - fails: `Arena` on an unreadable index.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — different base variables remain related by an unknown
    ///   fibre, while distinct canonical literals have an empty fibre.
    /// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
    #[spec(ensures: |ret| match ret {
        Ok(Fiber::Unit) => left == right || matches!((self.get_index(left), self.get_index(right)), (Ok(Index::Value(a)), Ok(Index::Value(b))) if equal_values(arena, a, b) == Convertibility::Convertible),
        Ok(Fiber::Empty) => matches!((self.get_index(left), self.get_index(right)), (Ok(Index::Value(a)), Ok(Index::Value(b))) if equal_values(arena, a, b) == Convertibility::Distinct && matches!((arena.value(a), arena.value(b)), (Some(&Value::Literal(_)), Some(&Value::Literal(_))))),
        Ok(Fiber::Discrete(a, b)) => a == left && b == right && left != right,
        Err(RelationError::Arena) => self.get_index(left).is_err() || self.get_index(right).is_err(),
        _ => false,
    })]
    fn discrete(
        &self,
        arena: &TermArena,
        left: IndexId,
        right: IndexId,
    ) -> Result<Fiber, RelationError>
    {
        if left == right {
            return Ok(Fiber::Unit);
        }
        let left_index = self.get_index(left)?;
        let right_index = self.get_index(right)?;
        if let (Index::Value(a), Index::Value(b)) = (left_index, right_index) {
            if equal_values(arena, a, b) == Convertibility::Convertible {
                return Ok(Fiber::Unit);
            }
            if matches!(
                (arena.value(a), arena.value(b)),
                (Some(Value::Literal(_)), Some(Value::Literal(_)))
            ) {
                return Ok(Fiber::Empty);
            }
        }
        Ok(Fiber::Discrete(left, right))
    }
}
