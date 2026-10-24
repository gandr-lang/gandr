//! The lexicographic path order with status over a precedence.
//!
//! At an instantiation the order reads as the computability path order reads
//! a variable applied to terms. [`orient`] is the oracle deciding whether a
//! left side stands above a right one and returning the derivation; [`check`]
//! is the checker replaying a derivation.
//!
//! [`orient`] fills one table of every pair of positions of the two sides
//! from the last positions up, so no comparison recurses: each cell records
//! whether the two subterms are one term and the clause, if any, that puts
//! the left above the right. The derivation is read off the table from the
//! root pair. [`check`] decides each equality a step reads by comparing the
//! two subterms, finds each ordered premise among the derivation's steps, and
//! refuses at the first step that does not hold.
//!
//! # Boundaries
//!
//! A left subterm is compared only when it applies a symbol, abstracts a name
//! or is a bound occurrence. A variable and an instantiation are above
//! nothing: a substitution can make either any term, so neither is stable
//! under it (the nonversatile terms of the βη-normal computability path
//! order). A right subterm that is a variable its side instantiates stands at
//! a function type and is below no term of the one base type; a term covers
//! it only through an argument equal to it.
//!
//! A covering clause asks the left subterm to cover every argument of the
//! right: to be above it, or to hold an argument equal to or above it. An
//! instantiation's arguments that are values need no cover: instantiating a
//! pattern at a value selects a branch of it and calls no operation, as a
//! logically constrained system's values stand below every term an operation
//! heads.
//!
//! # References
//!
//! - Sam Kamin and Jean-Jacques Lévy. "Two Generalizations of the Recursive
//!   Path Ordering." Unpublished note, University of Illinois, 1980 — the
//!   lexicographic path order.
//! - Nachum Dershowitz and Zohar Manna. "Proving Termination with Multiset
//!   Orderings." _Communications of the ACM_ 22(8), 1979,
//!   `doi:10.1145/359138.359142` — the multiset extension.
//! - Frédéric Blanqui, Jean-Pierre Jouannaud and Albert Rubio. "The
//!   Computability Path Ordering." _Logical Methods in Computer Science_ 11(4),
//!   2015, `doi:10.2168/LMCS-11(4:3)2015` — the clauses, Figure 1.
//! - Johannes Niederhauser and Aart Middeldorp. "The Computability Path Order
//!   for Beta-Eta-Normal Higher-Order Rewriting." `arXiv:2505.20121`, 2025 —
//!   the nonversatile terms a comparison starts from.
//! - Liye Guo and Cynthia Kop. "Higher-Order LCTRSs and Their Termination."
//!   `arXiv:2307.13519`, 2023 — values below every operation's term.

use alloc::vec::Vec;

use anodized::spec;

use crate::evidence::Argument;
use crate::evidence::Clause;
use crate::evidence::Cover;
use crate::evidence::CoverIndex;
use crate::evidence::Derivation;
use crate::evidence::Evidence;
use crate::evidence::Relation;
use crate::evidence::Step;
use crate::precedence::Place;
use crate::precedence::Precedence;
use crate::precedence::Status;
use crate::term::Former;
use crate::term::Node;
use crate::term::Term;
use crate::term::Valuation;
use crate::term::Valued;

/// Whether the order puts a left side above a right one.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Orientation
{
    /// It does, by the evidence.
    Oriented(Evidence),
    /// It does not.
    Unoriented,
}

/// Whether a derivation replays.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Replay
{
    /// Every step holds and one compares the two roots.
    Holds,
    /// It does not, refused where it fails.
    Refused(Refusal),
}

/// Where a derivation fails to replay.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// No step compares the two roots.
    Root,
    /// The step comparing the subterms at these positions does not hold.
    Step
    {
        /// The left subterm's position.
        left: Node,
        /// The right subterm's position.
        right: Node,
    },
}

/// The tables an orientation and a replay fill, kept between calls so a run of
/// comparisons allocates once.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub struct Buffers
{
    /// Every pair of positions, row by row.
    table: Vec<Cell>,
    /// How each right node is typed: a variable its side instantiates stands
    /// at a function type.
    functional: Vec<Typing>,
    /// Whether the derivation has read each pair.
    reached: Vec<bool>,
    /// The pairs waiting to be read or compared.
    pending: Vec<(Node, Node)>,
    /// The multiset extension's working lists.
    scratch: Scratch,
}

/// The multiset extension's working lists.
#[derive(Debug, Default)]
struct Scratch
{
    /// The left node's arguments.
    lefts: Vec<Node>,
    /// Whether each left argument equals a right argument it is matched with.
    matched: Vec<bool>,
    /// For each right argument, the left argument equal to it, if one is.
    partners: Vec<Option<Argument>>,
}

/// How one left subterm compares with one right subterm.
#[derive(Clone, Copy, Debug, Default)]
struct Cell
{
    /// The two are one term.
    equal: bool,
    /// The clause putting the left above the right, if one does.
    above: Option<Clause>,
}

impl Cell
{
    /// How the left subterm stands to the right one, if it is equal or above.
    ///
    /// # Specification
    /// trivial.
    fn relation(self) -> Option<Relation>
    {
        if self.equal {
            Some(Relation::Equal)
        }
        else {
            self.above.map(|_| Relation::Above)
        }
    }
}

/// How a right node is typed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Typing
{
    /// The one base type.
    Base,
    /// A function type: a variable its side instantiates.
    Function,
}

/// The right side's node count, a table's row width.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Columns(usize);

/// A cell's index in a table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Slot(usize);

/// A filled table, read by position pairs.
#[derive(Clone, Copy, Debug)]
struct Grid<'table>
{
    /// The cells, row by row.
    cells: &'table [Cell],
    /// The row width.
    columns: Columns,
}

impl Grid<'_>
{
    /// The cell of `row` and `column`; the default past the table.
    ///
    /// # Specification
    /// trivial.
    fn at(
        self,
        row: Node,
        column: Node,
    ) -> Cell
    {
        index(row, column, self.columns)
            .and_then(|at| self.cells.get(at.0).copied())
            .unwrap_or_default()
    }
}

/// The cell index of `row` and `column` in a table `columns` wide.
///
/// # Specification
/// trivial.
fn index(
    row: Node,
    column: Node,
    columns: Columns,
) -> Option<Slot>
{
    usize::from(row)
        .checked_mul(columns.0)?
        .checked_add(usize::from(column))
        .map(Slot)
}

/// Which covers a covering clause admits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Coverage
{
    /// An argument the left subterm is above, or one of its arguments is equal
    /// to or above.
    Plain,
    /// Those, or a value.
    Values,
}

/// Whether the order over `precedence` puts `left` above `right`, and the
/// derivation when it does.
///
/// # Specification
/// - requires: `left` and `right` are well-formed sides.
/// - ensures: oriented exactly when some clause puts `left`'s root above
///   `right`'s, the clauses read as the module states them; the evidence is
///   then a derivation [`check`] replays.
/// - ensures: unoriented when `left`'s root is a variable or an instantiation,
///   and when the two sides are one term.
/// - panics: none.
/// - intension: one table of every pair of positions, filled from the last up,
///   then the derivation read off it from the root pair.
///
/// # Adequacy
/// - hypothesis: L3 — each clause decides a witness: a recursion on a
///   descending argument by precedence and subterm, a multiset swap that the
///   lexicographic status refuses, an instantiation below the application
///   holding its variable bare or under its abstraction while β is not, a value
///   needing no cover, an abstraction and a bound occurrence standing where a
///   ground symbol does; a variable, an instantiation and an equal side are
///   above nothing. Dropping a clause, the nonversatile restriction, the value
///   cover or the abstraction walk changes one of them, and every oriented
///   witness's derivation replays.
/// - witness: `tests::lpo::a_descending_recursion_is_oriented_and_its_derivation_replays`
/// - witness: `tests::lpo::a_variable_or_an_equal_side_is_above_nothing`
/// - witness: `tests::lpo::multiset_status_orients_what_lexicographic_status_does_not`
/// - witness: `tests::lpo::an_instantiation_is_below_the_application_holding_its_variable`
/// - witness: `tests::lpo::a_pattern_under_its_abstraction_holds_its_variable`
/// - witness: `tests::lpo::a_value_needs_no_cover`
/// - witness: `tests::lpo::an_instantiation_on_the_left_is_above_nothing`
/// - witness: `tests::lpo::an_abstraction_and_a_bound_occurrence_stand_where_a_ground_symbol_does`
#[spec(ensures: |ret| match ret {
    Orientation::Oriented(Evidence::Path(ref derivation)) =>
        check(left, right, precedence, derivation, &mut Buffers::default()) == Replay::Holds,
    Orientation::Unoriented => true,
})]
#[inline]
pub fn orient<L, R, P>(
    left: &L,
    right: &R,
    precedence: &P,
    buffers: &mut Buffers,
) -> Orientation
where
    L: Valued,
    R: Term<Symbol = L::Symbol, Variable = L::Variable, Bound = L::Bound>,
    P: Precedence<Symbol = L::Symbol>,
{
    let order = Order {
        left,
        right,
        precedence,
    };
    order.fill(buffers);
    let root = Node::from(0_usize);
    let columns = Columns(usize::from(right.end()));
    if (Grid {
        cells: &buffers.table,
        columns,
    })
    .at(root, root)
    .above
    .is_none()
    {
        return Orientation::Unoriented;
    }
    Orientation::Oriented(Evidence::Path(order.derive(buffers)))
}

/// Whether `derivation` replays as a derivation of `left` above `right` over
/// `precedence`.
///
/// # Specification
/// - requires: `left` and `right` are well-formed sides.
/// - ensures: holds exactly when a step compares the two roots and every step
///   holds: its positions are the sides', its left subterm applies a symbol,
///   abstracts or is a bound occurrence, its right subterm is no variable the
///   right side instantiates, and its clause's conditions hold — each equality
///   it reads by comparing the two subterms, each ordered premise by a step at
///   the pair, each cover as the clause admits it. Otherwise refused at the
///   root, or at the first step, in the derivation's order, that does not hold.
/// - panics: none.
/// - executable: none — the replay is the predicate; restating it would replay
///   again.
/// - intension: one pass over the steps, each premise found by binary search
///   and each equality by one walk of the two subterms.
///
/// # Adequacy
/// - hypothesis: L3 — every oriented witness's derivation holds; a derivation
///   without its root step is refused at the root; a step whose clause is
///   swapped for one whose conditions fail, or whose premise step is removed,
///   is refused at that step; a forged step over an unoriented pair is refused.
///   Accepting a step without its premise, or reading a forged clause as
///   written, changes one of them.
/// - witness: `tests::lpo::a_descending_recursion_is_oriented_and_its_derivation_replays`
/// - witness: `tests::lpo::a_forged_derivation_is_refused`
#[inline]
pub fn check<L, R, P>(
    left: &L,
    right: &R,
    precedence: &P,
    derivation: &Derivation,
    buffers: &mut Buffers,
) -> Replay
where
    L: Valued,
    R: Term<Symbol = L::Symbol, Variable = L::Variable, Bound = L::Bound>,
    P: Precedence<Symbol = L::Symbol>,
{
    let order = Order {
        left,
        right,
        precedence,
    };
    match order.replay(derivation, buffers) {
        Ok(()) => Replay::Holds,
        Err(refusal) => Replay::Refused(refusal),
    }
}

/// The two sides and the precedence one comparison reads.
#[derive(Clone, Copy, Debug)]
struct Order<'sides, L, R, P>
{
    /// The left side.
    left: &'sides L,
    /// The right side.
    right: &'sides R,
    /// The precedence.
    precedence: &'sides P,
}

impl<L, R, P> Order<'_, L, R, P>
where
    L: Valued,
    R: Term<Symbol = L::Symbol, Variable = L::Variable, Bound = L::Bound>,
    P: Precedence<Symbol = L::Symbol>,
{
    /// Fill the table of every pair of positions, from the last up.
    ///
    /// # Specification
    /// - ensures: each cell holds whether its two subterms are one term and the
    ///   first clause that puts the left above the right — subterm, then the
    ///   clause the right former calls for — or none.
    /// - panics: none.
    /// - executable: none — the table is the order; a predicate restating it
    ///   would fill it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`orient`].
    /// - witness: `tests::lpo::a_descending_recursion_is_oriented_and_its_derivation_replays`
    fn fill(
        &self,
        buffers: &mut Buffers,
    )
    {
        let rows = usize::from(self.left.end());
        let columns = Columns(usize::from(self.right.end()));
        let &mut Buffers {
            ref mut table,
            ref mut functional,
            ref mut scratch,
            ..
        } = buffers;
        self.mark_functional(functional);
        table.clear();
        table.resize(rows.saturating_mul(columns.0), Cell::default());
        for row in (0 .. rows).rev() {
            for column in (0 .. columns.0).rev() {
                let (row, column) = (Node::from(row), Node::from(column));
                let grid = Grid {
                    cells: table,
                    columns,
                };
                let cell = self.compare(grid, functional, scratch, row, column);
                if let Some(slot) = index(row, column, columns).and_then(|at| table.get_mut(at.0)) {
                    *slot = cell;
                }
            }
        }
    }

    /// Type each right node: a variable its side instantiates at a function
    /// type, every other node at the base type.
    ///
    /// # Specification
    /// trivial.
    fn mark_functional(
        &self,
        functional: &mut Vec<Typing>,
    )
    {
        let end = usize::from(self.right.end());
        functional.clear();
        functional.extend(
            (0 .. end).map(|column| match self.right.former(Node::from(column)) {
                Former::Variable(variable)
                    if (0 .. end).any(|at| {
                        self.right.former(Node::from(at)) == Former::Application(variable)
                    }) =>
                {
                    Typing::Function
                },
                Former::Symbol(_)
                | Former::Variable(_)
                | Former::Application(_)
                | Former::Abstraction
                | Former::Bound(_) => Typing::Base,
            }),
        );
    }

    /// The cell of `row` and `column`, every pair past them compared.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        grid: Grid<'_>,
        functional: &[Typing],
        scratch: &mut Scratch,
        row: Node,
        column: Node,
    ) -> Cell
    {
        let heads = self.one_head(row, column);
        let equal = heads.is_some()
            && self
                .pairs(row, column)
                .all(|(one, two)| grid.at(one, two).equal);
        let comparable = matches!(
            self.left.former(row),
            Former::Symbol(_) | Former::Abstraction | Former::Bound(_)
        ) && functional.get(usize::from(column)) == Some(&Typing::Base);
        let above = if comparable {
            self.clause(grid, scratch, row, column, heads)
        }
        else {
            None
        };
        Cell { equal, above }
    }

    /// The first clause putting the left subterm at `row` above the right
    /// subterm at `column`, the subterm clause first.
    ///
    /// # Specification
    /// trivial.
    fn clause(
        &self,
        grid: Grid<'_>,
        scratch: &mut Scratch,
        row: Node,
        column: Node,
        heads: Option<Status>,
    ) -> Option<Clause>
    {
        let subterm = self
            .left
            .arguments(row)
            .enumerate()
            .find_map(|(index, own)| {
                grid.at(own, column)
                    .relation()
                    .map(|relation| Clause::Subterm {
                        argument: Argument::from(index),
                        relation,
                    })
            });
        if subterm.is_some() {
            return subterm;
        }
        match self.right.former(column) {
            Former::Variable(_) => None,
            Former::Application(variable) => {
                let held = self
                    .left
                    .arguments(row)
                    .position(|own| self.holds(own, variable).is_some())?;
                self.right
                    .arguments(column)
                    .all(|argument| {
                        self.valued(argument)
                            .or_else(|| self.covers(grid, row, argument))
                            .is_some()
                    })
                    .then_some(Clause::Instance {
                        held: Argument::from(held),
                    })
            },
            Former::Symbol(_) | Former::Abstraction | Former::Bound(_) => {
                if !self
                    .right
                    .arguments(column)
                    .all(|argument| self.covers(grid, row, argument).is_some())
                {
                    return None;
                }
                match heads {
                    Some(Status::Lexicographic) => {
                        let (index, (one, two)) = self
                            .pairs(row, column)
                            .enumerate()
                            .find(|&(_, (one, two))| !grid.at(one, two).equal)?;
                        grid.at(one, two).above.map(|_| Clause::Lexicographic {
                            argument: Argument::from(index),
                        })
                    },
                    Some(Status::Multiset) => self
                        .multiset(grid, scratch, row, column)
                        .map(|()| Clause::Multiset),
                    None => self.precedes(row, column),
                }
            },
        }
    }

    /// The status two subterms compare their arguments by when they apply one
    /// head: one former, as many arguments.
    ///
    /// # Specification
    /// trivial.
    fn one_head(
        &self,
        row: Node,
        column: Node,
    ) -> Option<Status>
    {
        let node = self.left.former(row);
        if node != self.right.former(column)
            || self.left.arguments(row).count() != self.right.arguments(column).count()
        {
            return None;
        }
        Some(match node {
            Former::Symbol(symbol) => self.precedence.status(symbol),
            Former::Variable(_)
            | Former::Application(_)
            | Former::Abstraction
            | Former::Bound(_) => Status::Lexicographic,
        })
    }

    /// The argument pairs of the subterms at `row` and `column`, left to
    /// right.
    ///
    /// # Specification
    /// trivial.
    fn pairs(
        &self,
        row: Node,
        column: Node,
    ) -> impl Iterator<Item = (Node, Node)> + Clone
    {
        self.left.arguments(row).zip(self.right.arguments(column))
    }

    /// The precedence clause, when the left head is a symbol above the right
    /// head; an abstraction and a bound occurrence stand where a ground
    /// symbol does.
    ///
    /// # Specification
    /// trivial.
    fn precedes(
        &self,
        row: Node,
        column: Node,
    ) -> Option<Clause>
    {
        let Former::Symbol(symbol) = self.left.former(row)
        else {
            return None;
        };
        let below = match self.right.former(column) {
            Former::Symbol(other) => self.precedence.place(other),
            Former::Abstraction | Former::Bound(_) => Place::Ground,
            Former::Variable(_) | Former::Application(_) => return None,
        };
        (self.precedence.place(symbol) > below).then_some(Clause::Precedence)
    }

    /// Where the left argument at `own` holds `variable`: it is the variable,
    /// or the variable instantiated under the abstractions above it.
    ///
    /// # Specification
    /// trivial.
    fn holds(
        &self,
        own: Node,
        variable: L::Variable,
    ) -> Option<Node>
    {
        let mut at = own;
        while self.left.former(at) == Former::Abstraction {
            at = self.left.arguments(at).next()?;
        }
        match self.left.former(at) {
            Former::Variable(held) | Former::Application(held) if held == variable => Some(at),
            Former::Symbol(_)
            | Former::Variable(_)
            | Former::Application(_)
            | Former::Abstraction
            | Former::Bound(_) => None,
        }
    }

    /// The value cover, when the right argument at `argument` is a variable
    /// the left side values.
    ///
    /// # Specification
    /// trivial.
    fn valued(
        &self,
        argument: Node,
    ) -> Option<Cover>
    {
        match self.right.former(argument) {
            Former::Variable(variable) if self.left.valuation(variable) == Valuation::Value => {
                Some(Cover::Value)
            },
            Former::Symbol(_)
            | Former::Variable(_)
            | Former::Application(_)
            | Former::Abstraction
            | Former::Bound(_) => None,
        }
    }

    /// How the left subterm at `row` covers the right argument at `argument`:
    /// above it, or by an own argument equal to or above it.
    ///
    /// # Specification
    /// trivial.
    fn covers(
        &self,
        grid: Grid<'_>,
        row: Node,
        argument: Node,
    ) -> Option<Cover>
    {
        if grid.at(row, argument).above.is_some() {
            return Some(Cover::Above);
        }
        self.left
            .arguments(row)
            .enumerate()
            .find_map(|(index, own)| {
                grid.at(own, argument)
                    .relation()
                    .map(|relation| Cover::Argument {
                        argument: Argument::from(index),
                        relation,
                    })
            })
    }

    /// The multiset extension at `row` and `column`: each right argument
    /// matched with an equal left one, no left argument twice, the rest each
    /// below a left argument no equality matched, and one such left argument.
    /// The matching is left in `scratch`.
    ///
    /// # Specification
    /// trivial.
    fn multiset(
        &self,
        grid: Grid<'_>,
        scratch: &mut Scratch,
        row: Node,
        column: Node,
    ) -> Option<()>
    {
        let &mut Scratch {
            ref mut lefts,
            ref mut matched,
            ref mut partners,
        } = scratch;
        lefts.clear();
        lefts.extend(self.left.arguments(row));
        matched.clear();
        matched.resize(lefts.len(), false);
        partners.clear();
        for argument in self.right.arguments(column) {
            let partner = lefts
                .iter()
                .zip(matched.iter())
                .position(|(&own, &taken)| !taken && grid.at(own, argument).equal);
            if let Some(slot) = partner.and_then(|at| matched.get_mut(at)) {
                *slot = true;
            }
            partners.push(partner.map(Argument::from));
        }
        let dominated =
            self.right
                .arguments(column)
                .zip(partners.iter())
                .all(|(argument, partner)| {
                    partner.is_some()
                        || lefts
                            .iter()
                            .zip(matched.iter())
                            .any(|(&own, &taken)| !taken && grid.at(own, argument).above.is_some())
                });
        (dominated && matched.iter().any(|&taken| !taken)).then_some(())
    }

    /// The derivation of the filled table's root pair: each pair it reads,
    /// once, with its clause and covers, ordered by position.
    ///
    /// # Specification
    /// - requires: the table is filled and its root pair has a clause.
    /// - ensures: one step per pair the root's clause reaches through ordered
    ///   premises, each with the clause its cell records and, for a covering
    ///   clause, one cover per argument of its right subterm; the steps ordered
    ///   by left position, then right.
    /// - panics: none.
    /// - executable: none — [`orient`]'s predicate replays the derivation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`orient`]: every oriented witness's derivation
    ///   replays, so a missing premise or a misplaced cover is refused.
    /// - witness: `tests::lpo::a_descending_recursion_is_oriented_and_its_derivation_replays`
    fn derive(
        &self,
        buffers: &mut Buffers,
    ) -> Derivation
    {
        let columns = Columns(usize::from(self.right.end()));
        let &mut Buffers {
            ref mut table,
            ref mut reached,
            ref mut pending,
            ref mut scratch,
            ..
        } = buffers;
        let grid = Grid {
            cells: table,
            columns,
        };
        reached.clear();
        reached.resize(table.len(), false);
        pending.clear();
        pending.push((Node::from(0_usize), Node::from(0_usize)));
        let mut steps = Vec::new();
        let mut covers = Vec::new();
        while let Some((row, column)) = pending.pop() {
            let Some(slot) = index(row, column, columns).and_then(|at| reached.get_mut(at.0))
            else {
                continue;
            };
            if *slot {
                continue;
            }
            *slot = true;
            let Some(clause) = grid.at(row, column).above
            else {
                continue;
            };
            let first = CoverIndex::from(covers.len());
            match clause {
                Clause::Subterm { argument, relation } => {
                    if relation == Relation::Above
                        && let Some(own) = self.left.arguments(row).nth(usize::from(argument))
                    {
                        pending.push((own, column));
                    }
                },
                Clause::Multiset => {
                    if self.multiset(grid, scratch, row, column).is_some() {
                        for (argument, partner) in
                            self.right.arguments(column).zip(scratch.partners.iter())
                        {
                            let cover = partner
                                .map(|index| Cover::Argument {
                                    argument: index,
                                    relation: Relation::Equal,
                                })
                                .or_else(|| {
                                    scratch
                                        .lefts
                                        .iter()
                                        .zip(scratch.matched.iter())
                                        .position(|(&own, &taken)| {
                                            !taken && grid.at(own, argument).above.is_some()
                                        })
                                        .map(|index| Cover::Argument {
                                            argument: Argument::from(index),
                                            relation: Relation::Above,
                                        })
                                });
                            if let Some(cover) = cover {
                                self.premise(cover, row, argument, pending);
                                covers.push(cover);
                            }
                        }
                    }
                },
                Clause::Precedence | Clause::Lexicographic { .. } | Clause::Instance { .. } => {
                    if let Clause::Lexicographic { argument } = clause
                        && let Some(pair) = self.pairs(row, column).nth(usize::from(argument))
                    {
                        pending.push(pair);
                    }
                    for argument in self.right.arguments(column) {
                        let value = match clause {
                            Clause::Instance { .. } => self.valued(argument),
                            Clause::Subterm { .. }
                            | Clause::Precedence
                            | Clause::Lexicographic { .. }
                            | Clause::Multiset => None,
                        };
                        if let Some(cover) = value.or_else(|| self.covers(grid, row, argument)) {
                            self.premise(cover, row, argument, pending);
                            covers.push(cover);
                        }
                    }
                },
            }
            steps.push(Step::new(row, column, clause, first));
        }
        steps.sort_unstable_by_key(|step| (step.left(), step.right()));
        Derivation::new(steps, covers)
    }

    /// Queue the ordered premise `cover` reads of the left subterm at `row`
    /// and the right argument at `argument`, if it reads one.
    ///
    /// # Specification
    /// trivial.
    fn premise(
        &self,
        cover: Cover,
        row: Node,
        argument: Node,
        pending: &mut Vec<(Node, Node)>,
    )
    {
        match cover {
            Cover::Above => pending.push((row, argument)),
            Cover::Argument {
                argument: own,
                relation: Relation::Above,
            } => {
                if let Some(own) = self.left.arguments(row).nth(usize::from(own)) {
                    pending.push((own, argument));
                }
            },
            Cover::Argument {
                relation: Relation::Equal,
                ..
            }
            | Cover::Value => {},
        }
    }

    /// Replay `derivation`: the root step, then every step in order.
    ///
    /// # Specification
    /// trivial.
    fn replay(
        &self,
        derivation: &Derivation,
        buffers: &mut Buffers,
    ) -> Result<(), Refusal>
    {
        let &mut Buffers {
            ref mut functional,
            ref mut pending,
            ref mut scratch,
            ..
        } = buffers;
        self.mark_functional(functional);
        let root = Node::from(0_usize);
        if step_at(derivation, root, root).is_none() {
            return Err(Refusal::Root);
        }
        for &step in derivation.steps() {
            self.step_holds(derivation, functional, pending, scratch, step)
                .ok_or_else(|| Refusal::Step {
                    left: step.left(),
                    right: step.right(),
                })?;
        }
        Ok(())
    }

    /// Whether `step` holds of the two sides, its premises found in
    /// `derivation`.
    ///
    /// # Specification
    /// trivial.
    fn step_holds(
        &self,
        derivation: &Derivation,
        functional: &[Typing],
        pending: &mut Vec<(Node, Node)>,
        scratch: &mut Scratch,
        step: Step,
    ) -> Option<()>
    {
        let (row, column) = (step.left(), step.right());
        (row < self.left.end() && column < self.right.end()).then_some(())?;
        let comparable = matches!(
            self.left.former(row),
            Former::Symbol(_) | Former::Abstraction | Former::Bound(_)
        ) && functional.get(usize::from(column)) == Some(&Typing::Base);
        comparable.then_some(())?;
        match step.clause() {
            Clause::Subterm { argument, relation } => {
                let own = self.left.arguments(row).nth(usize::from(argument))?;
                self.related(derivation, pending, own, column, relation)
            },
            Clause::Precedence => {
                self.precedes(row, column)?;
                self.covered(derivation, pending, step, Coverage::Plain)
            },
            Clause::Lexicographic { argument } => {
                (self.one_head(row, column)? == Status::Lexicographic).then_some(())?;
                let mut pairs = self.pairs(row, column);
                for (one, two) in pairs.by_ref().take(usize::from(argument)) {
                    self.equal(pending, one, two)?;
                }
                let (one, two) = pairs.next()?;
                step_at(derivation, one, two)?;
                self.covered(derivation, pending, step, Coverage::Plain)
            },
            Clause::Multiset => {
                (self.one_head(row, column)? == Status::Multiset).then_some(())?;
                self.covered(derivation, pending, step, Coverage::Plain)?;
                self.matching(derivation, scratch, step)
            },
            Clause::Instance { held } => {
                let Former::Application(variable) = self.right.former(column)
                else {
                    return None;
                };
                let own = self.left.arguments(row).nth(usize::from(held))?;
                self.holds(own, variable)?;
                self.covered(derivation, pending, step, Coverage::Values)
            },
        }
    }

    /// Whether every argument of `step`'s right subterm has a cover the
    /// clause admits, each cover's premise holding.
    ///
    /// # Specification
    /// trivial.
    fn covered(
        &self,
        derivation: &Derivation,
        pending: &mut Vec<(Node, Node)>,
        step: Step,
        coverage: Coverage,
    ) -> Option<()>
    {
        let first = usize::from(step.first_cover());
        for (offset, argument) in self.right.arguments(step.right()).enumerate() {
            match *derivation.covers().get(first.checked_add(offset)?)? {
                Cover::Above => {
                    step_at(derivation, step.left(), argument)?;
                },
                Cover::Argument {
                    argument: own,
                    relation,
                } => {
                    let own = self.left.arguments(step.left()).nth(usize::from(own))?;
                    self.related(derivation, pending, own, argument, relation)?;
                },
                Cover::Value => {
                    (coverage == Coverage::Values).then_some(())?;
                    self.valued(argument)?;
                },
            }
        }
        Some(())
    }

    /// Whether a multiset step's covers are a multiset matching: each an own
    /// argument, the equal ones pairwise distinct, the ordered ones matched by
    /// no equality, and some own argument matched by none.
    ///
    /// # Specification
    /// trivial.
    fn matching(
        &self,
        derivation: &Derivation,
        scratch: &mut Scratch,
        step: Step,
    ) -> Option<()>
    {
        let matched = &mut scratch.matched;
        matched.clear();
        matched.resize(self.left.arguments(step.left()).count(), false);
        let count = self.right.arguments(step.right()).count();
        let first = usize::from(step.first_cover());
        let covers = derivation
            .covers()
            .get(first .. first.checked_add(count)?)?;
        for cover in covers {
            if let Cover::Argument {
                argument,
                relation: Relation::Equal,
            } = *cover
            {
                let slot = matched.get_mut(usize::from(argument))?;
                (!*slot).then_some(())?;
                *slot = true;
            }
        }
        for cover in covers {
            match *cover {
                Cover::Argument {
                    argument,
                    relation: Relation::Above,
                } => (!matched.get(usize::from(argument)).copied()?).then_some(())?,
                Cover::Argument {
                    relation: Relation::Equal,
                    ..
                } => {},
                Cover::Above | Cover::Value => return None,
            }
        }
        matched.iter().any(|&taken| !taken).then_some(())
    }

    /// Whether the left subterm at `own` stands to the right one at `column`
    /// as `relation` says.
    ///
    /// # Specification
    /// trivial.
    fn related(
        &self,
        derivation: &Derivation,
        pending: &mut Vec<(Node, Node)>,
        own: Node,
        column: Node,
        relation: Relation,
    ) -> Option<()>
    {
        match relation {
            Relation::Equal => self.equal(pending, own, column),
            Relation::Above => step_at(derivation, own, column).map(|_| ()),
        }
    }

    /// Whether the subterms at `one` and `two` are one term.
    ///
    /// # Specification
    /// trivial.
    fn equal(
        &self,
        pending: &mut Vec<(Node, Node)>,
        one: Node,
        two: Node,
    ) -> Option<()>
    {
        pending.clear();
        pending.push((one, two));
        while let Some((one, two)) = pending.pop() {
            (one < self.left.end() && two < self.right.end()).then_some(())?;
            self.one_head(one, two)?;
            pending.extend(self.pairs(one, two));
        }
        Some(())
    }
}

/// The step of `derivation` comparing the subterms at `left` and `right`.
///
/// # Specification
/// trivial.
fn step_at(
    derivation: &Derivation,
    left: Node,
    right: Node,
) -> Option<&Step>
{
    let steps = derivation.steps();
    let at = steps
        .binary_search_by_key(&(left, right), |step| (step.left(), step.right()))
        .ok()?;
    steps.get(at)
}
