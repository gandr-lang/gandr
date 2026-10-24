//! The lexicographic path order with status over toy sides spelled in
//! pre-order, and the replay of its derivations.

use alloc::vec::Vec;

use gandr_theory_path_orders::Argument;
use gandr_theory_path_orders::Clause;
use gandr_theory_path_orders::Cover;
use gandr_theory_path_orders::CoverIndex;
use gandr_theory_path_orders::Derivation;
use gandr_theory_path_orders::Evidence;
use gandr_theory_path_orders::Former;
use gandr_theory_path_orders::Node;
use gandr_theory_path_orders::Place;
use gandr_theory_path_orders::Precedence;
use gandr_theory_path_orders::Rank;
use gandr_theory_path_orders::Relation;
use gandr_theory_path_orders::Status;
use gandr_theory_path_orders::Step;
use gandr_theory_path_orders::Term;
use gandr_theory_path_orders::Valuation;
use gandr_theory_path_orders::Valued;
use gandr_theory_path_orders::lpo::Buffers;
use gandr_theory_path_orders::lpo::Orientation;
use gandr_theory_path_orders::lpo::Refusal;
use gandr_theory_path_orders::lpo::Replay;
use gandr_theory_path_orders::lpo::check;
use gandr_theory_path_orders::lpo::orient;

/// A toy symbol, by its spelling.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Symbol(char);

/// A toy rule variable, by its spelling.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Variable(char);

/// A toy bound occurrence, by the abstractions between it and its binder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bound(u8);

/// An argument count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Arity(usize);

/// One node of a side spelled in pre-order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spelled
{
    /// A symbol applied to the next subterms.
    Op(Symbol, Arity),
    /// A variable.
    Var(Variable),
    /// A variable instantiated at the next subterms.
    App(Variable, Arity),
    /// An abstraction over the next subterm.
    Lam,
    /// A bound occurrence.
    Occ(Bound),
}

impl Spelled
{
    /// How many subterms follow the node as its arguments.
    ///
    /// # Specification
    /// trivial.
    const fn width(self) -> Arity
    {
        match self {
            Self::Op(_, arity) | Self::App(_, arity) => arity,
            Self::Lam => Arity(1),
            Self::Var(_) | Self::Occ(_) => Arity(0),
        }
    }
}

/// A side spelled in pre-order, each node's subterm end beside it, and the
/// variables it values.
#[derive(Clone, Debug)]
struct Side
{
    /// The nodes.
    nodes: Vec<Spelled>,
    /// The end of the subterm at each position.
    ends: Vec<Node>,
    /// The values.
    values: Vec<Variable>,
}

impl Side
{
    /// The side `nodes` spell, valuing nothing.
    ///
    /// # Specification
    /// trivial.
    fn new(nodes: &[Spelled]) -> Self
    {
        let mut ends = alloc::vec![Node::from(0_usize); nodes.len()];
        for (position, node) in nodes.iter().enumerate().rev() {
            let mut end = position.saturating_add(1);
            for _ in 0 .. node.width().0 {
                end = ends.get(end).map_or(end, |&next| usize::from(next));
            }
            if let Some(slot) = ends.get_mut(position) {
                *slot = Node::from(end);
            }
        }
        Self {
            nodes: nodes.to_vec(),
            ends,
            values: Vec::new(),
        }
    }

    /// The side, valuing `values`.
    ///
    /// # Specification
    /// trivial.
    fn valuing(
        mut self,
        values: &[Variable],
    ) -> Self
    {
        self.values = values.to_vec();
        self
    }

    /// The node at `node`.
    ///
    /// # Specification
    /// trivial.
    fn node(
        &self,
        node: Node,
    ) -> Spelled
    {
        *self
            .nodes
            .get(usize::from(node))
            .expect("a position of the side")
    }
}

impl Term for Side
{
    type Bound = Bound;
    type Symbol = Symbol;
    type Variable = Variable;

    /// The side's node count.
    ///
    /// # Specification
    /// trivial.
    fn end(&self) -> Node
    {
        Node::from(self.nodes.len())
    }

    /// The spelled node's former.
    ///
    /// # Specification
    /// trivial.
    fn former(
        &self,
        node: Node,
    ) -> Former<Symbol, Variable, Bound>
    {
        match self.node(node) {
            Spelled::Op(symbol, _) => Former::Symbol(symbol),
            Spelled::Var(variable) => Former::Variable(variable),
            Spelled::App(variable, _) => Former::Application(variable),
            Spelled::Lam => Former::Abstraction,
            Spelled::Occ(bound) => Former::Bound(bound),
        }
    }

    /// The node's arguments, each found past the end of the one before it.
    ///
    /// # Specification
    /// trivial.
    fn arguments(
        &self,
        node: Node,
    ) -> impl Iterator<Item = Node> + Clone
    {
        let first = Node::from(usize::from(node).saturating_add(1));
        core::iter::successors(Some(first), |at| self.ends.get(usize::from(*at)).copied())
            .take(self.node(node).width().0)
    }
}

impl Valued for Side
{
    /// A listed variable is a value; every other is a term.
    ///
    /// # Specification
    /// trivial.
    fn valuation(
        &self,
        variable: Variable,
    ) -> Valuation
    {
        if self.values.contains(&variable) {
            Valuation::Value
        }
        else {
            Valuation::Term
        }
    }
}

/// A precedence: the listed symbols at their places and statuses, every
/// other symbol ground and lexicographic.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
struct Ranks(Vec<(Symbol, Place, Status)>);

impl Precedence for Ranks
{
    type Symbol = Symbol;

    /// The listed place, or ground.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &self,
        symbol: Symbol,
    ) -> Place
    {
        self.0
            .iter()
            .find(|&&(listed, ..)| listed == symbol)
            .map_or(Place::Ground, |&(_, place, _)| place)
    }

    /// The listed status, or lexicographic.
    ///
    /// # Specification
    /// trivial.
    fn status(
        &self,
        symbol: Symbol,
    ) -> Status
    {
        self.0
            .iter()
            .find(|&&(listed, ..)| listed == symbol)
            .map_or(Status::Lexicographic, |&(.., status)| status)
    }
}

const ADD: Symbol = Symbol('+');
const SUCC: Symbol = Symbol('s');
const F: Symbol = Symbol('f');
const LET: Symbol = Symbol('l');
const APP: Symbol = Symbol('@');
const LAM: Symbol = Symbol('λ');
const GET: Symbol = Symbol('g');
const PUT: Symbol = Symbol('p');
const C: Symbol = Symbol('c');

const X: Variable = Variable('x');
const Y: Variable = Variable('y');
const K: Variable = Variable('k');
const S: Variable = Variable('s');
const T: Variable = Variable('t');
const U: Variable = Variable('u');

/// The symbol `symbol` applied to the next `arity` subterms.
///
/// # Specification
/// trivial.
const fn op(
    symbol: Symbol,
    arity: Arity,
) -> Spelled
{
    Spelled::Op(symbol, arity)
}

/// The ranked place `rank`.
///
/// # Specification
/// trivial.
fn ranked(rank: Rank) -> Place
{
    Place::Ranked(rank)
}

/// The derivation an orientation returns.
///
/// # Specification
/// trivial.
fn derivation(orientation: Orientation) -> Derivation
{
    match orientation {
        Orientation::Oriented(Evidence::Path(derivation)) => derivation,
        Orientation::Unoriented => panic!("the order orients the pair"),
    }
}

/// The clause of the step at the two roots.
///
/// # Specification
/// trivial.
fn root_clause(derivation: &Derivation) -> Clause
{
    derivation
        .steps()
        .iter()
        .find(|step| step.left() == Node::from(0_usize) && step.right() == Node::from(0_usize))
        .expect("a root step")
        .clause()
}

/// `add(s(x), y) ==> s(add(x, y))` orients by precedence over a descending
/// first argument, the inner comparison lexicographic, and the derivation
/// replays; a swap of the arguments does not orient.
#[test]
fn a_descending_recursion_is_oriented_and_its_derivation_replays()
{
    let ranks = Ranks(alloc::vec![(
        ADD,
        ranked(Rank::from(1_u64)),
        Status::Lexicographic
    )]);
    let left = Side::new(&[
        op(ADD, Arity(2)),
        op(SUCC, Arity(1)),
        Spelled::Var(X),
        Spelled::Var(Y),
    ]);
    let right = Side::new(&[
        op(SUCC, Arity(1)),
        op(ADD, Arity(2)),
        Spelled::Var(X),
        Spelled::Var(Y),
    ]);
    let buffers = &mut Buffers::default();
    let derivation = derivation(orient(&left, &right, &ranks, buffers));
    assert_eq!(root_clause(&derivation), Clause::Precedence);
    assert!(
        derivation.steps().iter().any(|step| step.clause()
            == Clause::Lexicographic {
                argument: Argument::from(0_usize)
            }),
        "the left side is above the inner call by its first argument"
    );
    assert_eq!(
        check(&left, &right, &ranks, &derivation, buffers),
        Replay::Holds
    );
    let swapped = Side::new(&[op(ADD, Arity(2)), Spelled::Var(Y), Spelled::Var(X)]);
    let unswapped = Side::new(&[op(ADD, Arity(2)), Spelled::Var(X), Spelled::Var(Y)]);
    assert_eq!(
        orient(&unswapped, &swapped, &ranks, buffers),
        Orientation::Unoriented
    );
}

/// A variable is above nothing, a term is not above itself, and a term is
/// above its own argument.
#[test]
fn a_variable_or_an_equal_side_is_above_nothing()
{
    let ranks = Ranks::default();
    let buffers = &mut Buffers::default();
    let variable = Side::new(&[Spelled::Var(X)]);
    let successor = Side::new(&[op(SUCC, Arity(1)), Spelled::Var(X)]);
    assert_eq!(
        orient(&variable, &successor, &ranks, buffers),
        Orientation::Unoriented
    );
    assert_eq!(
        orient(&successor, &successor, &ranks, buffers),
        Orientation::Unoriented
    );
    let derivation = derivation(orient(&successor, &variable, &ranks, buffers));
    assert_eq!(root_clause(&derivation), Clause::Subterm {
        argument: Argument::from(0_usize),
        relation: Relation::Equal,
    });
}

/// `f(s(x), y) ==> f(y, x)` orients at multiset status, `y` matched by
/// equality and `x` below `s(x)`, and not at lexicographic status, where the
/// first pair decides and `s(x)` is not above `y`.
#[test]
fn multiset_status_orients_what_lexicographic_status_does_not()
{
    let left = Side::new(&[
        op(F, Arity(2)),
        op(SUCC, Arity(1)),
        Spelled::Var(X),
        Spelled::Var(Y),
    ]);
    let right = Side::new(&[op(F, Arity(2)), Spelled::Var(Y), Spelled::Var(X)]);
    let buffers = &mut Buffers::default();
    let multiset = Ranks(alloc::vec![(
        F,
        ranked(Rank::from(1_u64)),
        Status::Multiset
    )]);
    let derivation = derivation(orient(&left, &right, &multiset, buffers));
    assert_eq!(root_clause(&derivation), Clause::Multiset);
    assert_eq!(
        check(&left, &right, &multiset, &derivation, buffers),
        Replay::Holds
    );
    let lexicographic = Ranks(alloc::vec![(
        F,
        ranked(Rank::from(1_u64)),
        Status::Lexicographic
    )]);
    assert_eq!(
        orient(&left, &right, &lexicographic, buffers),
        Orientation::Unoriented
    );
}

/// `let(u, t) ==> t(u)` orients: `t` is an argument of the left side and `u`
/// is covered. β, `app(lam(t), u) ==> t(u)`, does not: `t` sits under the
/// symbol `lam`, which no argument of `app` is.
#[test]
fn an_instantiation_is_below_the_application_holding_its_variable()
{
    let ranks = Ranks(alloc::vec![
        (LET, ranked(Rank::from(1_u64)), Status::Lexicographic),
        (APP, ranked(Rank::from(1_u64)), Status::Lexicographic),
    ]);
    let buffers = &mut Buffers::default();
    let instance = Side::new(&[Spelled::App(T, Arity(1)), Spelled::Var(U)]);
    let binding = Side::new(&[op(LET, Arity(2)), Spelled::Var(U), Spelled::Var(T)]);
    let derivation = derivation(orient(&binding, &instance, &ranks, buffers));
    assert_eq!(root_clause(&derivation), Clause::Instance {
        held: Argument::from(1_usize),
    });
    assert_eq!(
        check(&binding, &instance, &ranks, &derivation, buffers),
        Replay::Holds
    );
    let beta = Side::new(&[
        op(APP, Arity(2)),
        op(LAM, Arity(1)),
        Spelled::Var(T),
        Spelled::Var(U),
    ]);
    assert_eq!(
        orient(&beta, &instance, &ranks, buffers),
        Orientation::Unoriented
    );
}

/// `get(bind b . k(b)) ==> k(c)` orients: the argument holds `k` under the
/// abstraction of the name it is applied to, and `get` precedes `c`. `get(k)`
/// holds it bare. Under a symbol between the abstraction and the
/// instantiation, it is not held.
#[test]
fn a_pattern_under_its_abstraction_holds_its_variable()
{
    let ranks = Ranks(alloc::vec![(
        GET,
        ranked(Rank::from(1_u64)),
        Status::Lexicographic
    )]);
    let buffers = &mut Buffers::default();
    let instance = Side::new(&[Spelled::App(K, Arity(1)), op(C, Arity(0))]);
    let pattern = Side::new(&[
        op(GET, Arity(1)),
        Spelled::Lam,
        Spelled::App(K, Arity(1)),
        Spelled::Occ(Bound(0)),
    ]);
    let derivation = derivation(orient(&pattern, &instance, &ranks, buffers));
    assert_eq!(root_clause(&derivation), Clause::Instance {
        held: Argument::from(0_usize),
    });
    assert_eq!(
        check(&pattern, &instance, &ranks, &derivation, buffers),
        Replay::Holds
    );
    let bare = Side::new(&[op(GET, Arity(1)), Spelled::Var(K)]);
    assert!(matches!(
        orient(&bare, &instance, &ranks, buffers),
        Orientation::Oriented(_)
    ));
    let wrapped = Side::new(&[
        op(GET, Arity(1)),
        Spelled::Lam,
        op(F, Arity(1)),
        Spelled::App(K, Arity(1)),
        Spelled::Occ(Bound(0)),
    ]);
    assert_eq!(
        orient(&wrapped, &instance, &ranks, buffers),
        Orientation::Unoriented
    );
}

/// `put(s, get(bind b . k(b))) ==> put(s, k(s))` orients while `s` is a
/// value, which the instantiation needs no cover of, and not otherwise.
#[test]
fn a_value_needs_no_cover()
{
    let ranks = Ranks(alloc::vec![
        (PUT, ranked(Rank::from(2_u64)), Status::Lexicographic),
        (GET, ranked(Rank::from(1_u64)), Status::Lexicographic),
    ]);
    let buffers = &mut Buffers::default();
    let spelled = [
        op(PUT, Arity(2)),
        Spelled::Var(S),
        op(GET, Arity(1)),
        Spelled::Lam,
        Spelled::App(K, Arity(1)),
        Spelled::Occ(Bound(0)),
    ];
    let right = Side::new(&[
        op(PUT, Arity(2)),
        Spelled::Var(S),
        Spelled::App(K, Arity(1)),
        Spelled::Var(S),
    ]);
    let valued = Side::new(&spelled).valuing(&[S]);
    let derivation = derivation(orient(&valued, &right, &ranks, buffers));
    assert_eq!(root_clause(&derivation), Clause::Lexicographic {
        argument: Argument::from(1_usize),
    });
    assert!(derivation.covers().contains(&Cover::Value));
    assert_eq!(
        check(&valued, &right, &ranks, &derivation, buffers),
        Replay::Holds
    );
    assert_eq!(
        orient(&Side::new(&spelled), &right, &ranks, buffers),
        Orientation::Unoriented
    );
}

/// An instantiation on the left is above nothing, not even its own argument:
/// a substitution can make it any term.
#[test]
fn an_instantiation_on_the_left_is_above_nothing()
{
    let ranks = Ranks::default();
    let buffers = &mut Buffers::default();
    let instance = Side::new(&[Spelled::App(K, Arity(1)), op(C, Arity(0))]);
    let constant = Side::new(&[op(C, Arity(0))]);
    assert_eq!(
        orient(&instance, &constant, &ranks, buffers),
        Orientation::Unoriented
    );
}

/// A ranked symbol precedes an abstraction and a bound occurrence, as it does
/// a ground symbol; a ground symbol precedes neither.
#[test]
fn an_abstraction_and_a_bound_occurrence_stand_where_a_ground_symbol_does()
{
    let ranks = Ranks(alloc::vec![(
        F,
        ranked(Rank::from(1_u64)),
        Status::Lexicographic
    )]);
    let buffers = &mut Buffers::default();
    let abstraction = Side::new(&[Spelled::Lam, Spelled::Occ(Bound(0))]);
    let ranked_left = Side::new(&[op(F, Arity(1)), Spelled::Var(X)]);
    let derivation = derivation(orient(&ranked_left, &abstraction, &ranks, buffers));
    assert_eq!(root_clause(&derivation), Clause::Precedence);
    assert_eq!(
        check(&ranked_left, &abstraction, &ranks, &derivation, buffers),
        Replay::Holds
    );
    let ground_left = Side::new(&[op(C, Arity(1)), Spelled::Var(X)]);
    assert_eq!(
        orient(&ground_left, &abstraction, &ranks, buffers),
        Orientation::Unoriented
    );
}

/// A derivation is replayed, never trusted: without its root step it is
/// refused at the root; with the root's clause swapped for one whose
/// conditions fail, or with a premise step removed, it is refused at the root
/// step; a step forged over an unoriented pair is refused.
#[test]
fn a_forged_derivation_is_refused()
{
    let ranks = Ranks(alloc::vec![(
        ADD,
        ranked(Rank::from(1_u64)),
        Status::Lexicographic
    )]);
    let left = Side::new(&[
        op(ADD, Arity(2)),
        op(SUCC, Arity(1)),
        Spelled::Var(X),
        Spelled::Var(Y),
    ]);
    let right = Side::new(&[
        op(SUCC, Arity(1)),
        op(ADD, Arity(2)),
        Spelled::Var(X),
        Spelled::Var(Y),
    ]);
    let buffers = &mut Buffers::default();
    let honest = derivation(orient(&left, &right, &ranks, buffers));
    let root = Node::from(0_usize);
    let at_root = Replay::Refused(Refusal::Step {
        left: root,
        right: root,
    });
    let without = |keep: &dyn Fn(&Step) -> bool| {
        Derivation::new(
            honest
                .steps()
                .iter()
                .copied()
                .filter(|step| keep(step))
                .collect(),
            honest.covers().to_vec(),
        )
    };
    let rootless = without(&|step| step.left() != root || step.right() != root);
    assert_eq!(
        check(&left, &right, &ranks, &rootless, buffers),
        Replay::Refused(Refusal::Root)
    );
    let swapped = Derivation::new(
        honest
            .steps()
            .iter()
            .map(|&step| {
                if step.left() == root && step.right() == root {
                    Step::new(
                        root,
                        root,
                        Clause::Subterm {
                            argument: Argument::from(0_usize),
                            relation: Relation::Equal,
                        },
                        step.first_cover(),
                    )
                }
                else {
                    step
                }
            })
            .collect(),
        honest.covers().to_vec(),
    );
    assert_eq!(check(&left, &right, &ranks, &swapped, buffers), at_root);
    let premiseless = without(&|step| step.left() != root || step.right() != Node::from(1_usize));
    assert_eq!(check(&left, &right, &ranks, &premiseless, buffers), at_root);
    let unswapped = Side::new(&[op(ADD, Arity(2)), Spelled::Var(X), Spelled::Var(Y)]);
    let swapped_side = Side::new(&[op(ADD, Arity(2)), Spelled::Var(Y), Spelled::Var(X)]);
    let forged = Derivation::new(
        alloc::vec![Step::new(
            root,
            root,
            Clause::Precedence,
            CoverIndex::from(0_usize)
        )],
        alloc::vec![
            Cover::Argument {
                argument: Argument::from(1_usize),
                relation: Relation::Equal,
            },
            Cover::Argument {
                argument: Argument::from(0_usize),
                relation: Relation::Equal,
            },
        ],
    );
    assert_eq!(
        check(&unswapped, &swapped_side, &ranks, &forged, buffers),
        at_root
    );
}
