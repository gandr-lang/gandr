//! Termination of a description's rules: the lexicographic path order over its
//! faces read as first-order rewrite rules.
//!
//! A description's rules are read twice: the operation route compiles them to
//! a first-match decision tree, and the cell layer reads them as equations
//! between commands. The two readings agree on every term when the rules
//! terminate and every critical pair joins — Newman's lemma with the
//! critical-pair lemma — and this module decides the first half;
//! the cell layer's joinability check decides the second.
//!
//! # The order
//!
//! [`orient_rules`] compares each face's two sides by the lexicographic path
//! order over the precedence the description's own calls induce
//! ([`Precedence`]): every operation stands above every constructor and above
//! the results tuple, an operation above every other operation its rules call,
//! directly or through others, and an operation the description does not
//! declare above no operation it declares. Arguments of one symbol compare
//! left to right. The order is a simplification order, so a face it orients
//! decreases every term the face rewrites, in any context, and a description
//! all of whose faces it orients terminates. [`path_greater`] is the order on
//! two terms.
//!
//! **Choice.** A path order over the written faces, with the least precedence
//! the faces need. A face's left side applies an operation to constructor
//! patterns, so no argument of it holds an operation, and the order can put it
//! above a call to another operation only through the precedence: every
//! operation a face calls must rank below the operation it defines. The call
//! graph's transitive closure is therefore the least precedence any orienting
//! one contains, and since the order only grows with its precedence, ranking
//! the call graph's levels decides exactly whether some strict precedence
//! orients the faces. Recursion on a descending first argument, and a call to
//! a helper declared before or after the caller, are oriented as written.
//! **Alternative.** The cell layer's reduction order, which compares whole
//! commands with the cut above every frame. It lost because it orients
//! completion's derived cells and was never a termination proof for a store
//! holding polarity-derived cells: on the two-output division family it leaves
//! three of five rules unoriented — `divmod(m, Zero) ==> (Zero, m)` compares
//! equal, and `divmod(m, Succ(d)) ==> walk(m, d, d, Zero, Zero)` compares
//! below, because the command order does not know `divmod` calls `walk`.
//! Declaration order as the precedence, the operation route's own rule for
//! which call compiles, lost because it refuses a family that calls a helper
//! declared after the caller, which terminates and which the route merely
//! declines to compile.
//! **Reversal.** A rule a terminating program writes that this order cannot
//! orient — mutual recursion, which needs two operations of one rank, or an
//! argument that descends in a later position while an earlier one grows —
//! wants a quasi-precedence with multiset or permuted status per operation,
//! added beside the call graph rather than instead of it.
//!
//! # Second-order rules
//!
//! A variable a rule's right side instantiates, as `t(u)`, is a metavariable:
//! a term of a function type, one argument per variable the binding port that
//! binds it on the left binds. [`path_greater`] is then the higher-order
//! recursive path order of Jouannaud and Rubio restricted to patterns: every
//! other term has the one base type, and a base term is above no
//! metavariable; a term covers a right-side argument when it is above it or
//! one of its own arguments is equal to or above it, and an application is
//! above an instantiation `X(ū)` when `X` is one of its arguments and it
//! covers every one of `ū`. A rule that instantiates nothing compares exactly
//! as under the lexicographic path order: its variables are replaced, never
//! applied, so it rewrites as a first-order rule does. `let(u, t) ==> t(u)` is
//! oriented: `t` and `u` are both arguments of the left side. β,
//! `app(lam(t), u) ==> t(u)`, is not: `t` sits under `lam`, and no argument of
//! `app` is or covers it, so a theory writing it is refused as
//! non-terminating. The kernel reads metavariables the same way.
//!
//! # From faces to cells
//!
//! The cell store's rewriting is the faces' rewriting read through the command
//! encoding. A command `⟨p | c⟩` denotes the term `c[p]`: an operation frame
//! `f(q̄; κ)` contributes `κ[f(p, q̄)]` and a return-side frame `K⁻(κ)`
//! contributes `κ[K(p)]`. A face cell rewrites the command exactly as its face
//! rewrites the term it denotes; a constructor's frame cell moves the
//! constructor from the consumer to the producer and leaves the term it
//! denotes unchanged, and frame moves alone end because each shrinks the
//! consumer; an η cell denotes `K(f(w)) ==> w`, which the subterm property
//! orients under any precedence. Every face step therefore descends in the
//! order and every other step leaves the term fixed while the consumer
//! shrinks, so a store whose faces the order orients terminates.
//!
//! # References
//!
//! - Sam Kamin and Jean-Jacques Lévy. "Two Generalizations of the Recursive
//!   Path Ordering." Unpublished note, University of Illinois, 1980 — the
//!   lexicographic path order.
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998, § 5.4 — the order's definition, its
//!   simplification-order property, and the critical-pair lemma.
//! - Jean-Pierre Jouannaud and Albert Rubio. "The Higher-Order Recursive Path
//!   Ordering." LICS 1999 — the order on instantiations of metavariables.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::boundary::PathOrderStatus;
use crate::boundary::RuleIndex;
use crate::code::Name;
use crate::desc::OperDesc;
use crate::desc::TheoryDesc;
use crate::rule::FreeTerm;
use crate::rule::TermView;

/// How a description's rule faces stand under the path order.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Termination
{
    /// The order orients every face, so the rules terminate.
    Oriented,
    /// The first face, by its index among the description's rules, whose
    /// left-hand side the order does not put above its right-hand side.
    Unoriented(RuleIndex),
}

/// Orient every rule face of `desc` by the lexicographic path order over the
/// precedence its calls induce.
///
/// # Specification
/// - ensures: [`Termination::Oriented`] exactly when [`path_greater`] over
///   [`Precedence::of`] `desc` puts every face's left-hand side above its
///   right-hand side; otherwise the first face, in rule order, it does not.
/// - panics: none.
/// - intension: one precedence, then one [`path_greater`] table per face,
///   stopping at the first unoriented one.
///
/// # Adequacy
/// - hypothesis: L3 — the addition and two-output division families are
///   oriented as written, a call to a helper is oriented whichever of the two
///   is declared first, a rule that rebuilds its own call under a constructor,
///   a pair of mutually recursive operations and a call to an operation the
///   family does not declare are unoriented, and the index names the first such
///   rule; a precedence read from declaration order, or an index off by one,
///   changes a verdict.
/// - witness: `termination::tests::recursion_on_a_descending_argument_is_oriented`
/// - witness: `termination::tests::a_call_ranks_its_caller_above_its_callee_in_either_declaration_order`
/// - witness: `termination::tests::a_growing_rule_is_the_first_unoriented_one`
#[spec(ensures: |ret| {
    let precedence = Precedence::of(desc);
    match ret {
        Termination::Oriented => desc.rules.iter().all(|face| bool::from(path_greater(&precedence, &face.lhs, &face.rhs))),
        Termination::Unoriented(index) => desc.rules.get(usize::from(index))
            .is_some_and(|face| !bool::from(path_greater(&precedence, &face.lhs, &face.rhs)))
            && desc.rules.iter().take(usize::from(index)).all(|face| bool::from(path_greater(&precedence, &face.lhs, &face.rhs))),
    }
})]
#[inline]
#[must_use]
pub fn orient_rules<G>(desc: &TheoryDesc<G>) -> Termination
{
    orient_rules_with(desc, &[], &[])
}

/// Orient every rule face of `desc` and every rewrite of `ranking` and
/// `riding` by the lexicographic path order over the precedence `desc` and
/// `ranking` induce.
///
/// The check a rule a completion derives passes beside the rules it was
/// derived from. A rewrite of `ranking` raises its head above what it calls; a
/// rewrite of `riding` is oriented by the precedence the others induce and
/// adds nothing to it.
///
/// # Specification
/// - ensures: [`Termination::Oriented`] exactly when [`path_greater`] over
///   [`Precedence::with`] `desc` and `ranking` puts every left side above its
///   right side, `desc`'s rules, then `ranking`, then `riding`; otherwise the
///   first rule it does not, indexed in that order.
/// - panics: none.
/// - intension: one precedence, then one [`path_greater`] table per rule,
///   stopping at the first unoriented one.
///
/// # Adequacy
/// - hypothesis: L3 — a ranking rule calling an operation its head did not call
///   before raises the head above the callee and orients, a derived rule naming
///   a variable its left side does not bind is unoriented at its index past the
///   written rules, a ranking call closing a call cycle ranks both operations
///   alike and unorients the written rule that ranked them apart, and the same
///   rule riding the written precedence orients by the subterm property;
///   reading the precedence from the written rules alone, counting a riding
///   rule's calls, or indexing the derived rules from zero, changes a verdict.
/// - witness: `termination::tests::a_derived_rule_raises_its_head_above_what_it_calls`
#[spec(ensures: |ret| {
    let precedence = Precedence::with(desc, ranking);
    let mut rules = sides(desc, ranking).chain(pairs(riding));
    match ret {
        Termination::Oriented => rules.all(|(lhs, rhs)| bool::from(path_greater(&precedence, lhs, rhs))),
        Termination::Unoriented(index) => rules.clone().nth(usize::from(index))
            .is_some_and(|(lhs, rhs)| !bool::from(path_greater(&precedence, lhs, rhs)))
            && rules.take(usize::from(index)).all(|(lhs, rhs)| bool::from(path_greater(&precedence, lhs, rhs))),
    }
})]
#[inline]
#[must_use]
pub fn orient_rules_with<G>(
    desc: &TheoryDesc<G>,
    ranking: &[(FreeTerm, FreeTerm)],
    riding: &[(FreeTerm, FreeTerm)],
) -> Termination
{
    let precedence = Precedence::with(desc, ranking);
    let rules = sides(desc, ranking).chain(pairs(riding));
    for (index, (lhs, rhs)) in rules.enumerate() {
        if !bool::from(path_greater(&precedence, lhs, rhs)) {
            return Termination::Unoriented(RuleIndex::from(index));
        }
    }
    Termination::Oriented
}

/// The two sides of every rule face of `desc`, then of every rewrite of
/// `derived`.
///
/// # Specification
/// trivial.
fn sides<'rules, G>(
    desc: &'rules TheoryDesc<G>,
    derived: &'rules [(FreeTerm, FreeTerm)],
) -> impl Iterator<Item = (&'rules FreeTerm, &'rules FreeTerm)> + Clone
{
    desc.rules
        .iter()
        .map(|face| (&face.lhs, &face.rhs))
        .chain(pairs(derived))
}

/// The two sides of every rewrite of `rules`.
///
/// # Specification
/// trivial.
fn pairs(rules: &[(FreeTerm, FreeTerm)]) -> impl Iterator<Item = (&FreeTerm, &FreeTerm)> + Clone
{
    rules.iter().map(|&(ref lhs, ref rhs)| (lhs, rhs))
}

/// The precedence a description's faces induce over its operations: each
/// operation ranks one above the highest operation its faces call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Precedence<'desc>
{
    /// The declared operations.
    opers: &'desc [OperDesc],
    /// Each declared operation's rank, in declaration order; zero for an
    /// operation on a call cycle or calling into one.
    ranks: Vec<Rank>,
}

impl<'desc> Precedence<'desc>
{
    /// The precedence `desc`'s faces induce.
    ///
    /// # Specification
    /// - ensures: [`Precedence::with`] `desc` and no derived face.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Precedence::with`].
    /// - witness: `termination::tests::a_call_ranks_its_caller_above_its_callee_in_either_declaration_order`
    #[spec(ensures: |ret| ret.ranks.len() == desc.opers.len())]
    #[inline]
    #[must_use]
    pub fn of<G>(desc: &'desc TheoryDesc<G>) -> Self
    {
        Self::with(desc, &[])
    }

    /// The precedence `desc`'s faces and the rewrites of `ranking` induce
    /// together.
    ///
    /// # Specification
    /// - ensures: one rank per declared operation; an operation calling no
    ///   other declared operation ranks one, an operation whose faces call
    ///   other declared operations ranks one above the highest of them, and an
    ///   operation on a call cycle, or calling into one, ranks zero, as an
    ///   undeclared operation does. A call is an operation other than the
    ///   face's own anywhere in its right-hand side; a face defining an
    ///   undeclared operation induces nothing; a rewrite of `ranking` calls as
    ///   a written face does.
    /// - panics: none.
    /// - intension: callees counted per operation, then ranked leaves first, an
    ///   operation ranked once its last callee is.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`orient_rules`]: a helper declared after its
    ///   caller ranks below it, and two operations calling each other rank
    ///   alike; ranking by declaration position, or leaving a cycle's
    ///   operations distinct, changes a witnessed verdict. As
    ///   [`orient_rules_with`]: a ranking call raises its caller.
    /// - witness: `termination::tests::a_call_ranks_its_caller_above_its_callee_in_either_declaration_order`
    /// - witness: `termination::tests::a_derived_rule_raises_its_head_above_what_it_calls`
    #[spec(ensures: |ret| ret.ranks.len() == desc.opers.len())]
    #[inline]
    #[must_use]
    pub fn with<G>(
        desc: &'desc TheoryDesc<G>,
        ranking: &[(FreeTerm, FreeTerm)],
    ) -> Self
    {
        let count = desc.opers.len();
        let declared = |name: &Name| {
            desc.opers
                .iter()
                .position(|operation| operation.name == *name)
        };
        let mut callees: Vec<Vec<usize>> = vec![Vec::new(); count];
        for (lhs, rhs) in sides(desc, ranking) {
            let TermView::Op { name, .. } = lhs.view()
            else {
                continue;
            };
            let Some(caller) = declared(name)
            else {
                continue;
            };
            for node in flatten(rhs) {
                if let Symbol::Op(name) = node.symbol
                    && let Some(callee) = declared(name)
                    && callee != caller
                    && let Some(called) = callees.get_mut(caller)
                    && !called.contains(&callee)
                {
                    called.push(callee);
                }
            }
        }
        let mut callers: Vec<Vec<usize>> = vec![Vec::new(); count];
        for (caller, called) in callees.iter().enumerate() {
            for &callee in called {
                if let Some(waiting) = callers.get_mut(callee) {
                    waiting.push(caller);
                }
            }
        }
        let mut unranked: Vec<usize> = callees.iter().map(Vec::len).collect();
        let mut ready: Vec<usize> = (0 .. count)
            .filter(|&operation| unranked.get(operation) == Some(&0))
            .collect();
        let mut ranks = vec![Rank::default(); count];
        while let Some(operation) = ready.pop() {
            let highest = callees
                .get(operation)
                .into_iter()
                .flatten()
                .filter_map(|&callee| ranks.get(callee).copied())
                .max()
                .unwrap_or_default();
            if let Some(rank) = ranks.get_mut(operation) {
                *rank = Rank(highest.0.saturating_add(1));
            }
            for &caller in callers.get(operation).into_iter().flatten() {
                if let Some(left) = unranked.get_mut(caller) {
                    *left = left.saturating_sub(1);
                    if *left == 0 {
                        ready.push(caller);
                    }
                }
            }
        }
        Self {
            opers: &desc.opers,
            ranks,
        }
    }

    /// An operation's rank, or the lowest for one the description does not
    /// declare.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        name: &Name,
    ) -> Rank
    {
        self.opers
            .iter()
            .position(|operation| operation.name == *name)
            .and_then(|position| self.ranks.get(position).copied())
            .unwrap_or_default()
    }

    /// Each declared operation's name and rank, in declaration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn ranks(&self) -> impl Iterator<Item = (&'desc Name, Rank)> + '_
    {
        self.opers
            .iter()
            .zip(self.ranks.iter().copied())
            .map(|(operation, rank)| (&operation.name, rank))
    }
}

/// An operation's place in a [`Precedence`]: above every operation of a lower
/// rank, and beside every operation of its own.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rank(usize);

impl From<usize> for Rank
{
    /// The rank `rank`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: usize) -> Self
    {
        Self(rank)
    }
}

impl From<Rank> for usize
{
    /// The rank's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: Rank) -> Self
    {
        rank.0
    }
}

/// Whether the higher-order recursive path order over `precedence` puts
/// `left` above `right`: the lexicographic path order, with the variables
/// `right` instantiates read as metavariables.
///
/// # Specification
/// - ensures: negative when `right` is a metavariable. Otherwise positive
///   exactly when `left` is an application and some argument of it is equal to
///   or above `right`; or `right` is an application every argument of which
///   `left` covers, and either `left`'s symbol precedes `right`'s or the two
///   share a symbol and the first argument pair that differs, left to right, is
///   in the order; or `right` instantiates a metavariable that is an argument
///   of `left`, and `left` covers every argument of the instantiation. `left`
///   covers a term it is above, or one of its own arguments is equal to or
///   above.
/// - ensures: a variable is above nothing, and no term is above itself.
/// - panics: none.
/// - intension: one table of every argument pair of the two terms, filled from
///   the leaves up, so no comparison recurses.
///
/// # Adequacy
/// - hypothesis: L3 — the subterm, precedence and lexicographic cases each
///   decide a witness: a variable occurring below the left side, an operation
///   over a constructor wrapping a smaller call, and a recursion on a
///   descending first argument; an equal pair, a variable on the left and a
///   variable absent from the left side are not in the order. Swapping the
///   table's sweep direction, comparing arguments right to left or dropping the
///   dominance check changes one of them. A `let` instantiating its own
///   argument is above the instantiation and β is not; reading every variable
///   at base type orients β, and dropping the instantiation case refuses `let`.
/// - witness: `termination::tests::recursion_on_a_descending_argument_is_oriented`
/// - witness: `termination::tests::the_order_is_irreflexive_and_reads_variables_by_occurrence`
/// - witness: `termination::tests::an_instantiation_is_below_the_application_that_binds_its_metavariable`
#[spec(ensures: |ret| !bool::from(ret) || (left != right && !matches!(left.view(), TermView::Var(_))))]
#[inline]
#[must_use]
pub fn path_greater(
    precedence: &Precedence<'_>,
    left: &FreeTerm,
    right: &FreeTerm,
) -> PathOrderStatus
{
    let above = flatten(left);
    let below = flatten(right);
    let metavariables = metavariables(&below);
    let higher =
        |node: &Node<'_>| matches!(node.symbol, Symbol::Var(name) if metavariables.contains(name));
    let mut table = Table::new(&above, &below);
    let precedes = |above: Symbol<'_>, below: Symbol<'_>| match (above, below) {
        (Symbol::Op(_), Symbol::Ctor(_) | Symbol::Results) => true,
        (Symbol::Op(left), Symbol::Op(right)) => precedence.rank(left) > precedence.rank(right),
        _ => false,
    };
    // The first argument pair that differs, left to right, decides two
    // applications of one symbol.
    let lexicographic = |table: &Table, node: &Node<'_>, other: &Node<'_>| {
        node.arguments()
            .zip(other.arguments())
            .map(|(left, right)| table.at(left, right))
            .find(|pair| !pair.equal)
            .is_some_and(|pair| pair.greater)
    };
    // A node covers a right-side node it is above, or one of its own
    // arguments is equal to or above: the comparison a metavariable passed
    // bare takes, which no base term is above.
    let covers = |table: &Table, node: &Node<'_>, row: At, column: At| {
        table.at(row, column).greater
            || node.arguments().any(|argument| {
                let pair = table.at(argument, column);
                pair.equal || pair.greater
            })
    };
    for (row, node) in above.iter().enumerate().rev() {
        for (column, other) in below.iter().enumerate().rev() {
            let (row, column) = (At(row), At(column));
            let same = node.symbol == other.symbol && node.arity == other.arity;
            let equal = same
                && node
                    .arguments()
                    .zip(other.arguments())
                    .all(|(left, right)| table.at(left, right).equal);
            let greater = !matches!(node.symbol, Symbol::Var(_))
                && !higher(other)
                && (node.arguments().any(|argument| {
                    let pair = table.at(argument, column);
                    pair.equal || pair.greater
                }) || match other.symbol {
                    Symbol::Var(_) => false,
                    Symbol::Inst(name) => {
                        node.arguments().any(|argument| {
                            above
                                .get(argument.0)
                                .is_some_and(|bound| bound.symbol == Symbol::Var(name))
                        }) && other
                            .arguments()
                            .all(|argument| covers(&table, node, row, argument))
                    },
                    Symbol::Ctor(_) | Symbol::Op(_) | Symbol::Results => {
                        other
                            .arguments()
                            .all(|argument| covers(&table, node, row, argument))
                            && if same {
                                lexicographic(&table, node, other)
                            }
                            else {
                                precedes(node.symbol, other.symbol)
                            }
                    },
                });
            table.set(row, column, Comparison { equal, greater });
        }
    }
    PathOrderStatus::from(table.at(At(0), At(0)).greater)
}

/// The variables `nodes` instantiates: the metavariables of a rule whose right
/// side `nodes` is.
///
/// # Specification
/// - ensures: exactly the names of the instantiations among `nodes`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`path_greater`]: reading no metavariable orients β,
///   which the witness refuses.
/// - witness: `termination::tests::an_instantiation_is_below_the_application_that_binds_its_metavariable`
#[spec(ensures: |ret| ret.iter().all(|name| nodes.iter().any(|node| node.symbol == Symbol::Inst(name))))]
fn metavariables<'term>(nodes: &[Node<'term>]) -> BTreeSet<&'term Name>
{
    nodes
        .iter()
        .filter_map(|node| match node.symbol {
            Symbol::Inst(name) => Some(name),
            Symbol::Var(_) | Symbol::Ctor(_) | Symbol::Op(_) | Symbol::Results => None,
        })
        .collect()
}

/// What a node of a flattened term applies.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Symbol<'term>
{
    /// A pattern variable.
    Var(&'term Name),
    /// A constructor.
    Ctor(&'term Name),
    /// An operation.
    Op(&'term Name),
    /// A results tuple.
    Results,
    /// A metavariable's instantiation.
    Inst(&'term Name),
}

/// One node of a term read breadth first: what it applies, how many
/// arguments it takes, and where they start.
#[derive(Clone, Copy, Debug)]
struct Node<'term>
{
    /// The applied symbol.
    symbol: Symbol<'term>,
    /// The argument count.
    arity: usize,
    /// The position of the first argument; the rest follow it.
    first: usize,
}

/// `term`'s nodes breadth first: each node's arguments are adjacent and come
/// after it.
///
/// # Specification
/// - ensures: one node per term node, the root first; every node's arguments
///   occupy `first .. first + arity`, each past the node itself.
/// - panics: none.
/// - intension: one pass, the visit order doubling as the queue.
///
/// # Adequacy
/// - hypothesis: L3 — as [`path_greater`]: a misplaced argument range compares
///   the wrong pairs and changes a witnessed verdict.
/// - witness: `termination::tests::recursion_on_a_descending_argument_is_oriented`
#[spec(ensures: |ret| !ret.is_empty() && ret.iter().enumerate().all(|(position, node)|
    node.arity == 0 || (node.first > position && node.first.saturating_add(node.arity) <= ret.len())))]
fn flatten(term: &FreeTerm) -> Vec<Node<'_>>
{
    let mut visit = vec![term.to_node()];
    let mut nodes = Vec::new();
    let mut next = 0_usize;
    while let Some(&current) = visit.get(next) {
        let first = visit.len();
        let (symbol, arguments) = match current.view() {
            TermView::Var(name) => (Symbol::Var(name), None),
            TermView::Ctor { name, args } => (Symbol::Ctor(name), Some(args)),
            TermView::Op { name, args } => (Symbol::Op(name), Some(args)),
            TermView::Results { args } => (Symbol::Results, Some(args)),
            TermView::Inst { name, args } => (Symbol::Inst(name), Some(args)),
        };
        let arity = arguments.map_or(0, |arguments| {
            let count = arguments.len();
            visit.extend(arguments);
            count
        });
        nodes.push(Node {
            symbol,
            arity,
            first,
        });
        next = next.saturating_add(1);
    }
    nodes
}

impl Node<'_>
{
    /// The positions of the node's arguments, left to right.
    ///
    /// # Specification
    /// trivial.
    fn arguments(&self) -> impl Iterator<Item = At>
    {
        (self.first .. self.first.saturating_add(self.arity)).map(At)
    }
}

/// A node's position in a flattened term.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct At(usize);

/// How one node of the left term compares with one of the right.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Comparison
{
    /// The two subterms are equal.
    equal: bool,
    /// The left subterm is above the right in the order.
    greater: bool,
}

/// The comparison table of two flattened terms: how each node of the first
/// compares with each node of the second.
#[derive(Clone, Debug)]
struct Table
{
    /// The second term's node count.
    columns: usize,
    /// The comparisons, row by row.
    pairs: Vec<Comparison>,
}

impl Table
{
    /// A table of `above`'s nodes by `below`'s, no pair yet equal or ordered.
    ///
    /// # Specification
    /// trivial.
    fn new(
        above: &[Node<'_>],
        below: &[Node<'_>],
    ) -> Self
    {
        Self {
            columns: below.len(),
            pairs: vec![Comparison::default(); above.len().saturating_mul(below.len())],
        }
    }

    /// How the pair at `row` and `column` compares.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        row: At,
        column: At,
    ) -> Comparison
    {
        self.pairs
            .get(row.0.saturating_mul(self.columns).saturating_add(column.0))
            .copied()
            .unwrap_or_default()
    }

    /// Record how the pair at `row` and `column` compares.
    ///
    /// # Specification
    /// trivial.
    fn set(
        &mut self,
        row: At,
        column: At,
        comparison: Comparison,
    )
    {
        let at = row.0.saturating_mul(self.columns).saturating_add(column.0);
        if let Some(slot) = self.pairs.get_mut(at) {
            *slot = comparison;
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;
    use crate::arity::BridgeArity;
    use crate::arity::SortRef;
    use crate::boundary::NominalSerial;
    use crate::code::Attrs;
    use crate::code::Code;
    use crate::desc::CtorDesc;
    use crate::desc::DeclPolarity;
    use crate::desc::NominalId;
    use crate::desc::OperDesc;
    use crate::desc::SurfaceSpan;
    use crate::rule::RuleFace;
    use crate::test_support::Grade;

    /// A `Nat` family declaring `operations`, in order, with `rules`.
    ///
    /// # Specification
    /// trivial.
    fn nat<O>(
        operations: O,
        rules: Vec<(FreeTerm, FreeTerm)>,
    ) -> TheoryDesc<Grade>
    where
        O: IntoIterator<Item = OperDesc>,
    {
        TheoryDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Nat"),
            Vec::new(),
            [
                CtorDesc::new("Zero", Code::unit(), "Nat", Attrs::empty()),
                CtorDesc::new("Succ", Code::var("Nat"), "Nat", Attrs::empty()),
            ],
            operations.into_iter().collect::<Vec<_>>(),
            rules
                .into_iter()
                .map(|(lhs, rhs)| {
                    RuleFace::new(
                        lhs,
                        rhs,
                        Vec::new(),
                        SurfaceSpan::new(0_usize.into(), 1_usize.into()),
                    )
                })
                .collect::<Vec<_>>(),
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    /// An operation `name` from one `Nat` to one `Nat`.
    ///
    /// # Specification
    /// trivial.
    fn unary<N>(name: N) -> OperDesc
    where
        N: Into<Name>,
    {
        oper(name, vec![SortRef::new("x", "Nat")])
    }

    /// An operation `name` from two `Nat`s to one `Nat`.
    ///
    /// # Specification
    /// trivial.
    fn binary<N>(name: N) -> OperDesc
    where
        N: Into<Name>,
    {
        oper(name, vec![
            SortRef::new("x", "Nat"),
            SortRef::new("x", "Nat"),
        ])
    }

    /// An operation `name` from `inputs` to one `Nat`.
    ///
    /// # Specification
    /// trivial.
    fn oper<N>(
        name: N,
        inputs: Vec<SortRef>,
    ) -> OperDesc
    where
        N: Into<Name>,
    {
        OperDesc::new(
            name,
            BridgeArity::single_output(inputs, SortRef::new("y", "Nat")),
            Attrs::empty(),
        )
    }

    /// The variable `name`.
    ///
    /// # Specification
    /// trivial.
    fn var<N>(name: N) -> FreeTerm
    where
        N: Into<Name>,
    {
        FreeTerm::var(name)
    }

    /// `Succ(term)`.
    ///
    /// # Specification
    /// trivial.
    fn succ(term: FreeTerm) -> FreeTerm
    {
        FreeTerm::ctor("Succ", [term])
    }

    /// `Zero`.
    ///
    /// # Specification
    /// trivial.
    fn zero() -> FreeTerm
    {
        FreeTerm::ctor("Zero", [])
    }

    #[test]
    fn recursion_on_a_descending_argument_is_oriented()
    {
        let add = |m, n| FreeTerm::op("add", [m, n]);
        let family = nat([binary("add")], vec![
            (add(zero(), var("n")), var("n")),
            (add(succ(var("m")), var("n")), succ(add(var("m"), var("n")))),
        ]);
        assert_eq!(orient_rules(&family), Termination::Oriented);
        let precedence = Precedence::of(&family);
        assert!(
            !bool::from(path_greater(
                &precedence,
                &add(var("m"), succ(var("n"))),
                &add(succ(var("m")), var("n"))
            )),
            "the first argument decides before the second"
        );
        assert!(
            bool::from(path_greater(
                &precedence,
                &add(succ(var("m")), var("n")),
                &add(var("m"), succ(succ(var("n"))))
            )),
            "a descending first argument dominates a growing second"
        );
    }

    #[test]
    fn a_call_ranks_its_caller_above_its_callee_in_either_declaration_order()
    {
        let walk = |m, q| FreeTerm::op("walk", [m, q]);
        let entry = |m| FreeTerm::op("entry", [m]);
        let rules = || {
            vec![
                (walk(zero(), var("q")), var("q")),
                (
                    walk(succ(var("m")), var("q")),
                    walk(var("m"), succ(var("q"))),
                ),
                (entry(var("m")), walk(var("m"), zero())),
            ]
        };
        assert_eq!(
            orient_rules(&nat([binary("walk"), unary("entry")], rules())),
            Termination::Oriented,
            "an operation calls the helper declared before it"
        );
        assert_eq!(
            orient_rules(&nat([unary("entry"), binary("walk")], rules())),
            Termination::Oriented,
            "and the helper declared after it"
        );
        assert_eq!(
            orient_rules(&nat([binary("walk")], rules())),
            Termination::Unoriented(RuleIndex::from(2_usize)),
            "an operation the family does not declare is below every one it does"
        );
        let even = |n| FreeTerm::op("even", [n]);
        let odd = |n| FreeTerm::op("odd", [n]);
        let parity = nat([unary("even"), unary("odd"), unary("entry")], vec![
            (entry(var("n")), even(var("n"))),
            (even(zero()), zero()),
            (even(succ(var("n"))), odd(var("n"))),
            (odd(succ(var("n"))), even(var("n"))),
        ]);
        let precedence = Precedence::of(&parity);
        assert_eq!(
            [
                precedence.rank(&Name::from("even")),
                precedence.rank(&Name::from("odd"))
            ],
            [Rank(0), Rank(0)],
            "two operations calling each other rank alike"
        );
        assert_eq!(
            orient_rules(&parity),
            Termination::Unoriented(RuleIndex::from(0_usize)),
            "and so does every operation calling into them"
        );
    }

    #[test]
    fn a_growing_rule_is_the_first_unoriented_one()
    {
        let grow = |x| FreeTerm::op("grow", [x]);
        let twice = |x| FreeTerm::op("twice", [x]);
        let family = nat([unary("twice"), unary("grow")], vec![
            (twice(zero()), zero()),
            (grow(var("x")), succ(grow(var("x")))),
            (twice(var("x")), twice(twice(var("x")))),
        ]);
        assert_eq!(
            orient_rules(&family),
            Termination::Unoriented(RuleIndex::from(1_usize)),
            "a rule rebuilding its own call under a constructor never ends"
        );
        let nested = nat([unary("twice")], vec![(
            twice(var("x")),
            twice(twice(var("x"))),
        )]);
        assert_eq!(
            orient_rules(&nested),
            Termination::Unoriented(RuleIndex::from(0_usize)),
            "a rule nesting its own call never ends"
        );
    }

    #[test]
    fn a_derived_rule_raises_its_head_above_what_it_calls()
    {
        let f = |x| FreeTerm::op("f", [x]);
        let g = |x| FreeTerm::op("g", [x]);
        let family = nat([unary("f"), unary("g")], vec![
            (f(zero()), zero()),
            (g(zero()), zero()),
        ]);
        let calling = [(f(succ(var("x"))), g(var("x")))];
        let precedence = Precedence::with(&family, &calling);
        assert_eq!(
            [
                precedence.rank(&Name::from("f")),
                precedence.rank(&Name::from("g"))
            ],
            [Rank(2), Rank(1)],
            "the derived call ranks `f` above `g`, which the written rules leave alike"
        );
        assert_eq!(
            orient_rules_with(&family, &calling, &[]),
            Termination::Oriented
        );
        assert_eq!(
            orient_rules_with(&family, &[(f(var("x")), g(var("y")))], &[]),
            Termination::Unoriented(RuleIndex::from(2_usize)),
            "a derived rule is indexed past the written rules"
        );
        let written = nat([unary("f"), unary("g")], vec![(
            f(succ(var("x"))),
            g(var("x")),
        )]);
        assert_eq!(
            orient_rules_with(&written, &[(g(succ(var("x"))), f(var("x")))], &[]),
            Termination::Unoriented(RuleIndex::from(0_usize)),
            "a derived call closing a cycle ranks both operations alike and unorients the written rule"
        );
        let nested = [(g(f(var("x"))), f(var("x")))];
        assert_eq!(
            orient_rules_with(&written, &nested, &[]),
            Termination::Unoriented(RuleIndex::from(0_usize)),
            "ranking a call back to `f` closes the cycle"
        );
        assert_eq!(
            orient_rules_with(&written, &[], &nested),
            Termination::Oriented,
            "riding the written precedence, the rule descends to its own subterm"
        );
    }

    #[test]
    fn the_order_is_irreflexive_and_reads_variables_by_occurrence()
    {
        let family = nat([unary("pred")], Vec::new());
        let precedence = Precedence::of(&family);
        let pred = |x| FreeTerm::op("pred", [x]);
        let call = pred(succ(var("m")));
        assert!(!bool::from(path_greater(&precedence, &call, &call)));
        assert!(bool::from(path_greater(&precedence, &call, &var("m"))));
        assert!(
            !bool::from(path_greater(&precedence, &call, &var("n"))),
            "a variable absent from the left side is above it"
        );
        assert!(
            !bool::from(path_greater(&precedence, &var("m"), &zero())),
            "a variable is above nothing"
        );
        assert!(
            bool::from(path_greater(
                &precedence,
                &pred(var("m")),
                &FreeTerm::results([var("m"), zero()])
            )),
            "an operation is above the results tuple it returns"
        );
    }

    #[test]
    fn an_instantiation_is_below_the_application_that_binds_its_metavariable()
    {
        let bind = |u, t| FreeTerm::op("let", [u, t]);
        let app = |t, u| FreeTerm::op("app", [t, u]);
        let lam = |t| FreeTerm::op("lam", [t]);
        let zeta = nat([binary("let")], vec![(
            bind(var("u"), var("t")),
            FreeTerm::inst("t", [var("u")]),
        )]);
        assert_eq!(
            orient_rules(&zeta),
            Termination::Oriented,
            "`let` holds the metavariable and its argument, so `t(u)` is below it"
        );
        let growing = nat([binary("let")], vec![(
            bind(var("u"), var("t")),
            FreeTerm::inst("t", [bind(var("u"), var("t"))]),
        )]);
        assert_eq!(
            orient_rules(&growing),
            Termination::Unoriented(RuleIndex::from(0_usize)),
            "an instantiation at the rule's own call does not descend"
        );
        let beta = nat([binary("app"), unary("lam")], vec![(
            app(lam(var("t")), var("u")),
            FreeTerm::inst("t", [var("u")]),
        )]);
        assert_eq!(
            orient_rules(&beta),
            Termination::Unoriented(RuleIndex::from(0_usize)),
            "β's metavariable stands under `lam`, so the order cannot see past the binder"
        );
        let shadow = nat([binary("app"), unary("lam")], vec![(
            app(lam(var("t")), var("u")),
            app(var("t"), var("u")),
        )]);
        assert_eq!(
            orient_rules(&shadow),
            Termination::Oriented,
            "read with every variable at base type, β's first-order shadow orients"
        );
    }
}
