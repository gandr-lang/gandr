//! The second-order reading of a presentation's rules, under which a rule
//! instantiating a variable rewrites terms and takes part in critical pairs.
//! A binding field and an atom's abstraction each bind over their argument,
//! and an occurrence counts the binders of either kind between it and its
//! own. A rule's variable is a metavariable standing for a term abstracted
//! over the variables its left side applies it to, naming no other variable
//! the rule binds.
//!
//! Matching `get(bind s . k(s))` binds `k` to the field's body with `s`
//! abstracted, and fails where that body names a binder of the rule `k` is
//! not applied to; an instance `k(u)` substitutes `u` for the abstracted
//! variable. Terms are kept η-short: a binding field whose body applies a
//! metavariable to the field's own variable last, and names it nowhere
//! else, is that metavariable applied to the rest, so `bind x . k(x)` and
//! `k` are one term, and a rule's binding field matches a metavariable by
//! expanding it once.
//!
//! A critical pair of two rules, one of which instantiates a variable, is
//! found by pattern unification: the inner rule's left side, each of its
//! metavariables applied to the binders above the position it overlaps at,
//! is unified with the outer rule's left side there, a metavariable's
//! argument naming a binder the other side may not reach pruned away. The
//! pair's two reducts are normalized under every rule that is not
//! conditioned and compared: the critical pair lemma for pattern rewrite
//! systems.
//!
//! # References
//! - Dale Miller, _A logic programming language with lambda-abstraction,
//!   function variables, and simple unification_, Journal of Logic and
//!   Computation 1(4), 1991: patterns and their unification.
//! - Richard Mayr and Tobias Nipkow, _Higher-order rewrite systems and their
//!   confluence_, Theoretical Computer Science 192(1), 1998: the critical pair
//!   lemma for pattern rewrite systems.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::vec;
use alloc::vec::Vec;
use core::slice;

use super::Position;
use super::SymbolKind;
use super::TheoryNode;
use super::TheoryRule;
use super::TheoryRules;
use super::TheorySymbol;
use super::ordinal;
use crate::presented::Exhausted;
use crate::presented::RewriteFuel;
use crate::presented::RuleIndex;

/// A count of subterms, parameters or binders, or an occurrence's distance
/// to its binder.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Count(usize);

/// A metavariable: a rule's variable, or one unification introduced.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Meta(usize);

/// What a node binds over its arguments.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Binds
{
    /// Nothing: an operation, a constructor or a results tuple.
    Nothing,
    /// An atom: an atom's abstraction.
    Atom,
    /// A variable: a binding field.
    Variable,
}

/// One node of a term, in pre-order.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Node
{
    /// A symbol over its next subterms, binding what it binds over them.
    Symbol(TheorySymbol, Count, Binds),
    /// An occurrence of a binder of its kind, by the binders between the two.
    Index(Binds, Count),
    /// A metavariable applied to its next subterms.
    Meta(Meta, Count),
}

/// A term, its nodes in pre-order.
type Term = Vec<Node>;

/// What a metavariable stands for: a term abstracted over its parameters,
/// the last parameter at distance zero, its other free occurrences counted
/// from where the metavariable was bound.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Value
{
    /// The parameters the body abstracts.
    params: Count,
    /// The body.
    body: Term,
}

/// The value each bound metavariable stands for.
type Bindings = BTreeMap<Meta, Value>;

/// Which way [`shifted`] moves the free occurrences it moves.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Shift
{
    /// Out, under this many more binders.
    Up(Count),
    /// In, past this many binders removed.
    Down(Count),
}

/// What unifying two terms found.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Unified
{
    /// The most general unifier.
    Solved(Bindings),
    /// No unifier.
    Apart,
    /// A metavariable applied to other than distinct occurrences, which
    /// pattern unification does not decide.
    Undecided,
}

/// One step of unification on an equation.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Step
{
    /// The equation holds as it stands.
    Holds,
    /// These bindings, after which the equation is unified again.
    Bind(Vec<(Meta, Value)>),
    /// No unifier.
    Apart,
    /// Not a pattern equation.
    Undecided,
}

/// The verdict on one critical pair of the second-order reading.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Pair
{
    /// The two rules do not overlap there, or the pair's reducts normalize to
    /// one term.
    Joins,
    /// The pair's reducts normalize to two terms.
    Parts,
    /// The overlap is not a pattern unification problem.
    Undecided,
}

/// One rule read second-order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Rule
{
    /// The left side, η-short.
    left: Term,
    /// The right side, η-short.
    right: Term,
    /// One past the largest metavariable the rule names.
    metas: Count,
    /// Each left position of an operation, a constructor or a results tuple
    /// in the rule's own reading, by its position in this one.
    places: BTreeMap<Position, Position>,
    /// Whether the rule rewrites terms: every rule but a conditioned one.
    fires: Fires,
}

/// Whether a rule rewrites the terms a pair's reducts normalize.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fires
{
    /// It does.
    Always,
    /// It is conditioned and fires on no term the decision normalizes.
    Never,
}

/// A presentation's rules read second-order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(super) struct Higher
{
    /// Each rule's reading, by its index; [`None`] where a rule names a
    /// symbol outside the table.
    rules: Vec<Option<Rule>>,
    /// The binding field of one argument a metavariable expands under, when
    /// the table holds one.
    field: Option<TheorySymbol>,
}

impl Higher
{
    /// `rules` read second-order.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn new(rules: &TheoryRules) -> Self
    {
        let field = rules
            .symbols
            .iter()
            .position(|&(kind, arity)| kind == SymbolKind::Field && usize::from(arity) == 1);
        Self {
            rules: rules
                .rules
                .iter()
                .map(|rule| reading(rules, rule))
                .collect(),
            field: field.map(TheorySymbol),
        }
    }

    /// The critical pair at `at` of `outer`'s left side and `inner`'s,
    /// decided in the second-order reading.
    ///
    /// # Specification
    /// - requires: both rules well formed.
    /// - ensures: [`Pair::Joins`] when `at` is not an operation's position, the
    ///   two left sides do not unify there with `inner`'s metavariables applied
    ///   to the binders above `at`, or their most general unifier's two reducts
    ///   — `outer`'s right side, and `outer`'s left side with `inner`'s right
    ///   side grafted at `at`, both instantiated — normalize to one η-short
    ///   term under every rule not conditioned; [`Pair::Parts`] when they
    ///   normalize to two; [`Pair::Undecided`] when unification meets a
    ///   metavariable applied to other than distinct occurrences, or either
    ///   rule names a symbol outside the table.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — the verdict is a comparison of two normal forms,
    ///   and no predicate cheaper than computing them again states it.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `let` instantiating its argument joins a second
    ///   `let` rule at a constant and parts from one rewriting it apart;
    ///   get-get joins its own instance through its pattern; a relative monad's
    ///   associativity joins with itself and both unit laws.
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    /// - witness: `theory_rules::tests::a_relative_monads_laws_join_their_overlaps_2328`
    pub(super) fn pair(
        &self,
        outer: RuleIndex,
        at: Position,
        inner: RuleIndex,
        fuel: &mut RewriteFuel,
    ) -> Result<Pair, Exhausted>
    {
        let (Some(&Some(ref over)), Some(&Some(ref under))) = (
            self.rules.get(usize::from(outer)),
            self.rules.get(usize::from(inner)),
        )
        else {
            return Ok(Pair::Undecided);
        };
        let Some(&place) = over.places.get(&at)
        else {
            return Ok(Pair::Joins);
        };
        if over.left.get(place.0) != under.left.first() {
            return Ok(Pair::Joins);
        }
        let (Some(stop), Some(binders)) =
            (end(&over.left, place), binders_above(&over.left, place))
        else {
            return Ok(Pair::Undecided);
        };
        let lifted_left = lifted(&under.left, &binders, over.metas);
        let lifted_right = lifted(&under.right, &binders, over.metas);
        let fresh = Meta(over.metas.0.saturating_add(under.metas.0));
        let Some(redex) = over.left.get(place.0 .. stop.0)
        else {
            return Ok(Pair::Undecided);
        };
        let solution = match unified(
            redex.to_vec(),
            lifted_left,
            Count(binders.len()),
            fresh,
            self.field,
            fuel,
        )? {
            Unified::Solved(solution) => solution,
            Unified::Apart => return Ok(Pair::Joins),
            Unified::Undecided => return Ok(Pair::Undecided),
        };
        let mut grafted = over.left.get(.. place.0).unwrap_or_default().to_vec();
        grafted.extend(lifted_right);
        grafted.extend_from_slice(over.left.get(stop.0 ..).unwrap_or_default());
        let (Some(by_outer), Some(by_inner)) = (
            built(&over.right, &solution, self.field, fuel)?,
            built(&grafted, &solution, self.field, fuel)?,
        )
        else {
            return Ok(Pair::Parts);
        };
        let by_outer = self.normalize(contracted(by_outer, fuel)?, fuel)?;
        let by_inner = self.normalize(contracted(by_inner, fuel)?, fuel)?;
        Ok(match (by_outer, by_inner) {
            (Some(by_outer), Some(by_inner)) if by_outer == by_inner => Pair::Joins,
            (Some(_) | None, Some(_) | None) => Pair::Parts,
        })
    }

    /// `term`'s normal form under every rule that fires, rewriting the last
    /// redex in pre-order first; [`None`] where a rule's instance is ill
    /// formed.
    ///
    /// # Specification
    /// - requires: `term` η-short.
    /// - ensures: on [`Some`], an η-short term no rule that fires matches at
    ///   any position, reached from `term` by rewriting.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — a normal form is what this computes; checking one
    ///   is another match of every rule at every position.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pair`].
    /// - witness: `theory_rules::tests::a_relative_monads_laws_join_their_overlaps_2328`
    fn normalize(
        &self,
        term: Term,
        fuel: &mut RewriteFuel,
    ) -> Result<Option<Term>, Exhausted>
    {
        let mut term = term;
        'rewrite: loop {
            for at in (0 .. term.len()).rev() {
                let Some(&head @ Node::Symbol(_, _, Binds::Nothing)) = term.get(at)
                else {
                    continue;
                };
                let Some(Position(stop)) = end(&term, Position(at))
                else {
                    return Ok(None);
                };
                for rule in self.rules.iter().flatten() {
                    if rule.fires == Fires::Never || rule.left.first() != Some(&head) {
                        continue;
                    }
                    fuel.charge()?;
                    let Some(subject) = term.get(at .. stop)
                    else {
                        return Ok(None);
                    };
                    let Some(bindings) = matched(&rule.left, subject, fuel)?
                    else {
                        continue;
                    };
                    let Some(reduct) = built(&rule.right, &bindings, self.field, fuel)?
                    else {
                        return Ok(None);
                    };
                    drop(term.splice(at .. stop, reduct));
                    term = contracted(term, fuel)?;
                    continue 'rewrite;
                }
            }
            return Ok(Some(term));
        }
    }
}

/// `rule` read second-order, its variables metavariables by their ordinals;
/// [`None`] where it names a symbol outside `rules`' table.
///
/// # Specification
/// trivial.
fn reading(
    rules: &TheoryRules,
    rule: &TheoryRule,
) -> Option<Rule>
{
    let left = side(rules, rule.left())?;
    let right = side(rules, rule.right())?;
    let metas = left
        .iter()
        .chain(&right)
        .filter_map(|&node| match node {
            Node::Meta(Meta(meta), _) => Some(meta.saturating_add(1)),
            Node::Symbol(..) | Node::Index(..) => None,
        })
        .max()
        .unwrap_or_default();
    let mut fuel = RewriteFuel::from(u64::MAX);
    let (Ok(short_left), Ok(right)) = (
        contracted(left.clone(), &mut fuel),
        contracted(right, &mut fuel),
    )
    else {
        return None;
    };
    let operations = |term: &[Node]| {
        term.iter()
            .enumerate()
            .filter(|&(_, &node)| matches!(node, Node::Symbol(_, _, Binds::Nothing)))
            .map(|(at, _)| Position(at))
            .collect::<Vec<Position>>()
    };
    let places = operations(&left)
        .into_iter()
        .zip(operations(&short_left))
        .collect();
    Some(Rule {
        left: short_left,
        right,
        metas: Count(metas),
        places,
        fires: if rule.conditioned {
            Fires::Never
        }
        else {
            Fires::Always
        },
    })
}

/// A rule side read second-order, before contraction.
///
/// # Specification
/// trivial.
fn side(
    rules: &TheoryRules,
    nodes: &[TheoryNode],
) -> Option<Term>
{
    nodes
        .iter()
        .map(|&node| match node {
            TheoryNode::Symbol(symbol) => {
                let &(kind, arity) = rules.symbols.get(symbol.0)?;
                let arity = Count(usize::from(arity));
                Some(match kind {
                    SymbolKind::Operation(_) | SymbolKind::Constructor => {
                        Node::Symbol(symbol, arity, Binds::Nothing)
                    },
                    SymbolKind::Abstraction => Node::Symbol(symbol, arity, Binds::Atom),
                    SymbolKind::Field => Node::Symbol(symbol, arity, Binds::Variable),
                    SymbolKind::Occurrence(distance) => {
                        Node::Index(Binds::Atom, Count(usize::from(distance)))
                    },
                    SymbolKind::Bound(distance) => {
                        Node::Index(Binds::Variable, Count(usize::from(distance)))
                    },
                })
            },
            TheoryNode::Variable(variable) => Some(Node::Meta(Meta(ordinal(variable).0), Count(0))),
            TheoryNode::Instance(variable, count) => Some(Node::Meta(
                Meta(ordinal(variable).0),
                Count(usize::from(count)),
            )),
        })
        .collect()
}

/// The subterms `node` applies.
///
/// # Specification
/// trivial.
const fn width(node: Node) -> Count
{
    match node {
        Node::Symbol(_, arity, _) => arity,
        Node::Index(..) => Count(0),
        Node::Meta(_, count) => count,
    }
}

/// What `node` binds over its arguments.
///
/// # Specification
/// trivial.
const fn binder(node: Node) -> Binds
{
    match node {
        Node::Symbol(_, _, binds) => binds,
        Node::Index(..) | Node::Meta(..) => Binds::Nothing,
    }
}

/// One past the last node of the subterm at `start`; [`None`] when the term
/// ends first.
///
/// # Specification
/// trivial.
fn end(
    term: &[Node],
    start: Position,
) -> Option<Position>
{
    let mut owed = 1_usize;
    let mut at = start.0;
    while owed > 0 {
        let &node = term.get(at)?;
        owed = owed.saturating_sub(1).saturating_add(width(node).0);
        at = at.saturating_add(1);
    }
    Some(Position(at))
}

/// The positions of the subterms the node at `at` applies.
///
/// # Specification
/// trivial.
fn children(
    term: &[Node],
    at: Position,
) -> Option<Vec<Position>>
{
    let &node = term.get(at.0)?;
    let mut out = Vec::with_capacity(width(node).0);
    let mut next = Position(at.0.saturating_add(1));
    for _ in 0 .. width(node).0 {
        out.push(next);
        next = end(term, next)?;
    }
    Some(out)
}

/// The subterms the root of `term` applies, each copied out.
///
/// # Specification
/// trivial.
fn subterms(term: &[Node]) -> Option<Vec<Term>>
{
    children(term, Position(0))?
        .into_iter()
        .map(|start| Some(term.get(start.0 .. end(term, start)?.0)?.to_vec()))
        .collect()
}

/// The binders above each node of a sequence of terms, counted from its
/// start.
///
/// # Specification
/// trivial.
fn depths(term: &[Node]) -> Vec<Count>
{
    let mut out = Vec::with_capacity(term.len());
    // Each open node's arguments still to come, and what it binds.
    let mut open: Vec<(usize, Binds)> = Vec::new();
    let mut depth = 0_usize;
    for &node in term {
        out.push(Count(depth));
        let arity = width(node).0;
        if arity > 0 {
            if binder(node) != Binds::Nothing {
                depth = depth.saturating_add(1);
            }
            open.push((arity, binder(node)));
            continue;
        }
        while let Some(top) = open.last_mut() {
            top.0 = top.0.saturating_sub(1);
            if top.0 > 0 {
                break;
            }
            if top.1 != Binds::Nothing {
                depth = depth.saturating_sub(1);
            }
            let _closed = open.pop();
        }
    }
    out
}

/// The binders above position `at` of `term`, outermost first.
///
/// # Specification
/// trivial.
fn binders_above(
    term: &[Node],
    at: Position,
) -> Option<Vec<Binds>>
{
    let mut open: Vec<(usize, Binds)> = Vec::new();
    for (position, &node) in term.iter().enumerate() {
        if position == at.0 {
            return Some(
                open.iter()
                    .map(|&(_, binds)| binds)
                    .filter(|&binds| binds != Binds::Nothing)
                    .collect(),
            );
        }
        let arity = width(node).0;
        if arity > 0 {
            open.push((arity, binder(node)));
            continue;
        }
        while let Some(top) = open.last_mut() {
            top.0 = top.0.saturating_sub(1);
            if top.0 > 0 {
                break;
            }
            let _closed = open.pop();
        }
    }
    None
}

/// `term` with each occurrence free past its first `from` binders moved by
/// `shift`; [`None`] when one would move into those binders.
///
/// # Specification
/// trivial.
fn shifted(
    term: &[Node],
    from: Count,
    shift: Shift,
) -> Option<Term>
{
    term.iter()
        .zip(depths(term))
        .map(|(&node, Count(local))| match node {
            Node::Index(kind, Count(index)) if index >= local.saturating_add(from.0) => {
                let moved = match shift {
                    Shift::Up(Count(by)) => Some(index.saturating_add(by)),
                    Shift::Down(Count(by)) => index
                        .checked_sub(by)
                        .filter(|&moved| moved >= local.saturating_add(from.0)),
                };
                moved.map(|moved| Node::Index(kind, Count(moved)))
            },
            Node::Symbol(..) | Node::Index(..) | Node::Meta(..) => Some(node),
        })
        .collect()
}

/// `body` with its parameters, one per argument, replaced by `args`, the
/// last argument for the parameter at distance zero, each moved under the
/// binders above where it lands, and every other free occurrence moved
/// under `under` binders; [`None`] when an argument would move into a
/// binder.
///
/// # Specification
/// trivial.
fn substituted(
    body: &[Node],
    args: &[Term],
    under: Count,
    fuel: &mut RewriteFuel,
) -> Result<Option<Term>, Exhausted>
{
    let params = args.len();
    let mut out = Vec::with_capacity(body.len());
    for (&node, Count(local)) in body.iter().zip(depths(body)) {
        fuel.charge()?;
        let Node::Index(kind, Count(index)) = node
        else {
            out.push(node);
            continue;
        };
        let Some(free) = index.checked_sub(local)
        else {
            out.push(node);
            continue;
        };
        if free < params {
            let Some(moved) = params
                .checked_sub(free.saturating_add(1))
                .and_then(|place| args.get(place))
                .and_then(|arg| shifted(arg, Count(0), Shift::Up(Count(local))))
            else {
                return Ok(None);
            };
            out.extend(moved);
        }
        else {
            let ambient = free.saturating_sub(params);
            out.push(Node::Index(
                kind,
                Count(ambient.saturating_add(under.0).saturating_add(local)),
            ));
        }
    }
    Ok(Some(out))
}

/// `head` applied to `args` in turn: a binding field's body with its
/// variable replaced, or a metavariable's application extended; [`None`]
/// at anything else.
///
/// # Specification
/// trivial.
fn applied(
    head: Term,
    args: &[Term],
    fuel: &mut RewriteFuel,
) -> Result<Option<Term>, Exhausted>
{
    let mut term = head;
    for arg in args {
        match term.first().copied() {
            Some(Node::Symbol(_, Count(1), Binds::Variable)) => {
                let Some(next) = substituted(
                    term.get(1 ..).unwrap_or_default(),
                    slice::from_ref(arg),
                    Count(0),
                    fuel,
                )?
                else {
                    return Ok(None);
                };
                term = next;
            },
            Some(Node::Meta(meta, Count(count))) => {
                if let Some(first) = term.first_mut() {
                    *first = Node::Meta(meta, Count(count.saturating_add(1)));
                }
                term.extend_from_slice(arg);
            },
            Some(Node::Symbol(..) | Node::Index(..)) | None => return Ok(None),
        }
    }
    Ok(Some(term))
}

/// `value` instantiated at `args` where it stands under `under` binders:
/// its parameters replaced by the first of them and the result applied to
/// the rest, or, at fewer arguments than parameters, the parameters left
/// over abstracted by binding fields of `field`.
///
/// # Specification
/// trivial.
fn instance(
    value: &Value,
    args: &[Term],
    under: Count,
    field: Option<TheorySymbol>,
    fuel: &mut RewriteFuel,
) -> Result<Option<Term>, Exhausted>
{
    let params = value.params.0;
    if let (Some(taken), Some(rest)) = (args.get(.. params), args.get(params ..)) {
        let Some(term) = substituted(&value.body, taken, under, fuel)?
        else {
            return Ok(None);
        };
        return applied(term, rest, fuel);
    }
    let Some(field) = field
    else {
        return Ok(None);
    };
    let wrap = params.saturating_sub(args.len());
    let mut all = Vec::with_capacity(params);
    for arg in args {
        let Some(moved) = shifted(arg, Count(0), Shift::Up(Count(wrap)))
        else {
            return Ok(None);
        };
        all.push(moved);
    }
    for place in args.len() .. params {
        all.push(vec![Node::Index(
            Binds::Variable,
            Count(params.saturating_sub(place.saturating_add(1))),
        )]);
    }
    let Some(body) = substituted(&value.body, &all, Count(under.0.saturating_add(wrap)), fuel)?
    else {
        return Ok(None);
    };
    let mut out = vec![Node::Symbol(field, Count(1), Binds::Variable); wrap];
    out.extend(body);
    Ok(Some(out))
}

/// `term` η-short: each binding field whose body applies a metavariable to
/// the field's own variable last, and names it nowhere else, replaced by
/// the metavariable applied to the rest, until none is left.
///
/// # Specification
/// trivial.
fn contracted(
    term: Term,
    fuel: &mut RewriteFuel,
) -> Result<Term, Exhausted>
{
    let mut term = term;
    'search: loop {
        for at in (0 .. term.len()).rev() {
            fuel.charge()?;
            let (Some(short), Some(Position(stop))) =
                (contraction(&term, Position(at)), end(&term, Position(at)))
            else {
                continue;
            };
            drop(term.splice(at .. stop, short));
            continue 'search;
        }
        return Ok(term);
    }
}

/// The η-contraction of the binding field at `at`, when it has one.
///
/// # Specification
/// trivial.
fn contraction(
    term: &[Node],
    at: Position,
) -> Option<Term>
{
    let Some(&Node::Symbol(_, Count(1), Binds::Variable)) = term.get(at.0)
    else {
        return None;
    };
    let head = Position(at.0.saturating_add(1));
    let Some(&Node::Meta(meta, Count(count))) = term.get(head.0)
    else {
        return None;
    };
    let kept = count.checked_sub(1)?;
    let first = Position(head.0.saturating_add(1));
    let mut last = first;
    for _ in 0 .. kept {
        last = end(term, last)?;
    }
    if term.get(last.0 .. end(term, last)?.0)? != [Node::Index(Binds::Variable, Count(0))] {
        return None;
    }
    let rest = shifted(
        term.get(first.0 .. last.0)?,
        Count(0),
        Shift::Down(Count(1)),
    )?;
    let mut short = Vec::with_capacity(rest.len().saturating_add(1));
    short.push(Node::Meta(meta, Count(kept)));
    short.extend(rest);
    Some(short)
}

/// The metavariable application `flex` η-expanded once under a binding
/// field of `field`.
///
/// # Specification
/// trivial.
fn expansion(
    flex: &[Node],
    field: TheorySymbol,
) -> Option<Term>
{
    let (&Node::Meta(meta, Count(count)), args) = flex.split_first()?
    else {
        return None;
    };
    let lifted = shifted(args, Count(0), Shift::Up(Count(1)))?;
    let mut out = Vec::with_capacity(flex.len().saturating_add(2));
    out.push(Node::Symbol(field, Count(1), Binds::Variable));
    out.push(Node::Meta(meta, Count(count.saturating_add(1))));
    out.extend(lifted);
    out.push(Node::Index(Binds::Variable, Count(0)));
    Some(out)
}

/// The arguments of the metavariable application `flex`, when each is one
/// occurrence.
///
/// # Specification
/// trivial.
fn pattern(flex: &[Node]) -> Option<Vec<(Binds, Count)>>
{
    subterms(flex)?
        .into_iter()
        .map(|arg| match *arg.as_slice() {
            [Node::Index(kind, index)] => Some((kind, index)),
            [] | [_, ..] => None,
        })
        .collect()
}

/// `term`, standing under `depth` binders, abstracted over the occurrences
/// `names` lists, the last at distance zero; its other free occurrences
/// past those binders moved past the parameters; [`None`] when it names one
/// of those binders `names` does not list.
///
/// # Specification
/// trivial.
fn abstraction(
    term: &[Node],
    depth: Count,
    names: &[(Binds, Count)],
) -> Option<Term>
{
    let params = names.len();
    let place_of: BTreeMap<(Binds, Count), usize> = names
        .iter()
        .enumerate()
        .rev()
        .map(|(place, &name)| (name, place))
        .collect();
    term.iter()
        .zip(depths(term))
        .map(|(&node, Count(local))| match node {
            Node::Index(kind, Count(index)) => match index.checked_sub(local) {
                None => Some(node),
                Some(free) if free < depth.0 => {
                    let place = *place_of.get(&(kind, Count(free)))?;
                    let param = params.saturating_sub(place.saturating_add(1));
                    Some(Node::Index(kind, Count(local.saturating_add(param))))
                },
                Some(free) => Some(Node::Index(
                    kind,
                    Count(
                        local
                            .saturating_add(params)
                            .saturating_add(free.saturating_sub(depth.0)),
                    ),
                )),
            },
            Node::Symbol(..) | Node::Meta(..) => Some(node),
        })
        .collect()
}

/// What matching the η-short `left` against the η-short `subject` binds each
/// of `left`'s metavariables to; [`None`] when it does not match.
///
/// # Specification
/// - requires: `left` a well-formed rule's left side read second-order.
/// - ensures: on [`Some`], instantiating `left` at the bindings and contracting
///   gives `subject`; each metavariable's value names no binder of `left` it is
///   not applied to there.
/// - fails: [`Exhausted`] when `fuel` runs out first.
/// - panics: none.
/// - executable: none — checking a match instantiates `left` at the bindings
///   and contracts it, which is the work matching saves.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Higher::pair`].
/// - witness: `theory_rules::tests::a_relative_monads_laws_join_their_overlaps_2328`
fn matched(
    left: &[Node],
    subject: &[Node],
    fuel: &mut RewriteFuel,
) -> Result<Option<Bindings>, Exhausted>
{
    let left_depths = depths(left);
    let mut buffers: Vec<Term> = vec![subject.to_vec()];
    let mut bindings = Bindings::new();
    // Each pair still to match: a left position, a buffer, and its position.
    let mut pairs = vec![(Position(0), Count(0), Position(0))];
    while let Some((at, Count(buffer), from)) = pairs.pop() {
        fuel.charge()?;
        let (Some(&rule), Some(term)) = (left.get(at.0), buffers.get(buffer))
        else {
            return Ok(None);
        };
        let Some(&node) = term.get(from.0)
        else {
            return Ok(None);
        };
        match (rule, node) {
            (Node::Symbol(symbol, arity, binds), Node::Symbol(other, other_arity, other_binds)) => {
                if (symbol, arity, binds) != (other, other_arity, other_binds) {
                    return Ok(None);
                }
                let (Some(rule_args), Some(args)) = (children(left, at), children(term, from))
                else {
                    return Ok(None);
                };
                pairs.extend(
                    rule_args
                        .into_iter()
                        .zip(args)
                        .map(|(rule_arg, arg)| (rule_arg, Count(buffer), arg)),
                );
            },
            (Node::Symbol(symbol, Count(1), Binds::Variable), Node::Meta(..)) => {
                let Some(expanded) = end(term, from)
                    .and_then(|stop| term.get(from.0 .. stop.0))
                    .and_then(|flex| expansion(flex, symbol))
                else {
                    return Ok(None);
                };
                pairs.push((at, Count(buffers.len()), Position(0)));
                buffers.push(expanded);
            },
            (Node::Symbol(..), Node::Index(..) | Node::Meta(..)) => return Ok(None),
            (Node::Index(..), Node::Symbol(..) | Node::Index(..) | Node::Meta(..)) => {
                if rule != node {
                    return Ok(None);
                }
            },
            (Node::Meta(meta, params), Node::Symbol(..) | Node::Index(..) | Node::Meta(..)) => {
                let names = end(left, at)
                    .and_then(|stop| left.get(at.0 .. stop.0))
                    .and_then(pattern);
                let (Some(names), Some(&depth)) = (names, left_depths.get(at.0))
                else {
                    return Ok(None);
                };
                let Some(body) = end(term, from)
                    .and_then(|stop| term.get(from.0 .. stop.0))
                    .and_then(|bound| abstraction(bound, depth, &names))
                else {
                    return Ok(None);
                };
                let value = Value { params, body };
                match bindings.entry(meta) {
                    Entry::Vacant(entry) => {
                        let _value = entry.insert(value);
                    },
                    Entry::Occupied(entry) => {
                        if *entry.get() != value {
                            return Ok(None);
                        }
                    },
                }
            },
        }
    }
    Ok(Some(bindings))
}

/// `template` with each metavariable `bindings` binds instantiated at its
/// arguments where it stands, every other kept; [`None`] where an instance
/// is ill formed.
///
/// # Specification
/// trivial.
fn built(
    template: &[Node],
    bindings: &Bindings,
    field: Option<TheorySymbol>,
    fuel: &mut RewriteFuel,
) -> Result<Option<Term>, Exhausted>
{
    // Each subterm built so far, the next to the right on top.
    let mut done: Vec<Term> = Vec::new();
    for (&node, depth) in template.iter().zip(depths(template)).rev() {
        fuel.charge()?;
        let Some(first) = done.len().checked_sub(width(node).0)
        else {
            return Ok(None);
        };
        let args: Vec<Term> = done.split_off(first).into_iter().rev().collect();
        let bound = match node {
            Node::Meta(meta, _) => bindings.get(&meta),
            Node::Symbol(..) | Node::Index(..) => None,
        };
        let out = if let Some(value) = bound {
            let Some(term) = instance(value, &args, depth, field, fuel)?
            else {
                return Ok(None);
            };
            term
        }
        else {
            let mut out = vec![node];
            out.extend(args.into_iter().flatten());
            out
        };
        done.push(out);
    }
    let built = done.pop();
    Ok(built.filter(|_| done.is_empty()))
}

/// `side` with each metavariable renumbered past `offset` and applied first
/// to the binders `binders` lists, outermost first: a rule's side as it
/// stands under those binders.
///
/// # Specification
/// trivial.
fn lifted(
    side: &[Node],
    binders: &[Binds],
    offset: Count,
) -> Term
{
    let lift = binders.len();
    let mut out = Vec::with_capacity(side.len());
    for (&node, Count(local)) in side.iter().zip(depths(side)) {
        match node {
            Node::Meta(Meta(meta), Count(count)) => {
                out.push(Node::Meta(
                    Meta(meta.saturating_add(offset.0)),
                    Count(count.saturating_add(lift)),
                ));
                for (place, &kind) in binders.iter().enumerate() {
                    let distance = lift.saturating_sub(place.saturating_add(1));
                    out.push(Node::Index(kind, Count(local.saturating_add(distance))));
                }
            },
            Node::Symbol(..) | Node::Index(..) => out.push(node),
        }
    }
    out
}

/// The most general unifier of `first` and `second`, both standing under
/// `depth` binders, metavariables it introduces numbered from `fresh`.
///
/// # Specification
/// - requires: both η-short, every metavariable applied at most to occurrences.
/// - ensures: [`Unified::Solved`] with bindings under which the two instantiate
///   to one η-short term, every other unifier an instance of them;
///   [`Unified::Apart`] when none exists; [`Unified::Undecided`] when a
///   metavariable is applied to other than distinct occurrences.
/// - fails: [`Exhausted`] when `fuel` runs out first.
/// - panics: none.
/// - executable: none — a unifier's generality is a statement about every other
///   unifier, which no runtime predicate enumerates.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Higher::pair`].
/// - witness: `theory_rules::tests::a_relative_monads_laws_join_their_overlaps_2328`
fn unified(
    first: Term,
    second: Term,
    depth: Count,
    fresh: Meta,
    field: Option<TheorySymbol>,
    fuel: &mut RewriteFuel,
) -> Result<Unified, Exhausted>
{
    let mut fresh = fresh;
    let mut solution = Bindings::new();
    let mut equations = vec![(first, second, depth)];
    while let Some((left, right, depth)) = equations.pop() {
        fuel.charge()?;
        let (Some(&head), Some(&other)) = (left.first(), right.first())
        else {
            return Ok(Unified::Undecided);
        };
        let step = match (head, other) {
            (Node::Symbol(..), Node::Symbol(..)) => {
                if head != other {
                    return Ok(Unified::Apart);
                }
                let (Some(lefts), Some(rights)) = (subterms(&left), subterms(&right))
                else {
                    return Ok(Unified::Undecided);
                };
                let inner = if binder(head) == Binds::Nothing {
                    depth
                }
                else {
                    Count(depth.0.saturating_add(1))
                };
                equations.extend(
                    lefts
                        .into_iter()
                        .zip(rights)
                        .map(|(left, right)| (left, right, inner)),
                );
                Step::Holds
            },
            (Node::Index(..), Node::Index(..)) => {
                if head != other {
                    return Ok(Unified::Apart);
                }
                Step::Holds
            },
            (Node::Symbol(..), Node::Index(..)) | (Node::Index(..), Node::Symbol(..)) => {
                return Ok(Unified::Apart);
            },
            (Node::Meta(..), Node::Meta(..)) => flex_flex(&left, &right, &mut fresh),
            (Node::Meta(..), Node::Symbol(..) | Node::Index(..)) => {
                flex_rigid(&left, &right, depth, &mut fresh)
            },
            (Node::Symbol(..) | Node::Index(..), Node::Meta(..)) => {
                flex_rigid(&right, &left, depth, &mut fresh)
            },
        };
        let bound = match step {
            Step::Holds => continue,
            Step::Apart => return Ok(Unified::Apart),
            Step::Undecided => return Ok(Unified::Undecided),
            Step::Bind(bound) => bound,
        };
        let bound: Bindings = bound.into_iter().collect();
        for value in solution.values_mut() {
            let Some(body) = built(&value.body, &bound, field, fuel)?
            else {
                return Ok(Unified::Undecided);
            };
            value.body = contracted(body, fuel)?;
        }
        let mut next = Vec::with_capacity(equations.len().saturating_add(1));
        for (left, right, depth) in equations.into_iter().chain([(left, right, depth)]) {
            let (Some(left), Some(right)) = (
                built(&left, &bound, field, fuel)?,
                built(&right, &bound, field, fuel)?,
            )
            else {
                return Ok(Unified::Undecided);
            };
            next.push((contracted(left, fuel)?, contracted(right, fuel)?, depth));
        }
        equations = next;
        solution.extend(bound);
    }
    Ok(Unified::Solved(solution))
}

/// One step on an equation between two metavariable applications.
///
/// # Specification
/// trivial.
fn flex_flex(
    left: &[Node],
    right: &[Node],
    fresh: &mut Meta,
) -> Step
{
    let (
        Some(&Node::Meta(meta, Count(count))),
        Some(&Node::Meta(other, Count(other_count))),
        Some(names),
        Some(other_names),
    ) = (left.first(), right.first(), pattern(left), pattern(right))
    else {
        return Step::Undecided;
    };
    let new = *fresh;
    *fresh = Meta(new.0.saturating_add(1));
    let projection = |count: usize, kinds: &[(usize, Binds)]| {
        let mut body = Vec::with_capacity(kinds.len().saturating_add(1));
        body.push(Node::Meta(new, Count(kinds.len())));
        body.extend(kinds.iter().map(|&(place, kind)| {
            Node::Index(kind, Count(count.saturating_sub(place.saturating_add(1))))
        }));
        Value {
            params: Count(count),
            body,
        }
    };
    if meta == other {
        if count != other_count {
            return Step::Undecided;
        }
        let kept: Vec<(usize, Binds)> = names
            .iter()
            .zip(&other_names)
            .enumerate()
            .filter(|&(_, (name, other_name))| name == other_name)
            .map(|(place, (&(kind, _), _))| (place, kind))
            .collect();
        if kept.len() == count {
            return Step::Holds;
        }
        return Step::Bind(vec![(meta, projection(count, &kept))]);
    }
    let other_place_of: BTreeMap<(Binds, Count), usize> = other_names
        .iter()
        .enumerate()
        .rev()
        .map(|(place, &name)| (name, place))
        .collect();
    let (kept, other_kept): (Vec<_>, Vec<_>) = names
        .iter()
        .enumerate()
        .filter_map(|(place, &name)| {
            let other_place = *other_place_of.get(&name)?;
            Some(((place, name.0), (other_place, name.0)))
        })
        .unzip();
    Step::Bind(vec![
        (meta, projection(count, &kept)),
        (other, projection(other_count, &other_kept)),
    ])
}

/// One step on an equation between a metavariable application and a term
/// headed by a symbol or an occurrence, standing under `depth` binders.
///
/// # Specification
/// trivial.
fn flex_rigid(
    flex: &[Node],
    rigid: &[Node],
    depth: Count,
    fresh: &mut Meta,
) -> Step
{
    let (Some(&Node::Meta(meta, params)), Some(names)) = (flex.first(), pattern(flex))
    else {
        return Step::Undecided;
    };
    if rigid
        .iter()
        .any(|&node| matches!(node, Node::Meta(other, _) if other == meta))
    {
        return Step::Apart;
    }
    let reaches = |kind: Binds, index: usize, local: usize| {
        index
            .checked_sub(local)
            .is_none_or(|free| names.contains(&(kind, Count(free))))
    };
    let rigid_depths = depths(rigid);
    let mut at = 0_usize;
    let mut kept: Vec<(usize, Binds)> = Vec::new();
    while let (Some(&node), Some(&Count(local))) = (rigid.get(at), rigid_depths.get(at)) {
        match node {
            Node::Meta(other, Count(count)) => {
                let Some(args) = end(rigid, Position(at))
                    .and_then(|stop| rigid.get(at .. stop.0))
                    .and_then(pattern)
                else {
                    return Step::Undecided;
                };
                kept.clear();
                kept.extend(
                    args.iter()
                        .enumerate()
                        .filter(|&(_, &(kind, Count(index)))| reaches(kind, index, local))
                        .map(|(place, &(kind, _))| (place, kind)),
                );
                if kept.len() < count {
                    let new = *fresh;
                    *fresh = Meta(new.0.saturating_add(1));
                    let mut body = Vec::with_capacity(kept.len().saturating_add(1));
                    body.push(Node::Meta(new, Count(kept.len())));
                    body.extend(kept.iter().map(|&(place, kind)| {
                        Node::Index(kind, Count(count.saturating_sub(place.saturating_add(1))))
                    }));
                    return Step::Bind(vec![(other, Value {
                        params: Count(count),
                        body,
                    })]);
                }
                at = at.saturating_add(count);
            },
            Node::Index(kind, Count(index)) => {
                if !reaches(kind, index, local) {
                    return Step::Apart;
                }
            },
            Node::Symbol(..) => {},
        }
        at = at.saturating_add(1);
    }
    abstraction(rigid, depth, &names).map_or(Step::Undecided, |body| {
        Step::Bind(vec![(meta, Value { params, body })])
    })
}
