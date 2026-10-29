//! The indexed reading of a presentation's rules: each operation
//! application carrying the indices its sorting fixes.
//!
//! Over a sort indexed by terms, `sort Hom(dom : Ob, cod : Ob)`, an
//! operation's ports fix indices a term does not carry: in `comp(id(a), f)`
//! the objects `comp` composes at are `a`, `a` and the codomain of `f`.
//! Unindexed, two rules' overlap can part where the sorting makes its two
//! sides one: `comp(id(a), id(b))` parts into `id(a)` and `id(b)`, and over
//! the sorting `a` is `b`. The indexed reading writes each application with
//! its implicit indices first: the variables its ports' index terms name that
//! no input port binds, in order of first occurrence, inputs before the
//! output. Each is solved by first-order unification of the sort every
//! argument stands at with the sort its port states, an index naming an input
//! port standing for that port's argument: `comp(a, a, c, id(a), f) ==> f`.
//! Over those terms an overlap unifies the indices too, so the critical pairs
//! are the well-sorted ones.
//!
//! Only an index at a rigid sort is carried. A sort is flexible when a rule's
//! side applies an operation whose output stands at it, or an operation whose
//! output stands at it takes an input at a flexible sort; every other sort is
//! rigid, and a position whose binder ranges over a flexible sort is left off
//! the sort term. A rigid term holds only rigid subterms, and no rule rewrites
//! one, so two rigid terms are equal exactly when they are one term: a clash
//! of carried indices is a clash of sorts. An index at a flexible sort, a
//! whisker's composite `comp(f, h)`, equals another only modulo the rules, so
//! it is left off, and the overlaps it would refuse are kept (#1510).
//!
//! Termination stays the written rules' own. An indexed rule strips to its
//! written rule by dropping the indices. No step rewrites inside an index,
//! which is a rigid term no rule's left side matches, so every step strips to
//! a step of the written rules.
//!
//! A presentation the reading does not cover has none, and its rules are
//! decided as written: no sort indexed; a port that binds or abstracts; an
//! operation of other than one output; an index term naming no implicit index
//! and no input port; a rule other than first-order over operation
//! applications and variables; a rule whose two sides do not sort alike; a
//! sorting that fixes a rule's variable to a term, or two of them to one; a
//! right side naming an index its left side does not fix; or a rule one of
//! whose carried indices applies an operation with indices of its own. The
//! reading only narrows the critical pairs to the well-sorted ones, so
//! declining it decides no presentation the written reading does not.
//!
//! The front end's `gandr_theory_computads::Indexing` reads a description's
//! laws the same way; the kernel re-derives the indices from the value rather
//! than trusting the producer's.
//!
//! # References
//!
//! - John Cartmell. "Generalised Algebraic Theories and Contextual Categories."
//!   _Annals of Pure and Applied Logic_ 32 (1986), pages 209–243 — sorts
//!   indexed by terms, and an operation's implicit arguments: the indices its
//!   sorting fixes.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use crate::StringLiteral;
use crate::ValueId;
use crate::presented::FieldCount;
use crate::presented::RewriteFuel;
use crate::presented::RuleVariable;
use crate::term::ConstructorTag;
use crate::theory_rules::Class;
use crate::theory_rules::Flat;
use crate::theory_rules::Graph;
use crate::theory_rules::GraphNode;
use crate::theory_rules::Mark;
use crate::theory_rules::Node;
use crate::theory_rules::Ordinal;
use crate::theory_rules::PRESENTATION_FUEL;
use crate::theory_rules::Position;
use crate::theory_rules::Reader;
use crate::theory_rules::Reading;
use crate::theory_rules::Span;
use crate::theory_rules::TheoryNode;
use crate::theory_rules::TheoryRule;
use crate::theory_rules::TheorySymbol;
use crate::theory_rules::Verdict;
use crate::theory_rules::first_seen;
use crate::theory_rules::ordinal;
use crate::theory_rules::tag;

/// The first symbol a sort is read as in the unifier's graph: far past every
/// symbol a rule interns, so a sort is never one of them, and an index that
/// resolves to a sort is refused rather than read.
const SORT_BASE: usize = usize::MAX >> 1;

/// The sort a port states: its sort's name and the chain of its index terms.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct PortSort<'arena>
{
    /// The sort's name.
    sort: &'arena StringLiteral,
    /// The `Arg` chain of its index terms.
    indices: ValueId,
}

/// What a `Var` of a port's index term names: one of the operation's
/// implicit indices, or one of its input ports, by place.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Named
{
    /// The implicit index at this place.
    Implicit(Position),
    /// The input port at this place.
    Input(Position),
}

/// One operation's sorting, as the value states it.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Sorting<'arena>
{
    /// Its implicit indices: the variables its ports' index terms name that no
    /// input port binds, in order of first occurrence, inputs first.
    implicits: Vec<&'arena StringLiteral>,
    /// Each input port's name and sort, in order.
    inputs: Vec<(&'arena StringLiteral, PortSort<'arena>)>,
    /// Its one output's sort.
    output: PortSort<'arena>,
    /// What each name an index term may name stands for.
    named: BTreeMap<&'arena StringLiteral, Named>,
}

/// The sorting of each operation of an indexed presentation, by name, and the
/// index positions it leaves off.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub(super) struct Signature<'arena>
{
    /// Each operation's sorting over the indices it carries, by name.
    operations: BTreeMap<&'arena StringLiteral, Sorting<'arena>>,
    /// Each indexed sort's positions whose binder ranges over a flexible
    /// sort, which no sort term carries.
    dropped: BTreeMap<&'arena StringLiteral, BTreeSet<usize>>,
}

impl Signature<'_>
{
    /// Whether `name` is an operation applied at indices of its own.
    ///
    /// # Specification
    /// trivial.
    fn implicit(
        &self,
        name: &StringLiteral,
    ) -> Verdict
    {
        Verdict::from(
            self.operations
                .get(name)
                .is_some_and(|sorting| !sorting.implicits.is_empty()),
        )
    }
}

/// One node of a sort term as it is read, before the graph holds it: a symbol
/// over its next subterms, or a node the graph already holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Item
{
    /// A symbol over the next `FieldCount` subterms.
    Symbol(TheorySymbol, FieldCount),
    /// A node of the graph: an index, or the argument an input port names.
    Held(Node),
}

/// A node of a side read into the graph: the term it is and the sort it
/// stands at.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Sorted
{
    /// The term's node.
    term: Node,
    /// Its sort's node.
    sort: Node,
}

/// The buffers one rule's indexed reading is solved in, reused across rules.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Indexer<'arena>
{
    /// The unifier's graph, terms and sorts alike.
    graph: Graph,
    /// Each rule variable's term node, by ordinal.
    terms: Vec<Option<Node>>,
    /// Each rule variable's sort node, by ordinal.
    sorts: Vec<Option<Node>>,
    /// The sorted nodes of the side being read, the next argument on top.
    stack: Vec<Sorted>,
    /// The arguments of the application being read, in order.
    arguments: Vec<Sorted>,
    /// Every application's implicit indices, end to end.
    implicits: Vec<Node>,
    /// Where each position of the left side keeps its implicit indices.
    left: Vec<Option<Span>>,
    /// Where each position of the right side keeps its implicit indices.
    right: Vec<Option<Span>>,
    /// A sort term's nodes in pre-order.
    items: Vec<Item>,
    /// The nodes a sort term is built from.
    built: Vec<Node>,
    /// The index terms still to read.
    pending: Vec<ValueId>,
    /// The unifier's pairs.
    pairs: Vec<(Node, Node)>,
    /// An implicit index, flattened.
    flat: Vec<Flat>,
    /// The flattening's stack.
    flattening: Vec<Node>,
    /// The occurs check's marks.
    marks: Vec<Mark>,
    /// The occurs check's walk.
    walk: Vec<(Node, Position)>,
    /// The indices no rule variable is, in order of first meeting.
    unknowns: Vec<Node>,
    /// Each sort's symbol in the graph, by its name.
    sort_symbols: BTreeMap<&'arena StringLiteral, TheorySymbol>,
}

impl<'arena> Reader<'arena>
{
    /// The signature of the operations, when some sort of the chain `sorts` is
    /// indexed and the chain `operations` is one the indexed reading covers.
    ///
    /// # Specification
    /// - ensures: [`Some`] when a `Sort`, `Representable`, `Atom` or
    ///   `Computation` of `sorts` has an index port, each index port a `Port`,
    ///   and every `Oper`, `Obs`, `Const` and `Nested` of `operations` has a
    ///   distinct name, only `Port` inputs and one `Port` output, each index
    ///   term a `Var`, or an `App` or `Con` over its `Arg` chain. A position is
    ///   left off when its binder ranges over a flexible sort (see the module
    ///   documentation), the rules read so far seeding the flexible sorts; each
    ///   operation's implicit indices are the names its ports' carried index
    ///   terms' `Var`s name that no input port does, in pre-order, inputs then
    ///   the output, each once. [`None`] otherwise.
    /// - panics: none.
    /// - executable: none — the answer is the walk of the two chains.
    /// - intension: one walk of each chain, each index term read from a
    ///   worklist, the flexible sorts grown to their least fixed point.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a category's composition is implicit in its three
    ///   objects and its identity in none, so its laws read indexed; a plain
    ///   signature has no indexed reading.
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    pub(super) fn signature(
        &self,
        sorts: ValueId,
        operations: ValueId,
    ) -> Option<Signature<'arena>>
    {
        let tagged = |found: Option<(ConstructorTag, &'arena [ValueId])>| {
            found.map(|(tag, fields)| (usize::from(tag), fields))
        };
        let mut binders = Vec::new();
        let mut at = sorts;
        loop {
            at = match tagged(self.constructor(at))? {
                (tag::END, &[]) => break,
                (
                    tag::SORT | tag::REPRESENTABLE | tag::ATOM | tag::COMPUTATION,
                    &[name, ports, rest],
                ) => {
                    if !matches!(tagged(self.constructor(ports)), Some((tag::END, &[]))) {
                        binders.push((self.text(name)?, self.port_sorts(ports)?));
                    }
                    rest
                },
                (tag::SHAPE, &[_, _, _, rest]) => rest,
                _ => return None,
            };
        }
        if binders.is_empty() {
            return None;
        }
        let mut read = Vec::new();
        let mut at = operations;
        loop {
            let (name, inputs, outputs, rest) = match tagged(self.constructor(at))? {
                (tag::END, &[]) => break,
                (
                    tag::OPER | tag::OBS | tag::CONST | tag::NESTED,
                    &[name, inputs, outputs, rest],
                ) => (self.text(name)?, inputs, outputs, rest),
                _ => return None,
            };
            let inputs = self.port_sorts(inputs)?;
            let outputs = self.port_sorts(outputs)?;
            let &[(_, output)] = outputs.as_slice()
            else {
                return None;
            };
            read.push((name, inputs, output));
            at = rest;
        }
        let outputs: BTreeMap<&StringLiteral, &StringLiteral> = read
            .iter()
            .map(|&(name, _, output)| (name, output.sort))
            .collect();
        let mut flexible: BTreeSet<&StringLiteral> = BTreeSet::new();
        for rule in &self.rules {
            for side in [rule.left(), rule.right()] {
                if let Some(&TheoryNode::Symbol(symbol)) = side.first()
                    && let Some(&(Class::Operation, Some(name), _)) = self.keys.get(symbol.0)
                    && let Some(&sort) = outputs.get(name)
                {
                    let _first = flexible.insert(sort);
                }
            }
        }
        loop {
            let before = flexible.len();
            for &(_, ref inputs, output) in &read {
                if inputs.iter().any(|&(_, port)| flexible.contains(port.sort)) {
                    let _first = flexible.insert(output.sort);
                }
            }
            if flexible.len() == before {
                break;
            }
        }
        let dropped = binders
            .iter()
            .filter_map(|&(name, ref ports)| {
                let left: BTreeSet<usize> = ports
                    .iter()
                    .enumerate()
                    .filter(|&(_, &(_, port))| flexible.contains(port.sort))
                    .map(|(place, _)| place)
                    .collect();
                (!left.is_empty()).then_some((name, left))
            })
            .collect();
        let mut signature = Signature {
            operations: BTreeMap::new(),
            dropped,
        };
        let mut pending = Vec::new();
        for (name, inputs, output) in read {
            let mut named: BTreeMap<&'arena StringLiteral, Named> = inputs
                .iter()
                .enumerate()
                .map(|(place, &(input, _))| (input, Named::Input(Position(place))))
                .collect();
            let mut implicits = Vec::new();
            for port in inputs.iter().map(|&(_, port)| port).chain([output]) {
                let _count = self.carried_terms(port, &signature, &mut pending)?;
                while let Some(term) = pending.pop() {
                    match tagged(self.constructor(term))? {
                        (tag::VAR, &[variable]) => {
                            let variable = self.text(variable)?;
                            if !named.contains_key(variable) {
                                named.insert(variable, Named::Implicit(Position(implicits.len())));
                                implicits.push(variable);
                            }
                        },
                        (tag::APP | tag::CON, &[_, chain]) => {
                            let _count = self.index_terms(chain, &mut pending)?;
                        },
                        _ => return None,
                    }
                }
            }
            let sorting = Sorting {
                implicits,
                inputs,
                output,
                named,
            };
            if signature.operations.insert(name, sorting).is_some() {
                return None;
            }
        }
        Some(signature)
    }

    /// Each port of the chain `ports`, by its name and sort.
    ///
    /// # Specification
    /// - ensures: [`Some`] with one entry per `Port` member, in order; [`None`]
    ///   at any other member but `End`.
    /// - panics: none.
    /// - executable: none — the ports are the chain's own fields, read once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn port_sorts(
        &self,
        mut ports: ValueId,
    ) -> Option<Vec<(&'arena StringLiteral, PortSort<'arena>)>>
    {
        let mut read = Vec::new();
        loop {
            match self
                .constructor(ports)
                .map(|(tag, fields)| (usize::from(tag), fields))?
            {
                (tag::END, &[]) => return Some(read),
                (tag::PORT, &[name, sort, indices, rest]) => {
                    read.push((self.text(name)?, PortSort {
                        sort: self.text(sort)?,
                        indices,
                    }));
                    ports = rest;
                },
                _ => return None,
            }
        }
    }

    /// Push the terms of the `Arg` chain `chain` onto `pending`, last first,
    /// so the first is popped first; their count.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the chain's length when it is `Arg`s ended by
    ///   `End`, each term pushed; [`None`] otherwise, `pending` then holding
    ///   what it held.
    /// - panics: none.
    /// - executable: none — the terms pushed are the chain's own fields, and
    ///   `pending`'s prior contents are not named by any predicate's inputs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn index_terms(
        &self,
        mut chain: ValueId,
        pending: &mut Vec<ValueId>,
    ) -> Option<FieldCount>
    {
        let start = pending.len();
        loop {
            match self
                .constructor(chain)
                .map(|(tag, fields)| (usize::from(tag), fields))
            {
                Some((tag::END, &[])) => break,
                Some((tag::ARG, &[term, rest])) => {
                    pending.push(term);
                    chain = rest;
                },
                Some(_) | None => {
                    pending.truncate(start);
                    return None;
                },
            }
        }
        let terms = pending.get_mut(start ..)?;
        terms.reverse();
        Some(FieldCount::from(terms.len()))
    }

    /// Push the index terms `port`'s sort carries under `signature` onto
    /// `pending` as [`Self::index_terms`] does, leaving off each position
    /// `signature` drops from the sort; their count.
    ///
    /// # Specification
    /// - ensures: as [`Self::index_terms`] over the chain `port.indices`, each
    ///   term at a position `signature` drops from `port.sort` removed, the
    ///   rest in order.
    /// - panics: none.
    /// - executable: none — as [`Self::index_terms`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a 2-cell's homs are left off under a law of
    ///   composition, and a hom's objects are kept.
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn carried_terms(
        &self,
        port: PortSort<'arena>,
        signature: &Signature<'arena>,
        pending: &mut Vec<ValueId>,
    ) -> Option<FieldCount>
    {
        let start = pending.len();
        let count = usize::from(self.index_terms(port.indices, pending)?);
        let Some(dropped) = signature.dropped.get(port.sort)
        else {
            return Some(FieldCount::from(count));
        };
        // The terms stand last first, so the one at `place` from the end is
        // the chain's position `place`.
        let mut write = start;
        for (read, place) in (start .. pending.len()).zip((0 .. count).rev()) {
            if !dropped.contains(&place) {
                pending.swap(write, read);
                write = write.checked_add(1)?;
            }
        }
        pending.truncate(write);
        Some(FieldCount::from(write.checked_sub(start)?))
    }

    /// Every rule read, written and derived, in the indexed reading under
    /// `signature`, each operation application carrying its implicit indices.
    ///
    /// # Specification
    /// - ensures: [`Some`] with one rule per rule read, in order, when the
    ///   reading covers every one (see the module documentation): each
    ///   operation application's symbol the operation's at its port count and
    ///   implicit indices together, its indices first, each the most general
    ///   term the two sides' sorting fixes, an index the left side does not fix
    ///   a variable of its own; every variable renumbered by its first
    ///   occurrence on the left side, then the right. [`None`] when the reading
    ///   covers some rule not, or solving it runs past [`PRESENTATION_FUEL`].
    /// - panics: none.
    /// - executable: none — the rules returned are the solution itself.
    /// - intension: one graph per rule, its sides read from the leaves up, so
    ///   no step recurses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a category's unit laws carry the objects their
    ///   variables fix, and their overlap is one well-sorted term.
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    pub(super) fn indexed(
        &mut self,
        signature: &Signature<'arena>,
    ) -> Option<Vec<TheoryRule>>
    {
        if self
            .rules
            .iter()
            .any(|rule| rule.reading() == Reading::SecondOrder)
        {
            return None;
        }
        let mut fuel = RewriteFuel::from(PRESENTATION_FUEL);
        let mut indexer = Indexer::default();
        let rules = core::mem::take(&mut self.rules);
        let indexed = rules
            .iter()
            .map(|rule| indexer.rule(self, signature, rule, &mut fuel))
            .collect();
        self.rules = rules;
        indexed
    }
}

impl<'arena> Indexer<'arena>
{
    /// `rule` in the indexed reading, as [`Reader::indexed`] reads each rule.
    ///
    /// # Specification
    /// - ensures: as [`Reader::indexed`], for one rule.
    /// - panics: none.
    /// - executable: none — as [`Reader::indexed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader::indexed`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn rule(
        &mut self,
        reader: &mut Reader<'arena>,
        signature: &Signature<'arena>,
        rule: &TheoryRule,
        fuel: &mut RewriteFuel,
    ) -> Option<TheoryRule>
    {
        self.graph.clear();
        self.terms.clear();
        self.sorts.clear();
        self.implicits.clear();
        self.unknowns.clear();
        let mut left = core::mem::take(&mut self.left);
        let mut right = core::mem::take(&mut self.right);
        let sides = self
            .side(reader, signature, rule.left(), &mut left, fuel)
            .zip(self.side(reader, signature, rule.right(), &mut right, fuel));
        let solved = sides.and_then(|(from, to)| {
            (self
                .graph
                .unify(from.sort, to.sort, &mut self.pairs, fuel)
                .ok()?
                == Verdict::Holds)
                .then_some((from, to))
        });
        let indexed = solved.and_then(|(from, to)| {
            self.fixes_no_variable()?;
            for root in [from.sort, to.sort]
                .into_iter()
                .chain(self.implicits.iter().copied())
                .chain(self.sorts.iter().flatten().copied())
            {
                if self.graph.acyclic(root, &mut self.marks, &mut self.walk) == Verdict::Fails {
                    return None;
                }
            }
            let variables = Ordinal(self.terms.len());
            let mut sides = (Vec::new(), Vec::new());
            self.expanded(
                reader,
                signature,
                (rule.left(), &left),
                (&mut sides.0, variables),
                fuel,
            )?;
            self.expanded(
                reader,
                signature,
                (rule.right(), &right),
                (&mut sides.1, variables),
                fuel,
            )?;
            renumbered(&mut sides.0, &mut sides.1)?;
            Some(TheoryRule::new(sides.0.into(), sides.1.into()))
        });
        self.left = left;
        self.right = right;
        indexed
    }

    /// Read `side` into the graph: each node's term and the sort it stands
    /// at, each application's arguments unified with its ports' sorts and
    /// its implicit indices kept in `at` by position.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the root's term and sort when every node is a
    ///   variable, sharing its term and sort nodes across the rule, or an
    ///   operation application at its sorting's port count whose every
    ///   argument's sort unifies with its port's; `at` then holds, by position,
    ///   the span of `self.implicits` each application's indices take. [`None`]
    ///   otherwise.
    /// - panics: none.
    /// - executable: none — the graph built is the reading's own state.
    /// - intension: the side read from its last node to its first, each
    ///   application taking its arguments off a stack, as [`Graph::load`] does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader::indexed`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn side(
        &mut self,
        reader: &mut Reader<'arena>,
        signature: &Signature<'arena>,
        side: &[TheoryNode],
        at: &mut Vec<Option<Span>>,
        fuel: &mut RewriteFuel,
    ) -> Option<Sorted>
    {
        self.stack.clear();
        at.clear();
        at.resize(side.len(), None);
        for (position, &node) in side.iter().enumerate().rev() {
            let sorted = match node {
                TheoryNode::Variable(variable) => Sorted {
                    term: variable_node(&mut self.graph, &mut self.terms, ordinal(variable))?,
                    sort: variable_node(&mut self.graph, &mut self.sorts, ordinal(variable))?,
                },
                TheoryNode::Instance(..) => return None,
                TheoryNode::Symbol(symbol) => {
                    let &(class, name, arity) = reader.keys.get(symbol.0)?;
                    let (Class::Operation, Some(name)) = (class, name)
                    else {
                        return None;
                    };
                    let sorting = signature.operations.get(name)?;
                    if usize::from(arity) != sorting.inputs.len() {
                        return None;
                    }
                    self.arguments.clear();
                    for _ in 0 .. sorting.inputs.len() {
                        let argument = self.stack.pop()?;
                        self.arguments.push(argument);
                    }
                    let first = Position(self.graph.children.len());
                    self.graph
                        .children
                        .extend(self.arguments.iter().map(|argument| argument.term));
                    self.graph.nodes.push(GraphNode::Symbol {
                        symbol,
                        first,
                        arity: self.arguments.len(),
                    });
                    let term = Node(self.graph.nodes.len().saturating_sub(1));
                    let from = Position(self.implicits.len());
                    for _ in &sorting.implicits {
                        self.graph.nodes.push(GraphNode::Variable(None));
                        self.implicits
                            .push(Node(self.graph.nodes.len().saturating_sub(1)));
                    }
                    let span = Span {
                        from,
                        to: Position(self.implicits.len()),
                    };
                    for (place, &(_, port)) in sorting.inputs.iter().enumerate() {
                        let stated = self.instantiated(reader, signature, sorting, port, span)?;
                        let argument = self.arguments.get(place)?.sort;
                        if self
                            .graph
                            .unify(argument, stated, &mut self.pairs, fuel)
                            .ok()?
                            == Verdict::Fails
                        {
                            return None;
                        }
                    }
                    let sort =
                        self.instantiated(reader, signature, sorting, sorting.output, span)?;
                    *at.get_mut(position)? = Some(span);
                    Sorted { term, sort }
                },
            };
            self.stack.push(sorted);
        }
        let root = self.stack.pop()?;
        self.stack.is_empty().then_some(root)
    }

    /// The sort `port` states, built in the graph for the application whose
    /// implicit indices `span` holds and whose arguments are
    /// `self.arguments`.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the node of the sort's name applied to the
    ///   index terms `signature` carries, a `Var` naming one of `sorting`'s
    ///   implicit indices that index's node, one naming an input port that
    ///   port's argument, an `App` or `Con` the symbol its name and argument
    ///   count intern to; [`None`] at a `Var` naming neither, or any other
    ///   node.
    /// - panics: none.
    /// - executable: none — the nodes built are the graph's own state.
    /// - intension: the term read in pre-order from a worklist, then built from
    ///   its last node to its first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader::indexed`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn instantiated(
        &mut self,
        reader: &mut Reader<'arena>,
        signature: &Signature<'arena>,
        sorting: &Sorting<'arena>,
        port: PortSort<'arena>,
        span: Span,
    ) -> Option<Node>
    {
        let fresh = TheorySymbol(SORT_BASE.saturating_add(self.sort_symbols.len()));
        let sort = *self.sort_symbols.entry(port.sort).or_insert(fresh);
        self.items.clear();
        self.pending.clear();
        let count = reader.carried_terms(port, signature, &mut self.pending)?;
        self.items.push(Item::Symbol(sort, count));
        while let Some(term) = self.pending.pop() {
            let item = match reader
                .constructor(term)
                .map(|(tag, fields)| (usize::from(tag), fields))?
            {
                (tag::VAR, &[name]) => {
                    let name = reader.text(name)?;
                    let held = match *sorting.named.get(name)? {
                        Named::Implicit(Position(place)) => {
                            *self.implicits.get(span.from.0.checked_add(place)?)?
                        },
                        Named::Input(Position(place)) => self.arguments.get(place)?.term,
                    };
                    Item::Held(held)
                },
                (kind @ (tag::APP | tag::CON), &[name, chain]) => {
                    let class = if kind == tag::APP {
                        Class::Operation
                    }
                    else {
                        Class::Constructor
                    };
                    let count = reader.index_terms(chain, &mut self.pending)?;
                    let name = reader.text(name)?;
                    let symbol = reader.intern((class, Some(name), count));
                    Item::Symbol(symbol, count)
                },
                _ => return None,
            };
            self.items.push(item);
        }
        self.built.clear();
        for &item in self.items.iter().rev() {
            let node = match item {
                Item::Held(node) => node,
                Item::Symbol(symbol, count) => {
                    let first = Position(self.graph.children.len());
                    for _ in 0 .. usize::from(count) {
                        let child = self.built.pop()?;
                        self.graph.children.push(child);
                    }
                    self.graph.nodes.push(GraphNode::Symbol {
                        symbol,
                        first,
                        arity: usize::from(count),
                    });
                    Node(self.graph.nodes.len().saturating_sub(1))
                },
            };
            self.built.push(node);
        }
        let root = self.built.pop()?;
        self.built.is_empty().then_some(root)
    }

    /// Whether the solution leaves every rule variable a free variable of its
    /// own: the sorting fixes none to a term, and none to another.
    ///
    /// # Specification
    /// - ensures: [`Some`] exactly when every rule variable's term node
    ///   resolves to a free variable no other rule variable's resolves to.
    /// - panics: none.
    /// - executable: none — the solution is the graph's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader::indexed`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn fixes_no_variable(&self) -> Option<()>
    {
        let mut resolved: BTreeSet<Node> = BTreeSet::new();
        for &term in self.terms.iter().flatten() {
            let node = self.graph.resolve(term);
            if !matches!(
                self.graph.nodes.get(node.0),
                Some(&GraphNode::Variable(None))
            ) || !resolved.insert(node)
            {
                return None;
            }
        }
        Some(())
    }

    /// Write `side` into `out` with each application's implicit indices, kept
    /// in `at` by position, first: the application's symbol at its port
    /// count and indices together, then each index flattened, a rule
    /// variable's node as that variable and any other free node as a
    /// variable numbered from `variables` up, then the side's own nodes.
    ///
    /// # Specification
    /// - ensures: [`Some`] when every index flattens to operations and
    ///   constructors with no implicit indices of their own and variables, no
    ///   sort among them. [`None`] otherwise, or when `fuel` runs out.
    /// - panics: none.
    /// - executable: none — the side written is the reading's result.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader::indexed`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn expanded(
        &mut self,
        reader: &mut Reader<'arena>,
        signature: &Signature<'arena>,
        (side, at): (&[TheoryNode], &[Option<Span>]),
        (out, Ordinal(variables)): (&mut Vec<TheoryNode>, Ordinal),
        fuel: &mut RewriteFuel,
    ) -> Option<()>
    {
        let mut held: BTreeMap<Node, usize> = BTreeMap::new();
        for (place, &term) in self.terms.iter().enumerate() {
            if let Some(term) = term {
                let _first = *held.entry(self.graph.resolve(term)).or_insert(place);
            }
        }
        for (position, &node) in side.iter().enumerate() {
            let TheoryNode::Symbol(symbol) = node
            else {
                out.push(node);
                continue;
            };
            let span = (*at.get(position)?)?;
            let &(class, name, arity) = reader.keys.get(symbol.0)?;
            let count = span.to.0.checked_sub(span.from.0)?;
            let carried = FieldCount::from(usize::from(arity).checked_add(count)?);
            out.push(TheoryNode::Symbol(reader.intern((class, name, carried))));
            for index in span.from.0 .. span.to.0 {
                let implicit = *self.implicits.get(index)?;
                self.graph
                    .expand(implicit, &mut self.flat, &mut self.flattening, fuel)
                    .ok()?;
                for &flat in &self.flat {
                    let written = match flat {
                        Flat::Symbol(symbol, _) => {
                            let &(class, name, _) = reader.keys.get(symbol.0)?;
                            let own = match (class, name) {
                                (Class::Operation, Some(name)) => signature.implicit(name),
                                (Class::Constructor, _) => Verdict::Fails,
                                (
                                    Class::Operation
                                    | Class::Tuple
                                    | Class::Abstraction
                                    | Class::Occurrence(_)
                                    | Class::Field
                                    | Class::BoundVariable(_),
                                    _,
                                ) => Verdict::Holds,
                            };
                            if own == Verdict::Holds {
                                return None;
                            }
                            TheoryNode::Symbol(symbol)
                        },
                        Flat::Variable(free) => {
                            let place = if let Some(&place) = held.get(&free) {
                                place
                            }
                            else {
                                let Ordinal(unknown) = first_seen(&mut self.unknowns, free);
                                variables.checked_add(unknown)?
                            };
                            TheoryNode::Variable(RuleVariable::from(u32::try_from(place).ok()?))
                        },
                    };
                    out.push(written);
                }
            }
        }
        Some(())
    }
}

/// The node `slots` holds for the variable at `ordinal`, made free and kept
/// when it holds none.
///
/// # Specification
/// trivial.
fn variable_node(
    graph: &mut Graph,
    slots: &mut Vec<Option<Node>>,
    Ordinal(ordinal): Ordinal,
) -> Option<Node>
{
    if slots.len() <= ordinal {
        slots.resize(ordinal.checked_add(1)?, None);
    }
    let slot = slots.get_mut(ordinal)?;
    if let Some(node) = *slot {
        return Some(node);
    }
    graph.nodes.push(GraphNode::Variable(None));
    let node = Node(graph.nodes.len().saturating_sub(1));
    *slot = Some(node);
    Some(node)
}

/// Number the variables of `left` and `right` by first occurrence on `left`,
/// then on `right`.
///
/// # Specification
/// - ensures: [`Some`] with every variable renumbered so when each variable of
///   `right` occurs on `left`; [`None`] otherwise, the sides then partly
///   renumbered.
/// - panics: none.
/// - executable: none — the sides renumbered in place are the result.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Reader::indexed`].
/// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
fn renumbered(
    left: &mut [TheoryNode],
    right: &mut [TheoryNode],
) -> Option<()>
{
    let mut seen: Vec<RuleVariable> = Vec::new();
    for node in left.iter_mut() {
        if let TheoryNode::Variable(ref mut variable) = *node {
            let Ordinal(place) = first_seen(&mut seen, *variable);
            *variable = RuleVariable::from(u32::try_from(place).ok()?);
        }
    }
    let bound = seen.len();
    for node in right.iter_mut() {
        if let TheoryNode::Variable(ref mut variable) = *node {
            let Ordinal(place) = first_seen(&mut seen, *variable);
            if place >= bound {
                return None;
            }
            *variable = RuleVariable::from(u32::try_from(place).ok()?);
        }
    }
    Some(())
}
