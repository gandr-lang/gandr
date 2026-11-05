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
//! A sort is flexible when a rule's side applies an operation whose output
//! stands at it, or an operation whose output stands at it takes an input at
//! a flexible sort; every other sort is rigid. A rigid term holds only rigid
//! subterms, and no rule rewrites one, so two rigid terms are equal exactly
//! when they are one term. An index at a flexible sort, a context of a
//! category with families, equals another only modulo the rules.
//!
//! The reading first carries every index. It keeps that reading when every
//! rule reads in it and the path order over the stated ranks orients each
//! rule so read, an operation's written arguments compared before its indices
//! ([`gandr_theory_path_orders::Status::Explicit`]) (#5016). Otherwise a
//! position whose binder ranges over a flexible sort is left off the sort
//! term, and the overlaps it would refuse are kept (#1510).
//!
//! Termination holds either way. Where every index is carried, a step may
//! rewrite inside an index, and the path order orients every rule that
//! carries it, so the indexed rules terminate on their own. Otherwise an
//! index is rigid, no step rewrites inside one, and every step strips to a
//! step of the written rules, which terminate. An overlap that the carried
//! indices refuse is no peak of the indexed rules: no term carrying its
//! indices holds both redexes. By the critical pair lemma the indexed rules
//! then lose no peak.
//!
//! A port's sort may apply an operation with indices of its own, as a term
//! substitution's `Tm(d, subTy(a, s))` does, and the reading carries that
//! index with the indices its operation's sorting fixes (#5042). Each rule has
//! a rank: the position of its left side's sort among the sorts. Its two
//! sides sort alike modulo the rules of lower rank, each side's sort
//! normalized under them, as a generalized algebraic theory orders its
//! equations.
//!
//! A presentation the reading does not cover has none, and its rules are
//! decided as written: no sort indexed; a port that binds or abstracts; an
//! operation of other than one output; an index term naming no implicit index
//! and no input port; a rule other than first-order over operation
//! applications and variables; a rule whose two sides do not sort alike modulo
//! the rules of lower rank; a sorting that fixes a rule's variable to a term,
//! or two of them to one; or a right side naming an index its left side does
//! not fix. The reading only narrows the critical pairs to the well-sorted
//! ones, so declining it decides no presentation the written reading does not.
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

use alloc::boxed::Box;
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
use crate::theory_rules::normal_form;
use crate::theory_rules::ordinal;
use crate::theory_rules::tag;

/// The first symbol a sort is read as in the unifier's graph: far past every
/// symbol a rule interns, so a sort is never one of them, and an index that
/// resolves to a sort is refused rather than read.
const SORT_BASE: usize = usize::MAX >> 1;

/// The first symbol an operation's own name is read as while its ports' sorts
/// are elaborated: past every sort's symbol, so a name stands as a constant no
/// unifier binds, and no symbol a rule interns is one.
const NAMED_BASE: usize = SORT_BASE.saturating_add(usize::MAX >> 2);

/// The place of a sort in the sort chain: a rule's sort is the sort its left
/// side's operation outputs, and a rule is read modulo the rules of lower
/// rank.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rank(usize);

/// One node of a port's carried sort, in pre-order: a symbol over its next
/// subterms, or a name the operation's sorting binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Stated
{
    /// A symbol over the next `FieldCount` subterms.
    Symbol(TheorySymbol, FieldCount),
    /// An implicit index or an input port of the operation.
    Named(Named),
}

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
    /// Each port's sort over the indices the reading carries, the inputs in
    /// order and then the output: each index that applies an operation with
    /// indices of its own carries them, where the ports fix them.
    stated: Vec<Box<[Stated]>>,
}

/// Which index positions the indexed reading carries.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Carry
{
    /// Only the positions whose binder ranges over a rigid sort.
    Rigid,
    /// Every position.
    Every,
}

/// The sorting of each operation of an indexed presentation, by name, and the
/// index positions at a flexible sort.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub(super) struct Signature<'arena>
{
    /// Each operation's sorting over the indices it carries, by name.
    operations: BTreeMap<&'arena StringLiteral, Sorting<'arena>>,
    /// Each indexed sort's positions whose binder ranges over a flexible
    /// sort.
    dropped: BTreeMap<&'arena StringLiteral, BTreeSet<usize>>,
    /// Which positions the sort terms carry: under [`Carry::Rigid`] no sort
    /// term carries a position of `dropped`.
    carry: Carry,
    /// The rank of each operation's output sort, by the operation's name.
    ranks: BTreeMap<&'arena StringLiteral, Rank>,
}

impl Signature<'_>
{
    /// Whether `name` is an operation with indices of its own applied at
    /// `arity`, its port count alone: an index the reading does not carry.
    ///
    /// # Specification
    /// trivial.
    fn uncarried(
        &self,
        name: &StringLiteral,
        arity: FieldCount,
    ) -> Verdict
    {
        Verdict::from(self.operations.get(name).is_some_and(|sorting| {
            !sorting.implicits.is_empty() && usize::from(arity) == sorting.inputs.len()
        }))
    }

    /// Whether some index position stands at a flexible sort.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn flexible(&self) -> Verdict
    {
        Verdict::from(!self.dropped.is_empty())
    }

    /// The number of input ports of the operation `name`, when it declares
    /// one.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn inputs(
        &self,
        name: &StringLiteral,
    ) -> Option<FieldCount>
    {
        self.operations
            .get(name)
            .map(|sorting| FieldCount::from(sorting.inputs.len()))
    }
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
struct Indexer
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
    /// The nodes a sort term is built from.
    built: Vec<Node>,
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
    /// Each variable's binding as a sort is normalized.
    bindings: Vec<Option<Span>>,
    /// A right side as a sort's normalization builds it.
    rewritten: Vec<Flat>,
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
    ///   term a `Var`, or an `App` or `Con` over its `Arg` chain. A position
    ///   whose binder ranges over a flexible sort (see the module
    ///   documentation) is recorded as flexible, the rules read so far seeding
    ///   the flexible sorts, and under [`Carry::Rigid`] it is left off; each
    ///   operation's implicit indices are the names its ports' carried index
    ///   terms' `Var`s name that no input port does, in pre-order, inputs then
    ///   the output, each once. Each port's sort is elaborated
    ///   ([`Self::stated`]) under the operations before it, and each operation
    ///   ranks as its output sort's place in `sorts`. [`None`] otherwise.
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
    /// - witness: `theory_rules::tests::a_cwfs_laws_join_over_every_index_5016`
    pub(super) fn signature(
        &mut self,
        sorts: ValueId,
        operations: ValueId,
        carry: Carry,
    ) -> Option<Signature<'arena>>
    {
        let tagged = |found: Option<(ConstructorTag, &'arena [ValueId])>| {
            found.map(|(tag, fields)| (usize::from(tag), fields))
        };
        let mut binders = Vec::new();
        let mut ranked: BTreeMap<&'arena StringLiteral, Rank> = BTreeMap::new();
        let mut at = sorts;
        loop {
            at = match tagged(self.constructor(at))? {
                (tag::END, &[]) => break,
                (
                    tag::SORT | tag::REPRESENTABLE | tag::ATOM | tag::COMPUTATION,
                    &[name, ports, rest],
                ) => {
                    let text = self.text(name)?;
                    let _first = ranked.insert(text, Rank(ranked.len()));
                    if !matches!(tagged(self.constructor(ports)), Some((tag::END, &[]))) {
                        binders.push((text, self.port_sorts(ports)?));
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
        let ranks = read
            .iter()
            .filter_map(|&(name, _, output)| Some((name, *ranked.get(output.sort)?)))
            .collect();
        let mut signature = Signature {
            operations: BTreeMap::new(),
            dropped,
            carry,
            ranks,
        };
        let mut fuel = RewriteFuel::from(PRESENTATION_FUEL);
        let mut pending = Vec::new();
        let mut named: BTreeMap<&'arena StringLiteral, Named> = BTreeMap::new();
        for (name, inputs, output) in read {
            named.clear();
            named.extend(
                inputs
                    .iter()
                    .enumerate()
                    .map(|(place, &(input, _))| (input, Named::Input(Position(place)))),
            );
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
            let stated = self.stated(
                (&inputs, output),
                (&named, &implicits),
                (&signature, &ranked),
                &mut fuel,
            )?;
            let sorting = Sorting {
                implicits,
                inputs,
                stated,
            };
            if signature.operations.insert(name, sorting).is_some() {
                return None;
            }
        }
        Some(signature)
    }

    /// Each port's sort over the indices `signature` carries, for the
    /// operation whose ports are `inputs` and `output` and whose names are
    /// `named`: the inputs in order, then the output.
    ///
    /// # Specification
    /// - ensures: [`Some`] with one template per port, each its sort's symbol
    ///   (`SORT_BASE` above its rank in `ranked`) over its carried index terms
    ///   ([`Self::carried_terms`]). An index term that is a variable stands as
    ///   written. Every other one is read in one graph for the whole operation:
    ///   each application of an operation `signature` holds at its port count
    ///   carries fresh implicit indices, its arguments' sorts unified with its
    ///   ports' templates, an input port's variable at that port's sort once
    ///   its port is read and a fresh sort before; each of the operation's own
    ///   names is a constant. Such a term stands as read when it resolves to
    ///   the operation's names and symbols alone, and as written where its
    ///   reading meets a constructor, an operation `signature` does not hold at
    ///   that count, or a sort that does not unify, or leaves an index unfixed.
    ///   [`None`] when a port's sort has no rank, a term is not one the reading
    ///   covers, or `fuel` runs out.
    /// - panics: none.
    /// - executable: none — the templates are the solution itself.
    /// - intension: each index term read in pre-order from a worklist, then
    ///   built from its last node to its first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the type a term substitution moves its term's type to
    ///   carries the two contexts the substitution stands between.
    /// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
    fn stated(
        &mut self,
        (inputs, output): (
            &[(&'arena StringLiteral, PortSort<'arena>)],
            PortSort<'arena>,
        ),
        (named, implicits): (
            &BTreeMap<&'arena StringLiteral, Named>,
            &[&'arena StringLiteral],
        ),
        (signature, ranked): (&Signature<'arena>, &BTreeMap<&'arena StringLiteral, Rank>),
        fuel: &mut RewriteFuel,
    ) -> Option<Vec<Box<[Stated]>>>
    {
        // An index term as written, and its node as read when it reads.
        type ReadIndex = (Vec<Stated>, Option<Node>);
        let width = implicits.len().checked_add(inputs.len())?;
        let mut graph = Graph::default();
        let names: Vec<Node> = (0 .. width)
            .map(|place| {
                graph.nodes.push(GraphNode::Symbol {
                    symbol: TheorySymbol(NAMED_BASE.saturating_add(place)),
                    first: Position(graph.children.len()),
                    arity: 0,
                });
                Node(graph.nodes.len().saturating_sub(1))
            })
            .collect();
        let slot = |named: Named| match named {
            Named::Implicit(place) => place,
            Named::Input(Position(place)) => Position(implicits.len().saturating_add(place)),
        };
        let mut sorts: Vec<Option<Node>> = alloc::vec![None; width];
        let (mut pending, mut stack, mut built, mut pairs, mut children) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
        // Each port's sort symbol and index terms, each as written and as read.
        let mut read: Vec<(TheorySymbol, Vec<ReadIndex>)> = Vec::new();
        for (place, port) in inputs
            .iter()
            .map(|&(_, port)| port)
            .chain([output])
            .enumerate()
        {
            let rank = *ranked.get(port.sort)?;
            let symbol = TheorySymbol(SORT_BASE.saturating_add(rank.0));
            pending.clear();
            let _count = self.carried_terms(port, signature, &mut pending)?;
            let mut carried = Vec::with_capacity(pending.len());
            for &term in pending.iter().rev() {
                let written = self.written_index(term, named)?;
                let read = if matches!(*written.as_slice(), [Stated::Named(_)]) {
                    None
                }
                else {
                    self.elaborated(
                        &written,
                        (&mut graph, &names, &mut sorts),
                        &slot,
                        signature,
                        (&mut stack, &mut built, &mut pairs),
                        fuel,
                    )
                };
                carried.push((written, read));
            }
            if place < inputs.len() {
                // `grown` may push children of its own, so this node's
                // children gather apart and land as one range.
                children.clear();
                for &(ref written, read) in &carried {
                    let node = match read {
                        Some(node) => node,
                        None => grown(
                            &mut graph,
                            written,
                            |named| names.get(slot(named).0).copied(),
                            &mut built,
                        )?,
                    };
                    children.push(node);
                }
                let first = Position(graph.children.len());
                graph.children.extend(children.iter().copied());
                graph.nodes.push(GraphNode::Symbol {
                    symbol,
                    first,
                    arity: children.len(),
                });
                let node = Node(graph.nodes.len().saturating_sub(1));
                *sorts.get_mut(implicits.len().checked_add(place)?)? = Some(node);
            }
            read.push((symbol, carried));
        }
        let (mut flat, mut flattening) = (Vec::new(), Vec::new());
        let mut stated = Vec::with_capacity(read.len());
        for (symbol, carried) in read {
            let mut template = alloc::vec![Stated::Symbol(symbol, FieldCount::from(carried.len()))];
            for (written, read) in carried {
                let solved = match read {
                    Some(node) => {
                        graph.expand(node, &mut flat, &mut flattening, fuel).ok()?;
                        flat.iter()
                            .map(|&node| match node {
                                Flat::Symbol(TheorySymbol(symbol), 0) if symbol >= NAMED_BASE => {
                                    let place = symbol.checked_sub(NAMED_BASE)?;
                                    Some(Stated::Named(
                                        place
                                            .checked_sub(implicits.len())
                                            .map_or(Named::Implicit(Position(place)), |input| {
                                                Named::Input(Position(input))
                                            }),
                                    ))
                                },
                                Flat::Symbol(symbol, arity) => {
                                    Some(Stated::Symbol(symbol, FieldCount::from(arity)))
                                },
                                Flat::Variable(_) => None,
                            })
                            .collect::<Option<Vec<Stated>>>()
                    },
                    None => None,
                };
                template.extend(solved.unwrap_or(written));
            }
            stated.push(template.into());
        }
        Some(stated)
    }

    /// The template of the index term `term` as written: each `Var` the name
    /// `named` holds for it, each `App` and `Con` the symbol its name and
    /// argument count intern to, in pre-order.
    ///
    /// # Specification
    /// - ensures: [`Some`] with one template node per node of `term`; [`None`]
    ///   at a `Var` `named` does not hold, or any node but a `Var`, an `App` or
    ///   a `Con`.
    /// - panics: none.
    /// - executable: none — the template is the term's own reading.
    /// - intension: the term read in pre-order from a worklist.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stated`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn written_index(
        &mut self,
        term: ValueId,
        named: &BTreeMap<&'arena StringLiteral, Named>,
    ) -> Option<Vec<Stated>>
    {
        let mut pending = alloc::vec![term];
        let mut written = Vec::new();
        while let Some(term) = pending.pop() {
            let node = match self
                .constructor(term)
                .map(|(tag, fields)| (usize::from(tag), fields))?
            {
                (tag::VAR, &[name]) => Stated::Named(*named.get(self.text(name)?)?),
                (kind @ (tag::APP | tag::CON), &[name, chain]) => {
                    let class = if kind == tag::APP {
                        Class::Operation
                    }
                    else {
                        Class::Constructor
                    };
                    let count = self.index_terms(chain, &mut pending)?;
                    let name = self.text(name)?;
                    Stated::Symbol(self.intern((class, Some(name), count)), count)
                },
                _ => return None,
            };
            written.push(node);
        }
        Some(written)
    }

    /// The node the index term `written` reads as in `graph`, each application
    /// carrying its implicit indices, when its reading covers it.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the node when every node of `written` is a name
    ///   or an application of an operation `signature` holds at its port count,
    ///   each application's arguments' sorts unifying with its ports' templates
    ///   over fresh implicit indices; [`None`] otherwise, or when `fuel` runs
    ///   out, `graph` then holding what the reading built.
    /// - panics: none.
    /// - executable: none — the graph built is the reading's own state.
    /// - intension: the template built from its last node to its first, each
    ///   application taking its arguments off a stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stated`].
    /// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
    fn elaborated<S>(
        &mut self,
        written: &[Stated],
        (graph, names, sorts): (&mut Graph, &[Node], &mut [Option<Node>]),
        slot: &S,
        signature: &Signature<'arena>,
        (stack, built, pairs): (&mut Vec<Sorted>, &mut Vec<Node>, &mut Vec<(Node, Node)>),
        fuel: &mut RewriteFuel,
    ) -> Option<Node>
    where
        S: Fn(Named) -> Position,
    {
        stack.clear();
        for &node in written.iter().rev() {
            let sorted = match node {
                Stated::Named(named) => {
                    let Position(place) = slot(named);
                    let term = *names.get(place)?;
                    let held = sorts.get_mut(place)?;
                    let sort = if let Some(sort) = *held {
                        sort
                    }
                    else {
                        graph.nodes.push(GraphNode::Variable(None));
                        let sort = Node(graph.nodes.len().saturating_sub(1));
                        *held = Some(sort);
                        sort
                    };
                    Sorted { term, sort }
                },
                Stated::Symbol(symbol, count) => {
                    let Some(&(Class::Operation, Some(name), _)) = self.keys.get(symbol.0)
                    else {
                        return None;
                    };
                    let sorting = signature.operations.get(name)?;
                    if usize::from(count) != sorting.inputs.len() {
                        return None;
                    }
                    let count = usize::from(count);
                    let base = stack.len().checked_sub(count)?;
                    // The arguments stand on the stack's top, the first argument
                    // last pushed; the fresh implicit indices are consecutive
                    // nodes.
                    let at = |place: usize| -> Option<&Sorted> {
                        stack.get(
                            base.checked_add(count)?
                                .checked_sub(place.checked_add(1)?)?,
                        )
                    };
                    let fresh = graph.nodes.len();
                    let implicit_count = sorting.implicits.len();
                    graph
                        .nodes
                        .extend(sorting.implicits.iter().map(|_| GraphNode::Variable(None)));
                    let resolve = |named: Named| match named {
                        Named::Implicit(Position(place)) => {
                            (place < implicit_count).then(|| Node(fresh.saturating_add(place)))
                        },
                        Named::Input(Position(place)) => at(place).map(|argument| argument.term),
                    };
                    for place in 0 .. count {
                        let argument_sort = at(place)?.sort;
                        let stated = grown(graph, sorting.stated.get(place)?, resolve, built)?;
                        if graph.unify(argument_sort, stated, pairs, fuel).ok()? == Verdict::Fails {
                            return None;
                        }
                    }
                    let sort = grown(
                        graph,
                        sorting.stated.get(sorting.inputs.len())?,
                        resolve,
                        built,
                    )?;
                    let carried = FieldCount::from(count.checked_add(implicit_count)?);
                    let symbol = self.intern((Class::Operation, Some(name), carried));
                    let first = Position(graph.children.len());
                    graph.children.extend(
                        (0 .. implicit_count).map(|place| Node(fresh.saturating_add(place))),
                    );
                    for place in 0 .. count {
                        graph.children.push(at(place)?.term);
                    }
                    stack.truncate(base);
                    graph.nodes.push(GraphNode::Symbol {
                        symbol,
                        first,
                        arity: usize::from(carried),
                    });
                    Sorted {
                        term: Node(graph.nodes.len().saturating_sub(1)),
                        sort,
                    }
                },
            };
            stack.push(sorted);
        }
        let root = stack.pop()?;
        stack.is_empty().then_some(root.term)
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
        let Some(dropped) = signature
            .dropped
            .get(port.sort)
            .filter(|_| signature.carry == Carry::Rigid)
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
    ///   occurrence on the left side, then the right. The rules are read in
    ///   order of rank, and two sides whose sorts do not unify as they stand
    ///   unify after each sort is normalized by the indexed rules of lower
    ///   rank. [`None`] when the reading covers some rule not, or solving it
    ///   runs past [`PRESENTATION_FUEL`].
    /// - panics: none.
    /// - executable: none — the rules returned are the solution itself.
    /// - intension: one graph per rule, its sides read from the leaves up, so
    ///   no step recurses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a category's unit laws carry the objects their
    ///   variables fix, and their overlap is one well-sorted term; a `CwF`'s
    ///   laws on terms sort modulo its laws on types.
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    /// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
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
        let rules = core::mem::take(&mut self.rules);
        let indexed = self.in_rank_order(&rules, signature, &mut fuel);
        self.rules = rules;
        indexed
    }

    /// Each rule of `rules` in the indexed reading, as [`Self::indexed`] reads
    /// them: in order of rank, each read modulo the rules of lower rank.
    ///
    /// # Specification
    /// - ensures: as [`Self::indexed`], over `rules`; a rule whose left side
    ///   ranks no operation is read modulo no rule, and no rule is read modulo
    ///   it.
    /// - panics: none.
    /// - executable: none — as [`Self::indexed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::indexed`].
    /// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
    fn in_rank_order(
        &mut self,
        rules: &[TheoryRule],
        signature: &Signature<'arena>,
        fuel: &mut RewriteFuel,
    ) -> Option<Vec<TheoryRule>>
    {
        let mut order: Vec<(Option<Rank>, usize)> = rules
            .iter()
            .enumerate()
            .map(|(place, rule)| (self.rank(signature, rule), place))
            .collect();
        order.sort_unstable();
        let mut indexer = Indexer::default();
        let mut indexed: Vec<Option<TheoryRule>> = alloc::vec![None; rules.len()];
        let (mut below, mut ranked): (Vec<TheoryRule>, Vec<TheoryRule>) = (Vec::new(), Vec::new());
        let mut current = None;
        for (rank, place) in order {
            if rank != current {
                below.append(&mut ranked);
                current = rank;
            }
            let lower: &[TheoryRule] = if rank.is_some() { &below } else { &[] };
            let read = indexer.rule(self, signature, (rules.get(place)?, lower), fuel)?;
            if rank.is_some() {
                ranked.push(read.clone());
            }
            *indexed.get_mut(place)? = Some(read);
        }
        indexed.into_iter().collect()
    }

    /// The rank of `rule`'s sort: the rank of the sort its left side's
    /// operation outputs.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        signature: &Signature<'arena>,
        rule: &TheoryRule,
    ) -> Option<Rank>
    {
        let &TheoryNode::Symbol(symbol) = rule.left().first()?
        else {
            return None;
        };
        let &(Class::Operation, Some(name), _) = self.keys.get(symbol.0)?
        else {
            return None;
        };
        signature.ranks.get(name).copied()
    }
}

impl Indexer
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
        reader: &mut Reader<'_>,
        signature: &Signature<'_>,
        (rule, below): (&TheoryRule, &[TheoryRule]),
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
            self.sorted_alike(reader, below, (from.sort, to.sort), fuel)?;
            Some((from, to))
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
        reader: &mut Reader<'_>,
        signature: &Signature<'_>,
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
                    // The node carries its implicit indices first, as the
                    // indexed rules write it, so a sort that holds it meets
                    // the normal form the rules of lower rank give.
                    let carried =
                        FieldCount::from(usize::from(arity).checked_add(sorting.implicits.len())?);
                    let first = Position(self.graph.children.len());
                    self.graph.children.extend(
                        self.implicits
                            .get(span.from.0 .. span.to.0)?
                            .iter()
                            .copied(),
                    );
                    self.graph
                        .children
                        .extend(self.arguments.iter().map(|argument| argument.term));
                    self.graph.nodes.push(GraphNode::Symbol {
                        symbol: reader.intern((class, Some(name), carried)),
                        first,
                        arity: usize::from(carried),
                    });
                    let term = Node(self.graph.nodes.len().saturating_sub(1));
                    for (place, _) in sorting.inputs.iter().enumerate() {
                        let stated = self.instantiated(sorting, Position(place), span)?;
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
                    let sort = self.instantiated(sorting, Position(sorting.inputs.len()), span)?;
                    *at.get_mut(position)? = Some(span);
                    Sorted { term, sort }
                },
            };
            self.stack.push(sorted);
        }
        let root = self.stack.pop()?;
        self.stack.is_empty().then_some(root)
    }

    /// Unify `left` and `right`, the sorts of a rule's two sides; where they do
    /// not unify as they stand, unify their normal forms under `below`, the
    /// indexed rules of lower rank.
    ///
    /// # Specification
    /// - ensures: [`Some`] when the two sorts unify, or when `below` holds a
    ///   rule and the sorts' normal forms ([`normal_form`]) under it unify,
    ///   read after the graph as it stood before the first attempt.
    /// - fails: none.
    /// - panics: none.
    /// - executable: none — the solution is the graph's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `CwF`'s identity law on terms sorts only after its
    ///   left side's type is normalized by the identity law on types.
    /// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
    fn sorted_alike(
        &mut self,
        reader: &Reader<'_>,
        below: &[TheoryRule],
        (left, right): (Node, Node),
        fuel: &mut RewriteFuel,
    ) -> Option<()>
    {
        let before =
            (!below.is_empty()).then(|| (self.graph.nodes.clone(), self.graph.children.clone()));
        if self.unified(left, right, fuel)? == Verdict::Holds {
            return Some(());
        }
        let (nodes, children) = before?;
        self.graph.nodes = nodes;
        self.graph.children = children;
        let width = |symbol: TheorySymbol| {
            Position(
                reader
                    .keys
                    .get(symbol.0)
                    .map_or(0, |&(_, _, arity)| usize::from(arity)),
            )
        };
        let mut normal = [left, right];
        for sort in &mut normal {
            if self.graph.acyclic(*sort, &mut self.marks, &mut self.walk) == Verdict::Fails {
                return None;
            }
            self.graph
                .expand(*sort, &mut self.flat, &mut self.flattening, fuel)
                .ok()?;
            normal_form(
                below,
                &mut self.flat,
                (&mut self.bindings, &mut self.rewritten),
                width,
                fuel,
            )
            .ok()?;
            *sort = loaded(&mut self.graph, &self.flat, &mut self.built)?;
        }
        let [left, right] = normal;
        (self.unified(left, right, fuel)? == Verdict::Holds).then_some(())
    }

    /// Whether `left` and `right` unify to a finite term: the graph's unifier,
    /// then the occurs check on both, as the front end's sorting refuses an
    /// unknown solved by a term that names it.
    ///
    /// # Specification
    /// - ensures: [`Some`] with [`Verdict::Holds`] when the two unify and
    ///   neither reaches itself after; [`Verdict::Fails`] otherwise.
    /// - fails: [`None`] when `fuel` runs out.
    /// - panics: none.
    /// - executable: none — the solution is the graph's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::sorted_alike`]: a term's type solved as
    ///   that type moved along an identity is cyclic, so the sorts are read
    ///   modulo the identity law on types.
    /// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
    fn unified(
        &mut self,
        left: Node,
        right: Node,
        fuel: &mut RewriteFuel,
    ) -> Option<Verdict>
    {
        if self.graph.unify(left, right, &mut self.pairs, fuel).ok()? == Verdict::Fails {
            return Some(Verdict::Fails);
        }
        Some(Verdict::from([left, right].into_iter().all(|root| {
            self.graph.acyclic(root, &mut self.marks, &mut self.walk) == Verdict::Holds
        })))
    }

    /// The sort `sorting`'s port at `place` states, the inputs in order and
    /// then the output, built in the graph for the application whose implicit
    /// indices `span` holds and whose arguments are `self.arguments`.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the node of the port's template ([`Stated`]),
    ///   each implicit index its node in `span`, each input port its argument;
    ///   [`None`] at a place past the output, or a name `span` or the arguments
    ///   do not hold.
    /// - panics: none.
    /// - executable: none — the nodes built are the graph's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader::indexed`].
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    fn instantiated(
        &mut self,
        sorting: &Sorting<'_>,
        Position(place): Position,
        span: Span,
    ) -> Option<Node>
    {
        let (implicits, arguments) = (&self.implicits, &self.arguments);
        let resolve = |named: Named| match named {
            Named::Implicit(Position(place)) => {
                implicits.get(span.from.0.checked_add(place)?).copied()
            },
            Named::Input(Position(place)) => arguments.get(place).map(|argument| argument.term),
        };
        grown(
            &mut self.graph,
            sorting.stated.get(place)?,
            resolve,
            &mut self.built,
        )
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
        reader: &mut Reader<'_>,
        signature: &Signature<'_>,
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
                            let &(class, name, arity) = reader.keys.get(symbol.0)?;
                            let own = match (class, name) {
                                (Class::Operation, Some(name)) => signature.uncarried(name, arity),
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

/// The node `template` builds in `graph`, each name the node `resolve` gives
/// it: a [`Stated::Symbol`] over the nodes its subterms build.
///
/// # Specification
/// - ensures: [`Some`] with the root's node when `template` is one term and
///   `resolve` gives a node for each of its names; [`None`] otherwise.
/// - panics: none.
/// - executable: none — the nodes built are the graph's own state.
/// - intension: the template built from its last node to its first, each symbol
///   taking its subterms off `built`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Reader::indexed`].
/// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
fn grown<R>(
    graph: &mut Graph,
    template: &[Stated],
    resolve: R,
    built: &mut Vec<Node>,
) -> Option<Node>
where
    R: Fn(Named) -> Option<Node>,
{
    built.clear();
    for &item in template.iter().rev() {
        let node = match item {
            Stated::Named(named) => resolve(named)?,
            Stated::Symbol(symbol, count) => {
                let first = Position(graph.children.len());
                for _ in 0 .. usize::from(count) {
                    let child = built.pop()?;
                    graph.children.push(child);
                }
                graph.nodes.push(GraphNode::Symbol {
                    symbol,
                    first,
                    arity: usize::from(count),
                });
                Node(graph.nodes.len().saturating_sub(1))
            },
        };
        built.push(node);
    }
    let root = built.pop()?;
    built.is_empty().then_some(root)
}

/// The node the flattened term `flat` builds in `graph`, each variable its own
/// node.
///
/// # Specification
/// - ensures: [`Some`] with the root's node when `flat` is one term; [`None`]
///   otherwise.
/// - panics: none.
/// - executable: none — the nodes built are the graph's own state.
/// - intension: the term built from its last node to its first, as [`grown`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Indexer::sorted_alike`].
/// - witness: `theory_rules::tests::a_cwfs_laws_on_terms_join_modulo_its_laws_on_types_5042`
fn loaded(
    graph: &mut Graph,
    flat: &[Flat],
    built: &mut Vec<Node>,
) -> Option<Node>
{
    built.clear();
    for &item in flat.iter().rev() {
        let node = match item {
            Flat::Variable(node) => node,
            Flat::Symbol(symbol, arity) => {
                let first = Position(graph.children.len());
                for _ in 0 .. arity {
                    let child = built.pop()?;
                    graph.children.push(child);
                }
                graph.nodes.push(GraphNode::Symbol {
                    symbol,
                    first,
                    arity,
                });
                Node(graph.nodes.len().saturating_sub(1))
            },
        };
        built.push(node);
    }
    let root = built.pop()?;
    built.is_empty().then_some(root)
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
