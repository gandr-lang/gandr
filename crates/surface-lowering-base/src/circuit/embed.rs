//! Circuit bodies as wiring diagrams, their spider canon and bounded
//! embeddings.
//!
//! The surface adapter sits above the diagram matcher and the cell engine;
//! neither theory implementation depends on the other.
//!
//! A [`CircuitReading`] holds a body with the rule's declared input ports and
//! its marked wires. A marked wire has a sort with a special commutative
//! Frobenius algebra. The boundary of the wiring is the declared ports: the
//! inputs in telescope order, then the outputs in port order. Thus the order
//! of the nodes never changes the interface.
//!
//! A merge or a split on a marked wire is a spider. The body writes no node
//! for it: the wire map repeats the name of the wire. The reading gives the
//! spider one [`GeneratorSort::Spider`] generator, which the sort of the wire
//! names. The spider takes one fresh wire for each producer and one for each
//! consumer. [`circuit_canon`] decides the wiring modulo the Frobenius laws,
//! with the spider canon of `gandr-theory-circuit-algebras`.
//!
//! # References
//!
//! - `vault:01a178aa-61bf-70f2-a24f-b3a69dfcd199` — newest: a merge on a marked
//!   wire is a boxless spider, which canonicalization at the representation
//!   decides, never contraction rules.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::MatchBudget;
use gandr_theory_circuit_algebras::MatchObstruction;
use gandr_theory_circuit_algebras::Matching;
use gandr_theory_circuit_algebras::SpiderBudget;
use gandr_theory_circuit_algebras::SpiderCanon;
use gandr_theory_circuit_algebras::SpiderObstruction;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::WiringObstruction;
use gandr_theory_circuit_algebras::embeddings;
use gandr_theory_circuit_algebras::spider_canonicalize;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermView;

/// A circuit body, with what its wiring reads besides the nodes: the declared
/// input ports of the rule, and the marked wires.
#[derive(Clone, Copy, Debug)]
pub struct CircuitReading<'body>
{
    /// The body.
    body: &'body CircuitBody,
    /// The declared input ports, in telescope order.
    inputs: &'body [Name],
    /// Each marked wire, with the name of its sort. The sort has a special
    /// commutative Frobenius algebra.
    spiders: &'body BTreeMap<Name, Name>,
}

impl<'body> CircuitReading<'body>
{
    /// The reading of `body` with the declared input ports `inputs`, in
    /// telescope order, and the marked wires that `spiders` keys.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        body: &'body CircuitBody,
        inputs: &'body [Name],
        spiders: &'body BTreeMap<Name, Name>,
    ) -> Self
    {
        Self {
            body,
            inputs,
            spiders,
        }
    }

    /// The reading itself when a marked wire of it merges or splits, so that
    /// the reading gives the wire a spider.
    ///
    /// # Specification
    /// - ensures: the reading exactly when a marked wire has two producers or
    ///   two consumers, among the declared ports and the nodes; none otherwise.
    /// - panics: none.
    /// - executable: none — the count is the claim, and a predicate would walk
    ///   the declared ports and the nodes again.
    /// - intension: one pass over the declared ports and the nodes, as
    ///   [`circuit_wiring`] counts them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marked merge gives a spider; the same merge
    ///   unmarked, and a marked wire that neither merges nor splits, give none.
    /// - witness: `circuit::embed::tests::a_reading_is_spidered_where_a_marked_wire_merges_5763`
    #[inline]
    #[must_use]
    pub fn spidered(self) -> Option<Self>
    {
        (!spider_legs(self).is_empty()).then_some(self)
    }
}

/// Why a body has no literal wiring-diagram reading.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitWiringError
{
    /// A term application supplies no wire; its applied head is retained.
    ArgumentIsNotAPort(Name),
    /// A results tuple supplies no wire: it stands only at a rule's root.
    ResultsAreNotAPort,
    /// The diagram constructor refused the actual incidence structure.
    NotAWiring(WiringObstruction),
}

impl core::fmt::Display for CircuitWiringError
{
    /// State the boundary without replacing the underlying obstruction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::ArgumentIsNotAPort(ref head) => {
                write!(f, "the argument headed by `{head}` is a term, not a wire")
            },
            Self::ResultsAreNotAPort => {
                f.write_str("a results tuple is not a wire; it stands only at a rule's root")
            },
            Self::NotAWiring(ref obstruction) => {
                write!(f, "the circuit body is not a wiring: {obstruction}")
            },
        }
    }
}

impl core::error::Error for CircuitWiringError
{
}

/// Why an embedding query was refused rather than answered with no match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitEmbedError
{
    /// One body has no literal diagram reading.
    Wiring(CircuitWiringError),
    /// The matcher refused its bounded enumeration.
    Matching(MatchObstruction),
}

impl core::fmt::Display for CircuitEmbedError
{
    /// Retain the distinction between bad wiring and exhausted matching.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Wiring(ref error) => error.fmt(f),
            Self::Matching(ref obstruction) => {
                write!(f, "the circuit embedding search declined: {obstruction}")
            },
        }
    }
}

impl core::error::Error for CircuitEmbedError
{
}

/// Why a body has no spider canon.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitCanonError
{
    /// The body has no wiring reading.
    Wiring(CircuitWiringError),
    /// The spider canon refused the wiring, by name.
    Canon(SpiderObstruction),
}

impl core::fmt::Display for CircuitCanonError
{
    /// Keep the bad wiring apart from the refused canon.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Wiring(ref error) => error.fmt(f),
            Self::Canon(ref obstruction) => {
                write!(
                    f,
                    "the spider canon of the circuit body declined: {obstruction}"
                )
            },
        }
    }
}

impl core::error::Error for CircuitCanonError
{
}

/// Read each node as a generator, each variable argument as a wire, and each
/// marked wire that merges or splits as one spider.
///
/// # Specification
/// - requires: no additional precondition.
/// - ensures: each admitted node becomes one generator, in node order. It keeps
///   its arguments in order, its outputs in port order, its head name and its
///   head role. Each marked wire with two producers or two consumers becomes
///   one spider after the nodes. A declared input is a producer, and a declared
///   output is a consumer. The spider takes one fresh wire for each producer
///   and one for each consumer. The boundary is the declared inputs in
///   telescope order, then the declared outputs in port order.
/// - fails: a non-variable argument, or the obstruction of the diagram
///   constructor. An unmarked wire that merges or splits is refused there, as
///   [`WiringObstruction::FanIn`] or [`WiringObstruction::FanOut`] at that
///   wire.
/// - panics: none.
/// - intension: two passes over the nodes. The first counts the uses of each
///   marked wire, and the second builds the generators.
///
/// # Adequacy
/// - hypothesis: L3 — ordered chains, ground arguments, a merge and a split on
///   a marked wire, and the same merge and split unmarked, tell the literal
///   reading apart from invented vertices, reordered ports and an interface
///   that follows the node order.
/// - witness: `circuit::embed::tests::a_two_line_body_reads_as_a_diagram_with_one_internal_wire`
/// - witness: `circuit::embed::tests::a_ground_argument_names_no_wire`
/// - witness: `circuit::embed::tests::a_body_binding_one_port_twice_is_not_a_wiring`
/// - witness: `circuit::embed::tests::a_marked_merge_and_split_read_as_spiders_5800`
/// - witness: `circuit::embed::tests::every_order_of_the_nodes_gives_one_canon_5800`
///
/// # Errors
/// As the failure clause states.
#[inline]
#[spec(ensures: |output| output.as_ref().map_or(true, |wiring| wiring.generators().len() >= reading.body.nodes.len()
    && wiring.boundary().inputs().len() == reading.inputs.len()
    && wiring.boundary().outputs().len() == reading.body.outs.len()))]
pub fn circuit_wiring(reading: CircuitReading<'_>) -> Result<Wiring, CircuitWiringError>
{
    let body = reading.body;
    let mut wires = Wires::new(spider_legs(reading));
    let inputs: Vec<Wire> = reading
        .inputs
        .iter()
        .map(|port| wires.produced(port))
        .collect();
    let mut generators = Vec::with_capacity(body.nodes.len().saturating_add(wires.legs.len()));
    for node in &body.nodes {
        let arguments = node_arguments(node);
        let mut sources = Vec::with_capacity(arguments.len());
        for argument in arguments {
            sources.push(wires.consumed(port_of(argument)?));
        }
        let targets: Vec<Wire> = node.outs().iter().map(|out| wires.produced(out)).collect();
        generators.push(Generator::new(
            GeneratorLabel::new(node_head(node).as_ref(), node_sort(node)),
            sources,
            targets,
        ));
    }
    let outputs: Vec<Wire> = body.outs.iter().map(|port| wires.consumed(port)).collect();
    let count = wires.minted;
    for legs in wires.legs.into_values() {
        generators.push(Generator::new(
            GeneratorLabel::new(legs.sort.as_ref(), GeneratorSort::Spider),
            legs.sources,
            legs.targets,
        ));
    }
    Wiring::assemble(count, generators, Interface::new(inputs, outputs))
        .map_err(CircuitWiringError::NotAWiring)
}

/// The canon of a body's wiring modulo the Frobenius laws of its spiders.
///
/// # Specification
/// - requires: no additional precondition.
/// - ensures: the spider canon of the wiring that [`circuit_wiring`] reads. Two
///   readings reach one form exactly when the laws and a renumbering carry one
///   wiring onto the other. The canon ran at most `budget` trials.
/// - fails: [`CircuitCanonError::Wiring`] as [`circuit_wiring`] fails;
///   [`CircuitCanonError::Canon`] with [`SpiderObstruction::BudgetExhausted`]
///   before any trial, when the tied legs need more trials than `budget`.
/// - panics: none.
/// - intension: one reading, then the spider canon: one fusion and one
///   traversal for each trial.
///
/// # Adequacy
/// - hypothesis: L3 — a merge of three producers reaches the form of two merges
///   in either association; every order of the nodes reaches one form; a tie
///   one trial past the budget is refused, and a budget equal to the trials is
///   admitted.
/// - witness: `circuit::embed::tests::two_merges_in_either_association_are_one_canon_5800`
/// - witness: `circuit::embed::tests::every_order_of_the_nodes_gives_one_canon_5800`
/// - witness: `circuit::embed::tests::a_body_past_the_budget_is_refused_by_name_5800`
///
/// # Errors
/// As the failure clause states.
#[inline]
#[spec(ensures: |ref result| match *result {
    Ok(ref canon) => usize::from(canon.trials()) <= usize::from(budget),
    Err(CircuitCanonError::Canon(SpiderObstruction::BudgetExhausted { budget: allowed, .. })) => allowed == budget,
    Err(_) => true,
})]
pub fn circuit_canon(
    reading: CircuitReading<'_>,
    budget: SpiderBudget,
) -> Result<SpiderCanon, CircuitCanonError>
{
    let wiring = circuit_wiring(reading).map_err(CircuitCanonError::Wiring)?;
    spider_canonicalize(&wiring, budget).map_err(CircuitCanonError::Canon)
}

/// Enumerate the admitted diagram embeddings without disguising exhaustion.
///
/// # Specification
/// - requires: no additional precondition.
/// - ensures: the diagram matcher decides the readings of both bodies.
/// - fails: bad wiring or an exhausted matching allowance.
/// - panics: none.
/// - executable: none — the matcher's decision is the claim, and no predicate
///   restates it without running the matcher again.
///
/// # Adequacy
/// - hypothesis: L3 — a contained head, a different head and a zero allowance
///   separate admission, a genuine absence, and an undecided enumeration.
/// - witness: `circuit::embed::tests::a_rule_body_embeds_in_a_body_that_contains_it`
/// - witness: `circuit::embed::tests::a_body_that_does_not_contain_the_pattern_admits_no_embedding`
/// - witness: `circuit::embed::tests::an_exhausted_budget_declines_rather_than_reporting_no_match`
///
/// # Errors
/// As the failure clause states.
#[inline]
pub fn embed_circuit_rule(
    pattern: CircuitReading<'_>,
    target: CircuitReading<'_>,
    budget: MatchBudget,
) -> Result<Matching, CircuitEmbedError>
{
    let pattern = circuit_wiring(pattern).map_err(CircuitEmbedError::Wiring)?;
    let target = circuit_wiring(target).map_err(CircuitEmbedError::Wiring)?;
    embeddings(&pattern, &target, budget).map_err(CircuitEmbedError::Matching)
}

/// How often a wire is produced, or consumed, in one reading.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Multiplicity
{
    /// Not at all.
    #[default]
    Zero,
    /// Once.
    Once,
    /// Twice or more.
    Many,
}

impl Multiplicity
{
    /// The multiplicity with one use more.
    ///
    /// # Specification
    /// trivial.
    const fn more(self) -> Self
    {
        match self {
            Self::Zero => Self::Once,
            Self::Once | Self::Many => Self::Many,
        }
    }
}

/// Which side of a wire one use stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// A node output or a declared input: the use produces the wire.
    Produced,
    /// A node argument or a declared output: the use consumes the wire.
    Consumed,
}

/// The uses of one marked wire.
#[derive(Clone, Copy, Debug, Default)]
struct Uses
{
    /// How often a node or a declared input produces it.
    produced: Multiplicity,
    /// How often a node argument or a declared output consumes it.
    consumed: Multiplicity,
}

/// One spider of a reading: its sort, and the fresh wire of each producer and
/// of each consumer, in reading order.
#[derive(Debug)]
struct Legs<'body>
{
    /// The sort of the marked wire, which names the spider.
    sort: &'body Name,
    /// The wires that the producers of the marked wire produce.
    sources: Vec<Wire>,
    /// The wires that the consumers of the marked wire consume.
    targets: Vec<Wire>,
}

/// The marked wires of `reading` that merge or split, each with no legs yet.
///
/// # Specification
/// - requires: no additional precondition.
/// - ensures: one entry for each marked wire with two producers or two
///   consumers, among the declared ports and the nodes.
/// - panics: none.
/// - intension: one pass over the declared ports and the nodes, and one map
///   lookup for each port use.
///
/// # Adequacy
/// - hypothesis: L3 — a merge, a split and a plain marked wire separate the
///   wires that the reading gives a spider from the wires it keeps plain.
/// - witness: `circuit::embed::tests::a_marked_merge_and_split_read_as_spiders_5800`
#[spec(ensures: |legs| legs.len() <= reading.spiders.len())]
fn spider_legs(reading: CircuitReading<'_>) -> BTreeMap<&Name, Legs<'_>>
{
    let mut uses: BTreeMap<&Name, (&Name, Uses)> = BTreeMap::new();
    let mut count = |port, side| {
        if let Some(sort) = reading.spiders.get(port) {
            let &mut (_, ref mut seen) =
                uses.entry(port).or_insert_with(|| (sort, Uses::default()));
            match side {
                Side::Produced => seen.produced = seen.produced.more(),
                Side::Consumed => seen.consumed = seen.consumed.more(),
            }
        }
    };
    for port in reading.inputs {
        count(port, Side::Produced);
    }
    for node in &reading.body.nodes {
        for argument in node_arguments(node) {
            if let TermView::Var(port) = argument.view() {
                count(port, Side::Consumed);
            }
        }
        for out in node.outs() {
            count(out, Side::Produced);
        }
    }
    for port in &reading.body.outs {
        count(port, Side::Consumed);
    }
    uses.into_iter()
        .filter(|&(_, (_, seen))| {
            seen.produced == Multiplicity::Many || seen.consumed == Multiplicity::Many
        })
        .map(|(port, (sort, _))| {
            (port, Legs {
                sort,
                sources: Vec::new(),
                targets: Vec::new(),
            })
        })
        .collect()
}

/// The wires of one reading, numbered in one sequence: each plain wire by its
/// name on its first appearance, and each leg of a spider fresh.
#[derive(Debug)]
struct Wires<'body>
{
    /// The wire of each plain name.
    named: BTreeMap<&'body Name, Wire>,
    /// The legs of each spider, by its marked wire.
    legs: BTreeMap<&'body Name, Legs<'body>>,
    /// How many wires the reading has minted.
    minted: WireCount,
}

impl<'body> Wires<'body>
{
    /// The wires of a reading whose spiders are `legs`, with no wire yet.
    ///
    /// # Specification
    /// trivial.
    fn new(legs: BTreeMap<&'body Name, Legs<'body>>) -> Self
    {
        Self {
            named: BTreeMap::new(),
            legs,
            minted: WireCount::default(),
        }
    }

    /// The wire that a producer of `port` produces: a fresh source of the
    /// spider of `port`, or the plain wire of the name.
    ///
    /// # Specification
    /// - ensures: the wire is one the reading minted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a merge gives its spider one source for each
    ///   producer, and a plain wire keeps one identity.
    /// - witness: `circuit::embed::tests::a_marked_merge_and_split_read_as_spiders_5800`
    #[spec(ensures: |output| usize::from(output) < usize::from(self.minted))]
    fn produced(
        &mut self,
        port: &'body Name,
    ) -> Wire
    {
        if self.legs.contains_key(port) {
            let wire = self.fresh();
            if let Some(legs) = self.legs.get_mut(port) {
                legs.sources.push(wire);
            }
            return wire;
        }
        self.named(port)
    }

    /// The wire that a consumer of `port` consumes: a fresh target of the
    /// spider of `port`, or the plain wire of the name.
    ///
    /// # Specification
    /// - ensures: the wire is one the reading minted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a split gives its spider one target for each
    ///   consumer, and a plain wire keeps one identity.
    /// - witness: `circuit::embed::tests::a_marked_merge_and_split_read_as_spiders_5800`
    #[spec(ensures: |output| usize::from(output) < usize::from(self.minted))]
    fn consumed(
        &mut self,
        port: &'body Name,
    ) -> Wire
    {
        if self.legs.contains_key(port) {
            let wire = self.fresh();
            if let Some(legs) = self.legs.get_mut(port) {
                legs.targets.push(wire);
            }
            return wire;
        }
        self.named(port)
    }

    /// The plain wire that `port` names, minted on its first appearance.
    ///
    /// # Specification
    /// - ensures: a repeated name keeps its wire; a new name takes a fresh
    ///   wire.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two-step wiring observes the shared internal wire
    ///   and both distinct boundary wires.
    /// - witness: `circuit::embed::tests::a_two_line_body_reads_as_a_diagram_with_one_internal_wire`
    #[spec(captures: before = self.named.get(port).copied(), ensures: |output| self.named.get(port) == Some(&output) && before.is_none_or(|old| old == output))]
    fn named(
        &mut self,
        port: &'body Name,
    ) -> Wire
    {
        if let Some(&wire) = self.named.get(port) {
            return wire;
        }
        let wire = self.fresh();
        let _fresh = self.named.insert(port, wire);
        wire
    }

    /// A wire that no name has.
    ///
    /// # Specification
    /// - ensures: the wire is the one past every wire minted before.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the legs of one spider are distinct wires.
    /// - witness: `circuit::embed::tests::a_marked_merge_and_split_read_as_spiders_5800`
    #[spec(captures: before = self.minted, ensures: |output| usize::from(output) == usize::from(before) && usize::from(self.minted) == usize::from(before).saturating_add(1))]
    fn fresh(&mut self) -> Wire
    {
        let wire = Wire::from(usize::from(self.minted));
        self.minted = WireCount::from(usize::from(self.minted).saturating_add(1));
        wire
    }
}

/// The wire that a node argument names.
///
/// # Specification
/// - ensures: the variable that the argument is.
/// - fails: a term application, whose head is retained, or a results tuple.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a ground argument names no wire.
/// - witness: `circuit::embed::tests::a_ground_argument_names_no_wire`
#[spec(ensures: |output| output.is_ok() == matches!(argument.view(), TermView::Var(_)))]
fn port_of(argument: &FreeTerm) -> Result<&Name, CircuitWiringError>
{
    match argument.view() {
        TermView::Var(name) => Ok(name),
        TermView::Ctor { name, .. }
        | TermView::Op { name, .. }
        | TermView::Inst { name, .. }
        | TermView::Abs { atom: name, .. }
        | TermView::Atom(name)
        | TermView::Lam { var: name, .. }
        | TermView::Bound(name) => Err(CircuitWiringError::ArgumentIsNotAPort(name.clone())),
        TermView::Results { .. } => Err(CircuitWiringError::ResultsAreNotAPort),
    }
}

/// The source arguments of a body node, without copying its terms.
///
/// # Specification
/// trivial.
fn node_arguments(node: &CircuitNode) -> &[FreeTerm]
{
    match *node {
        CircuitNode::Frame(ref frame) => &frame.args,
        CircuitNode::Redex(ref redex) => core::slice::from_ref(&redex.source),
    }
}

/// Keep constructors, operations and rewrites in different label roles.
///
/// # Specification
/// trivial.
const fn node_sort(node: &CircuitNode) -> GeneratorSort
{
    match *node {
        CircuitNode::Frame(ref frame) => match frame.head {
            FrameHead::Ctor(_) => GeneratorSort::Value,
            FrameHead::Op(_) => GeneratorSort::Operation,
        },
        CircuitNode::Redex(_) => GeneratorSort::Rewrite,
    }
}

/// The original head spelling of one node.
///
/// # Specification
/// trivial.
const fn node_head(node: &CircuitNode) -> &Name
{
    match *node {
        CircuitNode::Frame(ref frame) => frame.head.name(),
        CircuitNode::Redex(ref redex) => &redex.rewrite,
    }
}

#[cfg(test)]
mod tests;
