//! Circuit bodies as literal wiring diagrams and bounded embeddings.
//!
//! The surface adapter sits above the diagram matcher and the cell engine;
//! neither theory implementation depends on the other.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::MatchBudget;
use gandr_theory_circuit_algebras::MatchObstruction;
use gandr_theory_circuit_algebras::Matching;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::WiringObstruction;
use gandr_theory_circuit_algebras::embeddings;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermView;

/// Why a body has no literal wiring-diagram reading.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitWiringError
{
    /// A term application supplies no wire; its applied head is retained.
    ArgumentIsNotAPort(Name),
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
            | Self::ArgumentIsNotAPort(ref head) => {
                write!(f, "the argument headed by `{head}` is a term, not a wire")
            },
            | Self::NotAWiring(ref obstruction) => {
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
            | Self::Wiring(ref error) => error.fmt(f),
            | Self::Matching(ref obstruction) => {
                write!(f, "the circuit embedding search declined: {obstruction}")
            },
        }
    }
}

impl core::error::Error for CircuitEmbedError
{
}

/// Read each node as a generator and each variable argument as a wire.
///
/// # Specification
/// - requires: no additional precondition.
/// - ensures: every admitted node becomes one generator, preserving the
///   argument order, output, head name and head role.
/// - fails: a non-variable argument or the diagram constructor's obstruction.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — ordered chains, ground arguments and repeated producers
///   distinguish literal wiring from invented vertices or reordered ports.
/// - witness: `circuit::embed::tests::a_two_line_body_reads_as_a_diagram_with_one_internal_wire`
/// - witness: `circuit::embed::tests::a_ground_argument_names_no_wire`
/// - witness: `circuit::embed::tests::a_body_binding_one_port_twice_is_not_a_wiring`
///
/// # Errors
/// As the failure clause states.
#[inline]
#[spec(ensures: |output| output.as_ref().map_or(true, |wiring| wiring.generators().len() == body.nodes.len()))]
pub fn circuit_wiring(body: &CircuitBody) -> Result<Wiring, CircuitWiringError>
{
    let mut generators = Vec::with_capacity(body.nodes.len());
    let mut bound = BTreeSet::new();
    let mut read = BTreeSet::new();
    let mut index = BTreeMap::new();
    for node in &body.nodes {
        let arguments = node_arguments(node);
        let mut sources = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let port = match argument.view() {
                | TermView::Var(name) => name,
                | TermView::Ctor { name, .. } | TermView::Op { name, .. } => {
                    return Err(CircuitWiringError::ArgumentIsNotAPort(name.clone()));
                },
            };
            let wire = intern(port, &mut index);
            read.insert(wire);
            sources.push(wire);
        }
        let target = intern(node.out(), &mut index);
        bound.insert(target);
        generators.push(Generator::new(
            GeneratorLabel::new(node_head(node).as_ref(), node_sort(node)),
            sources,
            alloc::vec![target],
        ));
    }
    let count = WireCount::from(index.len());
    let inputs: Vec<Wire> = (0_usize .. index.len())
        .map(Wire::from)
        .filter(|wire| !bound.contains(wire))
        .collect();
    let outputs: Vec<Wire> = (0_usize .. index.len())
        .map(Wire::from)
        .filter(|wire| !read.contains(wire))
        .collect();
    Wiring::assemble(count, generators, Interface::new(inputs, outputs))
        .map_err(CircuitWiringError::NotAWiring)
}

/// Enumerate the admitted diagram embeddings without disguising exhaustion.
///
/// # Specification
/// - requires: no additional precondition.
/// - ensures: the diagram matcher decides the literal readings of both bodies.
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
    pattern: &CircuitBody,
    target: &CircuitBody,
    budget: MatchBudget,
) -> Result<Matching, CircuitEmbedError>
{
    let pattern = circuit_wiring(pattern).map_err(CircuitEmbedError::Wiring)?;
    let target = circuit_wiring(target).map_err(CircuitEmbedError::Wiring)?;
    embeddings(&pattern, &target, budget).map_err(CircuitEmbedError::Matching)
}

/// Number one borrowed wire name on its first appearance.
///
/// # Specification
/// - requires: entries were minted by this function.
/// - ensures: repeated names retain their identity; a fresh name follows every
///   identity already minted.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the two-step wiring observes the shared internal wire and
///   both distinct boundary wires.
/// - witness: `circuit::embed::tests::a_two_line_body_reads_as_a_diagram_with_one_internal_wire`
#[spec(captures: before = index.get(port).copied(), ensures: |output| index.get(port) == Some(&output) && before.is_none_or(|old| old == output))]
fn intern<'body>(
    port: &'body Name,
    index: &mut BTreeMap<&'body Name, Wire>,
) -> Wire
{
    let next = Wire::from(index.len());
    *index.entry(port).or_insert(next)
}

/// The source arguments of a body node, without copying its terms.
///
/// # Specification
/// trivial.
fn node_arguments(node: &CircuitNode) -> &[FreeTerm]
{
    match *node {
        | CircuitNode::Frame(ref frame) => &frame.args,
        | CircuitNode::Redex(ref redex) => core::slice::from_ref(&redex.source),
    }
}

/// Keep constructors, operations and rewrites in different label roles.
///
/// # Specification
/// trivial.
const fn node_sort(node: &CircuitNode) -> GeneratorSort
{
    match *node {
        | CircuitNode::Frame(ref frame) => match frame.head {
            | FrameHead::Ctor(_) => GeneratorSort::Value,
            | FrameHead::Op(_) => GeneratorSort::Operation,
        },
        | CircuitNode::Redex(_) => GeneratorSort::Rewrite,
    }
}

/// The original head spelling of one node.
///
/// # Specification
/// trivial.
const fn node_head(node: &CircuitNode) -> &Name
{
    match *node {
        | CircuitNode::Frame(ref frame) => frame.head.name(),
        | CircuitNode::Redex(ref redex) => &redex.rewrite,
    }
}

#[cfg(test)]
mod tests;
