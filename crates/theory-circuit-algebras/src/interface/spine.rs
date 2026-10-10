//! The spine reading: one sequent command pattern read as a diagram with an
//! interface.
//!
//! The matcher quantifies over diagrams and the rewriting engines over terms.
//! This module is where the two meet: it reads a [`CmdPat`] as the monogamous
//! acyclic wiring the theory's conditions are stated over, so the embedding
//! matcher runs against the alphabet the engines hold and its verdict can be
//! compared with the one-sided matcher's where both apply. The reading is a
//! derived index: it holds nothing the command pattern does not, and nothing
//! reads it back as a term.
//!
//! # The reading
//!
//! A cut `⟨p |ε c⟩` reads as one cut wire, with the producer half above it and
//! the consumer spine below it:
//!
//! - a constructor `K(p̄)` is a [`GeneratorSort::Value`] generator whose one
//!   target is its output wire and whose sources are its arguments' wires;
//! - an operation frame `f(p̄; c)` is a [`GeneratorSort::Operation`] generator
//!   whose first source is the wire arriving down the spine, whose remaining
//!   sources are its arguments' wires, and whose one target continues the
//!   spine;
//! - a return-side constructor frame `K⁻(c)` is a [`GeneratorSort::Return`]
//!   generator from the arriving wire to the continuing one;
//! - the terminal `★` is a closed [`GeneratorSort::Terminal`] generator that
//!   consumes the arriving wire and produces none: a pattern ending in `★`
//!   demands the target end there too, which an open port would not;
//! - a producer metavariable is an input port, and a consumer metavariable
//!   declares the arriving wire an output port.
//!
//! # A name worn at both polarities is two interface nodes
//!
//! Interface nodes are keyed by metavariable, which is the `(name, category)`
//! pair the substitution keys bindings by. The seam shape `⟨r | seam(; r)⟩`
//! therefore reads as two nodes: the producer `r` an input port, the consumer
//! `r` an output port. Reading the name as one node — the cell metadata's
//! keying, which reads one hole at two polarities — would make the seam a
//! directed cycle and leave the fragment; it is not this view's reading.
//!
//! # A repeated hole is refused
//!
//! A metavariable occurring twice is a copy on a wire: it would leave the
//! fragment by out-degree two, and cell patterns are linear. The reading
//! refuses it by name rather than leaving it to surface as a fan-out.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cat;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsRef;
use gandr_theory_cell_complexes::ConsView;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::ProdRef;
use gandr_theory_cell_complexes::ProdView;
use gandr_theory_cell_complexes::Sym;
use quenchant_shape::shape::Maybe;

use crate::interface::Generator;
use crate::interface::GeneratorLabel;
use crate::interface::GeneratorName;
use crate::interface::GeneratorSort;
use crate::interface::Interface;
use crate::interface::Wire;
use crate::interface::WireCount;
use crate::interface::Wiring;
use crate::interface::WiringObstruction;

/// How the terminal consumer `★` is spelled as a generator name.
const TERMINAL: &str = "★";

/// The generator name a symbol spells.
///
/// # Specification
/// trivial.
fn name_of(symbol: &Sym) -> GeneratorName
{
    let spelling: &str = symbol.as_ref();
    GeneratorName::from(spelling)
}

quenchant_shape::reason_enum! {
    /// Why a spine reading has no port for a metavariable.
    pub mod spine_port {
        /// The reason the lookup finds no port.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The metavariable does not occur in the read pattern.
            NotInPattern,
        }
    }
}

/// A command pattern read as a diagram, with the wire its cut sits on and the
/// port each metavariable took.
///
/// The cut wire is the term reading's anchor: a one-sided term match is
/// exactly an embedding that sends the pattern's cut wire to the target's, and
/// without the anchor the relation is the strictly more general sub-diagram
/// one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpineReading
{
    /// The diagram the command pattern reads as.
    wiring: Wiring,
    /// The wire the cut sits on.
    cut: Wire,
    /// The port each metavariable took: a producer's input, a consumer's
    /// output.
    ports: BTreeMap<MetaVar, Wire>,
}

impl SpineReading
{
    /// The diagram.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wiring(&self) -> &Wiring
    {
        &self.wiring
    }

    /// The wire the cut sits on: the term reading's anchor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cut(&self) -> Wire
    {
        self.cut
    }

    /// The port `hole` took.
    ///
    /// # Specification
    /// - ensures: an input port of the wiring for a producer metavariable, an
    ///   output port for a consumer metavariable.
    /// - provides: [`spine_port::Absent::NotInPattern`] when `hole` does not
    ///   occur in the read pattern, at its category.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seam shape's producer and consumer `r` are
    ///   asserted on their two legs, and a name absent from the pattern is
    ///   absent.
    /// - witness: `interface::spine::tests::a_hole_at_both_polarities_reads_as_one_input_and_one_output`
    #[spec(ensures: |ref result| match *result {
        Maybe::Present(wire) => self.ports.get(hole) == Some(&wire) && match hole.cat() {
            Cat::Producer => self.wiring.boundary().inputs().contains(&wire),
            Cat::Consumer => self.wiring.boundary().outputs().contains(&wire),
        },
        Maybe::Absent(spine_port::Absent::NotInPattern) => !self.ports.contains_key(hole),
    })]
    #[inline]
    pub fn port_of(
        &self,
        hole: &MetaVar,
    ) -> Maybe<Wire, spine_port::Absent>
    {
        match self.ports.get(hole) {
            | Some(wire) => Maybe::Present(*wire),
            | None => Maybe::Absent(spine_port::Absent::NotInPattern),
        }
    }
}

/// A command pattern refused a spine reading.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SpineObstruction
{
    /// A metavariable occurs twice: a copy on a wire, which linearity refuses
    /// and monogamy excludes.
    RepeatedHole
    {
        /// The repeated metavariable.
        hole: MetaVar,
        /// The wire its first occurrence took.
        first: Wire,
        /// The wire its second occurrence would have taken.
        second: Wire,
    },
    /// The assembled diagram is outside the monogamous acyclic fragment.
    ///
    /// No linear command pattern reaches it; it is kept so the reading
    /// establishes the fragment rather than asserting it of its own output.
    Malformed
    {
        /// What assembly refused.
        obstruction: WiringObstruction,
    },
}

impl core::fmt::Display for SpineObstruction
{
    /// Names the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::RepeatedHole { .. } => "a metavariable occurs twice, a copy on a wire",
            | Self::Malformed { .. } => {
                "the read diagram is outside the monogamous acyclic fragment"
            },
        })
    }
}

impl core::error::Error for SpineObstruction
{
}

/// Reads a command pattern as a diagram with an interface, or refuses it.
///
/// # Specification
/// - ensures: one generator per constructor, operation frame, return frame and
///   terminal of `cmd`, numbered in reading order: the producer half
///   depth-first and left to right, then the consumer spine outermost frame
///   first, each operation frame before its arguments. The input ports are the
///   producer metavariables in first-occurrence order; the output port is the
///   consumer metavariable ending the spine, if one does; the cut wire is wire
///   0. Each metavariable is its own port, so a name worn at both polarities
///   is one input and one output.
/// - fails: [`SpineObstruction::RepeatedHole`] when a metavariable occurs
///   twice, naming it and both wires; [`SpineObstruction::Malformed`] if the
///   assembled diagram were outside the fragment, which no linear pattern
///   reaches.
/// - panics: none.
/// - intension: an explicit stack over each producer table and a loop down the
///   spine, so no part of the reading recurses on pattern depth.
///
/// # Errors
/// - [`SpineObstruction::RepeatedHole`]: `cmd` copies a metavariable.
/// - [`SpineObstruction::Malformed`]: assembly refused the read diagram.
///
/// # Adequacy
/// - hypothesis: L3 — the reading's generators, sorts, port order and anchor
///   are asserted exactly on a two-generator pattern and on one whose nodes
///   carry two holes each, where a reordered walk would show; the terminal is
///   separated from a port; the repeated hole is refused by name; the seam
///   shape reads as one input and one output. L2 — the embedding matcher over
///   this reading agrees with the substrate's one-sided matcher, seam rows
///   included.
/// - witness: `interface::spine::tests::a_spine_reads_as_its_generators_and_ports`
/// - witness: `interface::spine::tests::the_reading_declares_input_ports_in_first_occurrence_order`
/// - witness: `interface::spine::tests::a_terminal_is_a_closed_generator_not_a_port`
/// - witness: `interface::spine::tests::a_repeated_hole_is_refused_as_a_copy`
/// - witness: `interface::spine::tests::a_hole_at_both_polarities_reads_as_one_input_and_one_output`
/// - witness: `matching::tests::the_embedding_matcher_agrees_with_the_one_sided_matcher_on_the_spine`
#[spec(ensures: |ref result| {
    let producer = cmd.producer().to_ref();
    let consumer = cmd.consumer().to_ref();
    let nodes = usize::from(producer.size()).saturating_add(usize::from(consumer.size()));
    let holes = producer.metavars().chain(consumer.metavars()).count();
    match *result {
        Ok(ref reading) => reading.cut == Wire::from(0)
            && usize::from(reading.wiring.wire_count()) == nodes.saturating_sub(1)
            && usize::from(reading.wiring.edge_count()) == nodes.saturating_sub(holes)
            && reading.ports.len() == holes
            && producer.metavars().chain(consumer.metavars()).all(|hole| reading.ports.get(hole).is_some_and(|wire| match hole.cat() {
                Cat::Producer => reading.wiring.boundary().inputs().contains(wire),
                Cat::Consumer => reading.wiring.boundary().outputs().contains(wire),
            })),
        Err(SpineObstruction::RepeatedHole { ref hole, first, second }) => first != second
            && producer.metavars().chain(consumer.metavars()).filter(|candidate| *candidate == hole).count() > 1
            && usize::from(first) < nodes.saturating_sub(1) && usize::from(second) < nodes.saturating_sub(1),
        Err(SpineObstruction::Malformed { .. }) => true,
    }
})]
#[inline]
pub fn read_spine(cmd: &CmdPat) -> Result<SpineReading, SpineObstruction>
{
    let mut reader = Reader::default();
    let cut = reader.fresh();
    read_producer(cmd.producer().to_ref(), cut, &mut reader)?;
    read_consumer(cmd.consumer().to_ref(), cut, &mut reader)?;
    let boundary = Interface::new(reader.inputs, reader.outputs);
    match Wiring::assemble(WireCount::from(reader.next), reader.generators, boundary) {
        | Ok(wiring) => Ok(SpineReading {
            wiring,
            cut,
            ports: reader.ports,
        }),
        | Err(obstruction) => Err(SpineObstruction::Malformed { obstruction }),
    }
}

/// The reading's working state: wires allocated, generators emitted, ports
/// declared, and the port each metavariable took.
#[derive(Default)]
struct Reader
{
    /// The generators emitted so far.
    generators: Vec<Generator>,
    /// The next unallocated wire index.
    next: usize,
    /// The input ports, in declaration order.
    inputs: Vec<Wire>,
    /// The output ports, in declaration order.
    outputs: Vec<Wire>,
    /// The port each metavariable took.
    ports: BTreeMap<MetaVar, Wire>,
}

impl Reader
{
    /// Allocates the next wire.
    ///
    /// # Specification
    /// - requires: one more wire index is representable.
    /// - ensures: a wire no earlier call returned; wires are numbered from 0 in
    ///   allocation order. A pattern held in memory never allocates
    ///   `usize::MAX` wires, so the counter never saturates.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consecutive allocation and a mixed-polarity pattern
    ///   expose exact wire indices and boundary legs. Repeating an index,
    ///   skipping an index or using a nonzero initial cut differs; exhausted
    ///   index space is excluded.
    /// - witness: `interface::spine::tests::wire_allocation_and_declaration_keep_both_legs_ordered`
    /// - witness: `interface::spine::tests::a_spine_reads_as_its_generators_and_ports`
    #[spec(requires: self.next < usize::MAX, captures: [prior = self.next],
            ensures: |wire| usize::from(wire) == prior && self.next == prior.saturating_add(1))]
    fn fresh(&mut self) -> Wire
    {
        let wire = Wire::from(self.next);
        self.next = self.next.saturating_add(1);
        wire
    }

    /// Declares `wire` the port of `hole`: an input for a producer, an output
    /// for a consumer.
    ///
    /// # Specification
    /// - requires: `wire` is already allocated.
    /// - ensures: `hole` is recorded once, on the leg its category names.
    /// - fails: [`SpineObstruction::RepeatedHole`] when `hole` already took a
    ///   port. A consumer metavariable only ends a spine, so the repeat is
    ///   reachable for a producer metavariable alone.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SpineObstruction::RepeatedHole`] on a second occurrence of `hole`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh producer and consumer holes, including one name
    ///   at both polarities, expose leg order and exact map entries; repeats on
    ///   either leg expose the first and rejected wire without changing state.
    ///   Category erasure, reordering and partial mutation on refusal differ;
    ///   the wire is allocated by the reader.
    /// - witness: `interface::spine::tests::wire_allocation_and_declaration_keep_both_legs_ordered`
    /// - witness: `interface::spine::tests::a_repeated_hole_is_refused_as_a_copy`
    #[spec(requires: usize::from(wire) < self.next, captures: [
        prior = self.ports.get(hole).copied(), count = self.ports.len(),
        inputs = self.inputs.len(), outputs = self.outputs.len(), next = self.next,
    ], ensures: |ref result| self.next == next && match *result {
        Ok(()) => prior.is_none() && self.ports.len() == count.saturating_add(1) && self.ports.get(hole) == Some(&wire)
            && match hole.cat() {
                Cat::Producer => self.inputs.len() == inputs.saturating_add(1) && self.inputs.last() == Some(&wire) && self.outputs.len() == outputs,
                Cat::Consumer => self.outputs.len() == outputs.saturating_add(1) && self.outputs.last() == Some(&wire) && self.inputs.len() == inputs,
            },
        Err(SpineObstruction::RepeatedHole { hole: ref repeated, first, second }) => repeated == hole && prior == Some(first) && second == wire
            && self.ports.get(hole) == Some(&first) && self.ports.len() == count && self.inputs.len() == inputs && self.outputs.len() == outputs,
        Err(SpineObstruction::Malformed { .. }) => false,
    })]
    fn declare(
        &mut self,
        hole: &MetaVar,
        wire: Wire,
    ) -> Result<(), SpineObstruction>
    {
        if let Some(first) = self.ports.get(hole).copied() {
            return Err(SpineObstruction::RepeatedHole {
                hole: hole.clone(),
                first,
                second: wire,
            });
        }
        self.ports.insert(hole.clone(), wire);
        match hole.cat() {
            | Cat::Producer => self.inputs.push(wire),
            | Cat::Consumer => self.outputs.push(wire),
        }
        Ok(())
    }
}

/// Reads a producer table whose value leaves on `out`.
///
/// # Specification
/// - requires: `out` is allocated and is the wire this producer produces.
/// - ensures: one [`GeneratorSort::Value`] generator per constructor node, in
///   depth-first left-to-right order, each with fresh source wires for its
///   arguments; each metavariable leaf declared an input port.
/// - fails: the repeated-hole refusal of [`Reader::declare`].
/// - panics: none.
/// - intension: an explicit stack of `(subtree, wire)` pairs, so the walk never
///   recurses on pattern depth.
///
/// # Errors
/// [`SpineObstruction::RepeatedHole`] on a copied metavariable.
///
/// # Adequacy
/// - hypothesis: L3 — branching producer trees and repeated leaves expose
///   constructor order, fresh-wire counts and input-port order, or exact
///   repetition refusal. Reversed child traversal, omitted constructors or
///   treating a producer hole as an output differs; the output wire is
///   allocated and the producer pattern is well-formed.
/// - witness: `interface::spine::tests::a_spine_reads_as_its_generators_and_ports`
/// - witness: `interface::spine::tests::the_reading_declares_input_ports_in_first_occurrence_order`
/// - witness: `interface::spine::tests::a_repeated_hole_is_refused_as_a_copy`
#[spec(requires: usize::from(out) < reader.next, captures: [
    generators = reader.generators.len(), next = reader.next, inputs = reader.inputs.len(), outputs = reader.outputs.len(),
], ensures: |ref result| reader.outputs.len() == outputs && match *result {
    Ok(()) => {
        let holes = root.metavars().count();
        let nodes = usize::from(root.size());
        reader.next == next.saturating_add(nodes.saturating_sub(1))
            && reader.generators.len() == generators.saturating_add(nodes.saturating_sub(holes))
            && reader.inputs.len() == inputs.saturating_add(holes)
            && reader.generators.iter().skip(generators).all(|generator| generator.label().sort() == GeneratorSort::Value)
            && reader.inputs.iter().skip(inputs).zip(root.metavars()).all(|(wire, hole)| reader.ports.get(hole) == Some(wire))
            && match root.view() {
                ProdView::Meta(hole) => reader.ports.get(hole) == Some(&out),
                ProdView::Ctor { ctor, args } => reader.generators.get(generators).is_some_and(|generator|
                    generator.label().name().as_ref() == ctor.as_ref() && generator.sources().len() == args.len() && generator.targets() == [out]),
            }
    },
    Err(SpineObstruction::RepeatedHole { ref hole, first, second }) => reader.ports.get(hole) == Some(&first) && usize::from(second) < reader.next,
    Err(SpineObstruction::Malformed { .. }) => false,
})]
fn read_producer(
    root: ProdRef<'_>,
    out: Wire,
    reader: &mut Reader,
) -> Result<(), SpineObstruction>
{
    let mut stack: Vec<(ProdRef<'_>, Wire)> = alloc::vec![(root, out)];
    while let Some((node, wire)) = stack.pop() {
        match node.view() {
            | ProdView::Meta(hole) => {
                reader.declare(hole, wire)?;
            },
            | ProdView::Ctor { ctor, args } => {
                let mut sources: Vec<Wire> = Vec::with_capacity(args.len());
                let pushed = stack.len();
                for arg in args {
                    let source = reader.fresh();
                    sources.push(source);
                    stack.push((arg, source));
                }
                if let Some(pending) = stack.get_mut(pushed ..) {
                    pending.reverse();
                }
                reader.generators.push(Generator::new(
                    GeneratorLabel::new(name_of(ctor), GeneratorSort::Value),
                    sources,
                    [wire],
                ));
            },
        }
    }
    Ok(())
}

/// Reads a consumer spine whose value arrives on `arriving`.
///
/// # Specification
/// - requires: `arriving` is allocated and is the wire the spine's outermost
///   frame consumes.
/// - ensures: one generator per operation frame, return frame and terminal,
///   threaded on one wire each; an operation frame's argument wires are
///   allocated before its continuation and read after it is emitted; a consumer
///   metavariable ending the spine declared an output port.
/// - fails: the repeated-hole refusal of [`Reader::declare`], from a frame's
///   producer arguments or the spine's end.
/// - panics: none.
/// - intension: a loop down the spine, so the walk never recurses on spine
///   length.
///
/// # Errors
/// [`SpineObstruction::RepeatedHole`] on a copied metavariable.
///
/// # Adequacy
/// - hypothesis: L3 — operation and return frames, producer arguments, a
///   terminal and a consumer-hole end expose exact generator roles, threading
///   and port order. Wrong root roles, missing frames, reordered arguments or a
///   fabricated terminal port differs; the arriving wire is allocated and no
///   general graph is read here.
/// - witness: `interface::spine::tests::a_spine_reads_as_its_generators_and_ports`
/// - witness: `interface::spine::tests::the_reading_declares_input_ports_in_first_occurrence_order`
/// - witness: `interface::spine::tests::a_terminal_is_a_closed_generator_not_a_port`
/// - witness: `interface::spine::tests::a_hole_at_both_polarities_reads_as_one_input_and_one_output`
#[spec(requires: usize::from(arriving) < reader.next, captures: [
    generators = reader.generators.len(), next = reader.next, inputs = reader.inputs.len(), outputs = reader.outputs.len(),
], ensures: |ref result| match *result {
    Ok(()) => {
        let nodes = usize::from(root.size());
        let holes = root.metavars().count();
        let consumer_holes = root.metavars().filter(|hole| hole.cat() == Cat::Consumer).count();
        reader.next == next.saturating_add(nodes.saturating_sub(1))
            && reader.generators.len() == generators.saturating_add(nodes.saturating_sub(holes))
            && reader.inputs.len() == inputs.saturating_add(holes.saturating_sub(consumer_holes))
            && reader.outputs.len() == outputs.saturating_add(consumer_holes)
            && reader.inputs.iter().skip(inputs).zip(root.metavars().filter(|hole| hole.cat() == Cat::Producer)).all(|(wire, hole)| reader.ports.get(hole) == Some(wire))
            && reader.outputs.iter().skip(outputs).zip(root.metavars().filter(|hole| hole.cat() == Cat::Consumer)).all(|(wire, hole)| reader.ports.get(hole) == Some(wire))
            && match root.view() {
                ConsView::Meta(hole) => reader.ports.get(hole) == Some(&arriving),
                ConsView::Top => reader.generators.get(generators).is_some_and(|generator| generator.label().sort() == GeneratorSort::Terminal && generator.sources() == [arriving] && generator.targets().is_empty()),
                ConsView::Frame { ctor, .. } => reader.generators.get(generators).is_some_and(|generator| generator.label().sort() == GeneratorSort::Return && generator.label().name().as_ref() == ctor.as_ref() && generator.sources() == [arriving] && generator.targets().len() == 1),
                ConsView::Op { op, args, .. } => reader.generators.get(generators).is_some_and(|generator| generator.label().sort() == GeneratorSort::Operation && generator.label().name().as_ref() == op.as_ref() && generator.sources().first() == Some(&arriving) && generator.sources().len() == args.len().saturating_add(1) && generator.targets().len() == 1),
            }
    },
    Err(SpineObstruction::RepeatedHole { ref hole, first, second }) => reader.ports.get(hole) == Some(&first) && usize::from(second) < reader.next,
    Err(SpineObstruction::Malformed { .. }) => false,
})]
fn read_consumer(
    root: ConsRef<'_>,
    arriving: Wire,
    reader: &mut Reader,
) -> Result<(), SpineObstruction>
{
    let mut node = root;
    let mut wire = arriving;
    loop {
        match node.view() {
            | ConsView::Meta(hole) => return reader.declare(hole, wire),
            | ConsView::Top => {
                reader.generators.push(Generator::new(
                    GeneratorLabel::new(TERMINAL, GeneratorSort::Terminal),
                    [wire],
                    [],
                ));
                return Ok(());
            },
            | ConsView::Frame { ctor, ret } => {
                let next = reader.fresh();
                reader.generators.push(Generator::new(
                    GeneratorLabel::new(name_of(ctor), GeneratorSort::Return),
                    [wire],
                    [next],
                ));
                wire = next;
                node = ret;
            },
            | ConsView::Op { op, args, ret } => {
                let mut sources: Vec<Wire> = Vec::with_capacity(args.len().saturating_add(1));
                sources.push(wire);
                let mut pending: Vec<(ProdRef<'_>, Wire)> = Vec::with_capacity(args.len());
                for arg in args {
                    let source = reader.fresh();
                    sources.push(source);
                    pending.push((arg, source));
                }
                let next = reader.fresh();
                reader.generators.push(Generator::new(
                    GeneratorLabel::new(name_of(op), GeneratorSort::Operation),
                    sources,
                    [next],
                ));
                for (arg, source) in pending {
                    read_producer(arg, source, reader)?;
                }
                wire = next;
                node = ret;
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    extern crate std;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::ProdPat;

    use super::*;
    use crate::interface::Edge;
    use crate::interface::EdgeCount;
    use crate::interface::wire_consumer;
    use crate::interface::wire_producer;

    /// `⟨Succ(m) | add(n; α)⟩`: the running two-generator pattern.
    ///
    /// # Specification
    /// trivial.
    fn succ_add() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        )
    }

    /// The generator at `edge`, which the fixture's diagram holds.
    ///
    /// # Specification
    /// - requires: the edge is present and names a generator of `wiring`.
    /// - ensures: the borrowed generator at that position.
    /// - panics: on an absent or out-of-range fixture edge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real spine generators expose their labels and ordered
    ///   ports, while absent and first-past edges panic. A different generator
    ///   or a fabricated fallback changes these observations; this is a fixture
    ///   observer, not a fallible public lookup.
    /// - witness: `interface::spine::tests::a_spine_reads_as_its_generators_and_ports`
    /// - witness: `interface::spine::tests::generator_observer_refuses_absent_or_out_of_range_edges`
    #[spec(requires: match *edge { Maybe::Present(index) => usize::from(index) < wiring.generators().len(), Maybe::Absent(_) => false },
        ensures: |generator| match *edge {
            Maybe::Present(index) => wiring.generators().get(usize::from(index)).is_some_and(|expected| core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(generator))),
            Maybe::Absent(_) => false,
        })]
    fn generator_at<'wiring, R>(
        wiring: &'wiring Wiring,
        edge: &Maybe<Edge, R>,
    ) -> &'wiring Generator
    {
        let Maybe::Present(edge) = *edge
        else {
            panic!("the fixture's wire has a generator on that side");
        };
        let Maybe::Present(generator) = wiring.generator(edge)
        else {
            panic!("the incidence maps name only generators of the diagram");
        };
        generator
    }

    #[test]
    fn a_spine_reads_as_its_generators_and_ports()
    {
        let reading = read_spine(&succ_add()).expect("the running pattern is linear");
        let wiring = reading.wiring();
        assert_eq!(
            EdgeCount::from(2),
            wiring.edge_count(),
            "one generator for Succ and one for the add frame"
        );
        assert_eq!(
            2_usize,
            wiring.boundary().inputs().len(),
            "the two producer metavariables are the open inputs"
        );
        assert_eq!(
            1_usize,
            wiring.boundary().outputs().len(),
            "and the consumer metavariable is the one open output"
        );
        let producer = generator_at(wiring, &wiring.producer_of(reading.cut()));
        assert_eq!(
            GeneratorSort::Value,
            producer.label().sort(),
            "the cut's producer is the value-side constructor"
        );
        assert_eq!(
            "Succ",
            producer.label().name().as_ref(),
            "and it is the one the pattern names"
        );
        let consumer = generator_at(wiring, &wiring.consumer_of(reading.cut()));
        assert_eq!(
            GeneratorSort::Operation,
            consumer.label().sort(),
            "the spine head is the operation frame"
        );
        assert_eq!(
            2_usize,
            consumer.sources().len(),
            "which takes the arriving wire and its one argument"
        );
        assert_eq!(
            Some(&reading.cut()),
            consumer.sources().first(),
            "with the arriving wire first"
        );
    }

    #[test]
    fn the_reading_declares_input_ports_in_first_occurrence_order()
    {
        // `⟨Pair(x, y) | add(u, v; α)⟩`. Port order is observable only once a
        // node carries two holes: with one per node every walk order agrees.
        let cmd = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("y")]),
            ConsPat::op(
                "add",
                [ProdPat::meta("u"), ProdPat::meta("v")],
                ConsPat::meta("alpha"),
            ),
        );
        let reading = read_spine(&cmd).expect("the fixture is linear");
        let wiring = reading.wiring();
        assert_eq!(
            &wires![1, 2, 3, 4][..],
            wiring.boundary().inputs(),
            "x, y, u, v: depth-first left to right, which is first-occurrence order"
        );
        assert_eq!(
            &wires![5][..],
            wiring.boundary().outputs(),
            "and the consumer metavariable is the one output"
        );
        let head = generator_at(wiring, &wiring.consumer_of(reading.cut()));
        assert_eq!(
            &wires![0, 3, 4][..],
            head.sources(),
            "the operation frame takes the arriving wire, then its arguments in order"
        );
    }

    #[test]
    fn a_terminal_is_a_closed_generator_not_a_port()
    {
        // A pattern ending in ★ demands the target end there too, so the
        // terminal is a generator consuming a wire and producing none.
        let closed = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let reading = read_spine(&closed).expect("a ground closed cut is linear");
        let wiring = reading.wiring();
        assert_eq!(
            EdgeCount::from(2),
            wiring.edge_count(),
            "the constructor and the terminal are both generators"
        );
        assert!(
            wiring.boundary().outputs().is_empty(),
            "and the diagram has no open output"
        );
        let terminal = generator_at(wiring, &wiring.consumer_of(reading.cut()));
        assert_eq!(
            GeneratorSort::Terminal,
            terminal.label().sort(),
            "the terminal carries its own sort"
        );
        assert!(
            terminal.targets().is_empty(),
            "and produces nothing, which is what makes it closed"
        );
    }

    #[test]
    fn a_repeated_hole_is_refused_as_a_copy()
    {
        let copied = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
            ConsPat::top(),
        );
        assert_eq!(
            Err(SpineObstruction::RepeatedHole {
                hole: MetaVar::producer("x"),
                first: Wire::from(1),
                second: Wire::from(2),
            }),
            read_spine(&copied),
            "the refusal names the copied hole and the wires both occurrences take"
        );
    }

    #[test]
    fn a_hole_at_both_polarities_reads_as_one_input_and_one_output()
    {
        // ⟨r | seam(; r)⟩: one name worn by a producer and a consumer
        // metavariable. Keyed by metavariable, as the substitution keys
        // bindings, it is two interface nodes: r once on each leg.
        let seam = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("r"),
            ConsPat::op("seam", [], ConsPat::meta("r")),
        );
        let reading = read_spine(&seam).expect("a name at both polarities reads as two nodes");
        let wiring = reading.wiring();
        assert_eq!(
            Maybe::Present(reading.cut()),
            reading.port_of(&MetaVar::producer("r")),
            "the producer r is the cut wire, entering as a port"
        );
        assert_eq!(
            &[reading.cut()][..],
            wiring.boundary().inputs(),
            "and it is the one input"
        );
        assert_eq!(
            Maybe::Present(Wire::from(1)),
            reading.port_of(&MetaVar::consumer("r")),
            "the consumer r is the wire the seam frame continues on"
        );
        assert_eq!(
            &wires![1][..],
            wiring.boundary().outputs(),
            "and it is the one output"
        );
        let frame = generator_at(wiring, &wiring.consumer_of(reading.cut()));
        assert_eq!(
            (&wires![0][..], &wires![1][..]),
            (frame.sources(), frame.targets()),
            "the seam frame runs from the input r to the output r, with no loop back"
        );
        assert_eq!(
            Maybe::Absent(wire_producer::Absent::BoundaryInput),
            wiring.producer_of(reading.cut()),
            "the input r has no producer"
        );
        assert_eq!(
            Maybe::Absent(wire_consumer::Absent::BoundaryOutput),
            wiring.consumer_of(Wire::from(1)),
            "and the output r no consumer"
        );
        assert_eq!(
            Maybe::Absent(spine_port::Absent::NotInPattern),
            reading.port_of(&MetaVar::producer("s")),
            "a name the pattern does not wear has no port"
        );
    }

    #[test]
    fn wire_allocation_and_declaration_keep_both_legs_ordered()
    {
        let mut reader = Reader::default();
        let first = reader.fresh();
        let second = reader.fresh();
        let third = reader.fresh();
        assert_eq!([first, second, third], wires![0, 1, 2]);
        reader
            .declare(&MetaVar::producer("x"), first)
            .expect("first input");
        reader
            .declare(&MetaVar::consumer("x"), second)
            .expect("same name on the other leg");
        reader
            .declare(&MetaVar::producer("y"), third)
            .expect("second input");
        assert_eq!(reader.inputs, wires![0, 2]);
        assert_eq!(reader.outputs, wires![1]);
        let before = reader.ports.clone();
        assert_eq!(
            reader.declare(&MetaVar::producer("x"), third),
            Err(SpineObstruction::RepeatedHole {
                hole: MetaVar::producer("x"),
                first,
                second: third
            })
        );
        assert_eq!(
            reader.declare(&MetaVar::consumer("x"), first),
            Err(SpineObstruction::RepeatedHole {
                hole: MetaVar::consumer("x"),
                first: second,
                second: first
            })
        );
        assert_eq!(reader.ports, before);
        assert_eq!(reader.inputs, wires![0, 2]);
        assert_eq!(reader.outputs, wires![1]);
    }

    #[test]
    fn generator_observer_refuses_absent_or_out_of_range_edges()
    {
        let reading = read_spine(&succ_add()).expect("valid spine");
        let absent: Maybe<Edge, wire_producer::Absent> =
            Maybe::Absent(wire_producer::Absent::BoundaryInput);
        assert!(std::panic::catch_unwind(|| generator_at(reading.wiring(), &absent)).is_err());
        let foreign: Maybe<Edge, wire_producer::Absent> =
            Maybe::Present(Edge::from(usize::from(reading.wiring().edge_count())));
        assert!(std::panic::catch_unwind(|| generator_at(reading.wiring(), &foreign)).is_err());
    }
}
