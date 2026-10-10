//! Presentation-order invariance over generated diagrams: a random wire
//! renumbering and generator relisting of a generated diagram canonicalizes to
//! the form the original does, and both relabellings verify.
//!
//! The generator is biased toward the shapes where the traversal has no
//! boundary to anchor on — components with no boundary port, port-free
//! generators and isolated wires — and draws its labels from a three-label
//! alphabet, so seeds and components that tie on a prefix of their
//! linearization, or outright, are common rather than rare.

use anodized::spec;
use gandr_theory_circuit_algebras::DiagramEquality;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::canonicalize;
use gandr_theory_circuit_algebras::same_diagram;
use proptest::prelude::*;
use proptest::sample::Index;

/// One step of a generated diagram's construction.
#[derive(Clone, Debug)]
enum Step
{
    /// A wire no generator touches, declared on both legs.
    IsolatedWire,
    /// A new input port, open for a later generator to consume.
    Input,
    /// A generator over the wires still open.
    Generator
    {
        /// The generator's label.
        label: GeneratorLabel,
        /// One pick per source: the open wire each consumes, while any is
        /// open.
        picks: Vec<Index>,
        /// How many fresh wires it produces.
        produces: usize,
    },
}

/// How a wire still open after the last step is closed.
#[derive(Clone, Copy, Debug)]
enum Closing
{
    /// Declared as an output port.
    Output,
    /// Consumed by a terminal generator, leaving no port.
    Terminal,
}

/// A generated construction: its steps, then the closings cycled over the
/// wires the steps leave open.
#[derive(Clone, Debug)]
struct Recipe
{
    /// The construction steps, in order.
    steps: Vec<Step>,
    /// The closings, never empty, applied in turn to the open wires.
    closings: Vec<Closing>,
}

/// A diagram's parts, before assembly.
#[derive(Clone, Debug, Default)]
struct Built
{
    /// How many wires it declares.
    wires: usize,
    /// Its generators, in listing order.
    generators: Vec<Generator>,
    /// Its input ports, in order.
    inputs: Vec<Wire>,
    /// Its output ports, in order.
    outputs: Vec<Wire>,
}

/// A renumbering of a diagram's wires and a relisting of its generators.
#[derive(Clone, Debug)]
struct Relisting
{
    /// The new number of each wire, by its old number.
    wires: Vec<usize>,
    /// The old position of each generator, by its new position.
    edges: Vec<usize>,
}

impl Recipe
{
    /// Interprets the construction into a diagram inside the fragment.
    ///
    /// Every wire is fresh when it is created and is consumed at most once, by
    /// a generator created after it, so the diagram is monogamous and acyclic;
    /// every wire with no producer is declared an input, and every wire left
    /// unconsumed is declared an output or closed by a terminal, so it is
    /// boundary-honest.
    ///
    /// # Specification
    /// - requires: at least one closing and a representable total wire count.
    /// - ensures: follows the steps, then closes each remaining open wire in
    ///   cyclic closing order, producing monogamous, acyclic, boundary-honest
    ///   parts.
    /// - panics: none on the bounded recipe domain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed isolated, open and generated wires expose
    ///   cyclic closure and boundary roles. L1 — generated diagrams and their
    ///   permutations pass assembly and certificate verification. Losing an
    ///   open wire, duplicating a producer or assigning a backward dependency
    ///   differs; recipes have nonempty closings and representable allocation
    ///   counts.
    /// - witness: `tests::normal_form::recipe_closes_open_wires_and_preserves_isolated_roles`
    /// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
    #[spec(requires: !self.closings.is_empty() && self.steps.iter().try_fold(0_usize, |count, step| count.checked_add(match *step { Step::IsolatedWire | Step::Input => 1, Step::Generator { produces, .. } => produces })).is_some(),
    ensures: |ref built| built.wires == self.steps.iter().fold(0_usize, |count, step| count.saturating_add(match *step { Step::IsolatedWire | Step::Input => 1, Step::Generator { produces, .. } => produces }))
        && built.inputs.iter().chain(&built.outputs).all(|wire| usize::from(*wire) < built.wires)
        && built.generators.iter().all(|generator| generator.sources().iter().chain(generator.targets()).all(|wire| usize::from(*wire) < built.wires))
        && (0..built.wires).all(|position| {
            let wire = Wire::from(position);
            let produced = built.generators.iter().flat_map(Generator::targets).filter(|port| **port == wire).count();
            let consumed = built.generators.iter().flat_map(Generator::sources).filter(|port| **port == wire).count();
            produced <= 1 && consumed <= 1 && built.inputs.iter().filter(|port| **port == wire).count() == usize::from(produced == 0)
                && built.outputs.iter().filter(|port| **port == wire).count() == usize::from(consumed == 0)
                && built.generators.iter().position(|generator| generator.targets().contains(&wire)).zip(built.generators.iter().position(|generator| generator.sources().contains(&wire))).is_none_or(|(producer, consumer)| producer < consumer)
        }))]
    fn build(&self) -> Built
    {
        let mut built = Built::default();
        let mut open: Vec<Wire> = Vec::new();
        for step in &self.steps {
            match *step {
                | Step::IsolatedWire => {
                    let wire = built.fresh();
                    built.inputs.push(wire);
                    built.outputs.push(wire);
                },
                | Step::Input => {
                    let wire = built.fresh();
                    built.inputs.push(wire);
                    open.push(wire);
                },
                | Step::Generator {
                    ref label,
                    ref picks,
                    produces,
                } => {
                    let mut sources: Vec<Wire> = Vec::with_capacity(picks.len());
                    for pick in picks {
                        if open.is_empty() {
                            break;
                        }
                        sources.push(open.remove(pick.index(open.len())));
                    }
                    let targets: Vec<Wire> = core::iter::repeat_with(|| built.fresh())
                        .take(produces)
                        .collect();
                    open.extend(targets.iter().copied());
                    built
                        .generators
                        .push(Generator::new(label.clone(), sources, targets));
                },
            }
        }
        for (wire, closing) in open.into_iter().zip(self.closings.iter().cycle()) {
            match *closing {
                | Closing::Output => built.outputs.push(wire),
                | Closing::Terminal => built.generators.push(Generator::new(
                    GeneratorLabel::new("t", GeneratorSort::Terminal),
                    [wire],
                    [],
                )),
            }
        }
        built
    }
}

impl Built
{
    /// A fresh wire.
    ///
    /// # Specification
    /// - requires: another wire index is representable.
    /// - ensures: returns the previous count and increments it exactly once.
    /// - panics: none within the representable domain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — isolated, input and produced wires have distinct
    ///   consecutive positions in the mixed recipe witness. Reusing an index or
    ///   skipping one changes its boundary or incidence. Counts at the machine
    ///   limit are outside this bounded generator domain.
    /// - witness: `tests::normal_form::recipe_closes_open_wires_and_preserves_isolated_roles`
    /// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
    #[spec(requires: self.wires < usize::MAX, captures: [prior = self.wires], ensures: |wire| usize::from(wire) == prior && self.wires == prior.saturating_add(1))]
    fn fresh(&mut self) -> Wire
    {
        let wire = Wire::from(self.wires);
        self.wires = self.wires.saturating_add(1);
        wire
    }

    /// The parts assembled into a diagram.
    ///
    /// # Specification
    /// - requires: these parts satisfy the wiring assembly invariants.
    /// - ensures: preserves all counts, ordered generators and boundary ports.
    /// - panics: if assembly refuses malformed parts.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — generated original and permuted presentations are
    ///   assembled and their isomorphism certificates checked. Losing or
    ///   reordering a record changes the certificate or form; malformed parts
    ///   are outside the helper domain.
    /// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
    #[spec(ensures: |ref diagram| usize::from(diagram.wire_count()) == self.wires && diagram.generators() == self.generators && diagram.boundary().inputs() == self.inputs && diagram.boundary().outputs() == self.outputs)]
    fn assemble(&self) -> Wiring
    {
        Wiring::assemble(
            WireCount::from(self.wires),
            self.generators.clone(),
            Interface::new(self.inputs.clone(), self.outputs.clone()),
        )
        .expect("a generated diagram is monogamous, boundary-honest and acyclic")
    }

    /// The same diagram under `relisting`: every wire renumbered, the
    /// generators listed in the new order, the interface legs kept position
    /// by position.
    ///
    /// # Specification
    /// - requires: both relisting arrays are permutations of their respective
    ///   domains, and all ports name declared wires.
    /// - ensures: preserves every label and ordered port under the wire
    ///   permutation and lists generators in the requested order.
    /// - panics: on invalid permutation indices or undeclared ports.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — random full-domain permutations preserve the
    ///   canonical form and both independently verified relabellings. Reversing
    ///   the wire permutation, relisting ports or losing a generator changes
    ///   that evidence. The predicate states ordered correspondence without
    ///   canonicalizing a second time; inputs are bijections.
    /// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
    #[spec(requires: relisting.wires.len() == self.wires && relisting.edges.len() == self.generators.len()
        && relisting.wires.iter().enumerate().all(|entry| *entry.1 < self.wires && !relisting.wires.iter().take(entry.0).any(|prior| prior == entry.1))
        && relisting.edges.iter().enumerate().all(|entry| *entry.1 < self.generators.len() && !relisting.edges.iter().take(entry.0).any(|prior| prior == entry.1))
        && self.inputs.iter().chain(&self.outputs).chain(self.generators.iter().flat_map(|generator| generator.sources().iter().chain(generator.targets()))).all(|wire| usize::from(*wire) < self.wires),
    ensures: |ref result| result.wires == self.wires && result.generators.len() == self.generators.len()
        && [(&*self.inputs, &*result.inputs), (&*self.outputs, &*result.outputs)].into_iter().all(|(before, after)| before.len() == after.len()
            && before.iter().zip(after).all(|(wire, image)| relisting.wires.get(usize::from(*wire)).is_some_and(|mapped| *image == Wire::from(*mapped))))
        && result.generators.iter().zip(&relisting.edges).all(|(record, position)| self.generators.get(*position).is_some_and(|original|
            record.label() == original.label() && [(original.sources(), record.sources()), (original.targets(), record.targets())].into_iter().all(|(before, after)| before.len() == after.len()
                && before.iter().zip(after).all(|(wire, image)| relisting.wires.get(usize::from(*wire)).is_some_and(|mapped| *image == Wire::from(*mapped)))))))]
    fn relisted(
        &self,
        relisting: &Relisting,
    ) -> Self
    {
        let rename = |wire: &Wire| Wire::from(relisting.wires[usize::from(*wire)]);
        let generators = relisting
            .edges
            .iter()
            .map(|edge| {
                let generator = &self.generators[*edge];
                Generator::new(
                    generator.label().clone(),
                    generator
                        .sources()
                        .iter()
                        .map(rename)
                        .collect::<Vec<Wire>>(),
                    generator
                        .targets()
                        .iter()
                        .map(rename)
                        .collect::<Vec<Wire>>(),
                )
            })
            .collect();
        Self {
            wires: self.wires,
            generators,
            inputs: self.inputs.iter().map(rename).collect(),
            outputs: self.outputs.iter().map(rename).collect(),
        }
    }
}

/// A label from a small alphabet: two names, one of them also worn at a
/// second sort.
///
/// # Specification
/// trivial.
fn label() -> impl Strategy<Value = GeneratorLabel>
{
    prop_oneof![
        Just(GeneratorLabel::new("a", GeneratorSort::Value)),
        Just(GeneratorLabel::new("b", GeneratorSort::Value)),
        Just(GeneratorLabel::new("a", GeneratorSort::Operation)),
    ]
}

/// One construction step, weighted toward port-free generators, isolated
/// wires and generators that start a component from nothing.
///
/// # Specification
/// trivial.
fn step() -> impl Strategy<Value = Step>
{
    prop_oneof![
        2 => Just(Step::IsolatedWire),
        1 => Just(Step::Input),
        2 => label().prop_map(|label| Step::Generator {
            label,
            picks: Vec::new(),
            produces: 0,
        }),
        7 => (
            label(),
            proptest::collection::vec(any::<Index>(), 0 ..= 2_usize),
            0 ..= 2_usize,
        )
            .prop_map(|(label, picks, produces)| Step::Generator {
                label,
                picks,
                produces,
            }),
    ]
}

/// How an open wire is closed, weighted toward terminals so most components
/// keep no boundary port.
///
/// # Specification
/// trivial.
fn closing() -> impl Strategy<Value = Closing>
{
    prop_oneof![3 => Just(Closing::Terminal), 1 => Just(Closing::Output)]
}

/// A generated construction.
///
/// # Specification
/// trivial.
fn recipe() -> impl Strategy<Value = Recipe>
{
    (
        proptest::collection::vec(step(), 0 ..= 12_usize),
        proptest::collection::vec(closing(), 1 ..= 4_usize),
    )
        .prop_map(|(steps, closings)| Recipe { steps, closings })
}

/// A generated diagram with a random renumbering and relisting of it.
///
/// # Specification
/// - ensures: generates valid built parts and full-domain wire and generator
///   permutations, retaining interface positions.
/// - panics: none within the recipe strategy bounds.
/// - executable: none — the return type is an opaque strategy, which the
///   backend cannot name in its generated closure; observing samples also needs
///   a test runner rather than a predicate on the strategy value.
///
/// # Adequacy
/// - hypothesis: L1 — generated diagrams and random renumberings yield equal
///   forms with both certificates verified. The property also executes the
///   permutation-domain preconditions before relisting, so omissions or
///   duplicate indices fail. Sampling is bounded rather than exhaustive.
/// - witness: `tests::normal_form::every_presentation_permutation_canonicalizes_alike`
fn presented() -> impl Strategy<Value = (Built, Relisting)>
{
    recipe().prop_flat_map(|recipe| {
        let built = recipe.build();
        let wires = (0 .. built.wires).collect::<Vec<usize>>();
        let edges = (0 .. built.generators.len()).collect::<Vec<usize>>();
        (
            Just(built),
            Just(wires).prop_shuffle(),
            Just(edges).prop_shuffle(),
        )
            .prop_map(|(built, wires, edges)| (built, Relisting { wires, edges }))
    })
}

proptest! {
    /// A generated diagram and a renumbering and relisting of it reach one
    /// form; each relabelling verifies against its own presentation and that
    /// form, and the decision calls them one diagram with both relabellings.
    #[test]
    fn every_presentation_permutation_canonicalizes_alike(
        (built, relisting) in presented(),
    ) {
        let original = built.assemble();
        let permuted = built.relisted(&relisting).assemble();
        let left = canonicalize(&original);
        let right = canonicalize(&permuted);
        prop_assert_eq!(
            left.form(),
            right.form(),
            "a renumbering and relisting reaches the original's form"
        );
        prop_assert_eq!(
            Ok(()),
            left.relabelling().verify(&original, left.form()),
            "the original's relabelling is an isomorphism onto the form"
        );
        prop_assert_eq!(
            Ok(()),
            right.relabelling().verify(&permuted, right.form()),
            "and so is the permuted presentation's"
        );
        let DiagramEquality::Same(shared) = same_diagram(&original, &permuted)
        else {
            return Err(TestCaseError::fail("two presentations of one diagram are one diagram"));
        };
        prop_assert_eq!(
            Ok(()),
            shared.left().verify(&original, shared.form()),
            "the decision's left relabelling reaches the shared form"
        );
        prop_assert_eq!(
            Ok(()),
            shared.right().verify(&permuted, shared.form()),
            "and so does its right one"
        );
    }
}

#[test]
fn recipe_closes_open_wires_and_preserves_isolated_roles()
{
    let recipe = Recipe {
        steps: vec![Step::IsolatedWire, Step::Input, Step::Generator {
            label: GeneratorLabel::new("a", GeneratorSort::Value),
            picks: Vec::new(),
            produces: 1,
        }],
        closings: vec![Closing::Terminal, Closing::Output],
    };
    let built = recipe.build();
    assert_eq!(built.wires, 3);
    assert_eq!(built.inputs, [Wire::from(0), Wire::from(1)]);
    assert_eq!(built.outputs, [Wire::from(0), Wire::from(2)]);
    assert_eq!(built.generators.len(), 2);
    let first = built
        .generators
        .first()
        .expect("the generating step exists");
    assert!(first.sources().is_empty());
    assert_eq!(first.targets(), [Wire::from(2)]);
    let terminal = built.generators.last().expect("the closing exists");
    assert_eq!(terminal.sources(), [Wire::from(1)]);
    assert!(terminal.targets().is_empty());
    let wiring = built.assemble();
    let canonical = canonicalize(&wiring);
    assert_eq!(
        canonical.relabelling().verify(&wiring, canonical.form()),
        Ok(())
    );
}
