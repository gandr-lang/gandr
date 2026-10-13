//! `ua_n` at every certified stratum, derived from code univalence.
//!
//! An equivalence of graphical species, given by its translators at each
//! corolla, is a path of the certificate universe between the two species'
//! degree telescopes, derived corolla by corolla.
//!
//! # The statement
//!
//! Fix a catalogue and a degree `n ≥ 1` whose stratum `gandr-theory-sites`
//! certifies: the corolla condition, and the Segal condition at every shape
//! of degree two to `n`. The quantifier range is every shape of degree at
//! most `n` in that catalogue; the alphabet is the stratum's probes, the
//! raising maps out of its shapes that send each vertex to one vertex. For two
//! species `a` and `b` and an equivalence `e : Equiv a b` given, at each
//! corolla `C` the species inhabit, by a pair of closed translators between the
//! codes `⌜a(C)⌝` and `⌜b(C)⌝`, [`derive()`] returns a value of
//! `Path_U(⌜Telₙ a⌝, ⌜Telₙ b⌝)` whose every component the kernel replays. A
//! stratum the site does not certify has no [`SegalStratum`] to pass, so
//! `ua_n` there is refused before it is asked:
//! [`gandr_theory_sites::Uncertified`] names the degree, or the failing shape
//! and the degree whose condition it fails.
//!
//! The target is the certificate universe, never the ambient identity type.
//! Over decidable codes Hedberg's theorem makes the ambient identity a
//! proposition, so a `ua` into it would identify the swap of a binary
//! generator with the identity; in the certificate universe the two are two
//! certificates, each replayed, and their identity is the record of their
//! translators' pointwise identities.
//!
//! # The codes and the telescope
//!
//! The code of a species at a corolla, [`code`], is the sum of one unit per
//! element of the species there, in the stratum's enumeration order, so an
//! element is an injection of the unit and a translator is a function between
//! two such sums. The degree telescope reads a diagram on the site degree by
//! degree, each stage a type over the matching object of the stage below.
//! Degree zero holds the empty shape, whose value the strict Segal condition
//! fixes as the unit; each corolla's matching object is that unit, so degree
//! one is a plain product over the corollas the species inhabit, in catalogue
//! order. At each degree `d` from two to `n` every shape is the colimit of its
//! corollas, which the stratum certifies, so a free algebra's value there is
//! the product of its corolla values: the stage adds no data over the stages
//! below, and its type is the unit. `⌜Telₙ a⌝` is
//! `() × (⌜a(C₁)⌝ × (… × (⌜a(Cₖ)⌝ × (() × … ()))))`, the `n − 1` units of
//! degrees two to `n` last, nested to the right as the kernel's binary path
//! product nests; at degree one with one corolla it is `() × ⌜a(C₁)⌝`, and
//! with none `()`.
//!
//! # The derivation
//!
//! [`derive()`] evaluates each translator at every element to read its table,
//! checks the tables as an equivalence of species at the stratum — mutually
//! inverse and natural along every automorphism of the corolla, a condition
//! code univalence alone does not see — and decides each corolla's code
//! univalence by [`crate::equiv::decide`], the round trips by computation and
//! their traces the evidence the kernel replays. The path is reflexivity at
//! the unit for degree zero, the universe certificate over each corolla's two
//! codes with the given translators, reflexivity at the unit for each degree
//! from two to `n`, and the native path product over them. Declared at its
//! classifier and checked, it crosses the bridge as the kernel's native path,
//! and admission replays every corolla's round trips.
//!
//! # The written statement
//!
//! `ua[n, k](a, b, f, g)` states univalence at the stratum of degree `n` over
//! the catalogue of shapes up to size `k`: the statement fixes its alphabet
//! and its quantifier range, so a check never ranges past what it names. `a`
//! and `b` are two signature descriptions, one generator per operation at the
//! corolla of its arity; `f` and `g` are records keyed by generator labels,
//! each field the translator at the corolla its label names, `f` from the
//! codes of `a` to those of `b` and `g` back. The lowering resolves the
//! descriptions by name and the node carries them, so the checker reads no
//! name.
//!
//! Checking runs in two steps. The premises check every translator against
//! the arrow between its corolla's two [`code`]s, so a translator at the wrong
//! code is a type mismatch before any table is read. The decision then
//! certifies the stratum — the bound within an allowance of five, the degree
//! one or more, the catalogue's site meeting the corolla condition and, from
//! degree two, the Segal condition — sends each label to its generator's
//! corolla, requires one translator per corolla on each side and runs
//! [`derive()`]. A refusal names its defect: a [`StratumDefect`] for the
//! stratum, a [`UaDefect`] for the translators.
//!
//! The statement synthesises `Path(Type, ⌜Telₙ a⌝, ⌜Telₙ b⌝)`, as
//! `equiv(f, g)` does: the element identity at the universe, whose fibre the
//! kernel computes as the universe path, so the target stays the certificate
//! universe and transport along it is element transport in any motive over the
//! universe. The derived path is recorded at the statement's node and read
//! back by the bridge, which erases the node to it; a constant defined as a
//! statement unfolds to it, so transport along the constant moves an element
//! through the translators. The node itself is inert under evaluation: a
//! transport along a statement written in place, rather than through a
//! constant, does not compute.
//!
//! # Obligations
//!
//! - **The corolla restriction.** `ua-desc : Terms a ≅ Terms b → a ≅ b` is not
//!   full faithfulness alone: an isomorphism of the free algebras is reflected
//!   to the generating species by restricting it to the corollas. That lemma is
//!   `gandr_theory_sites::restrict`, with its own witness, at every certified
//!   stratum; it is why an equivalence given at the corollas is the whole of
//!   `Equiv a b` there, and why [`derive()`] reads nothing past them.
//! - **The two-cell coherence.** A univalence map must be a typoid function
//!   (Petrakis): equivalent equivalences go to identified paths. Two
//!   equivalences whose translators agree pointwise give certificates the
//!   kernel's structural conversion keeps apart, so the identification is not
//!   conversion; it is the identity record of the two certificates at each
//!   corolla, and reflexivity at each unit stage. Its translator fields are
//!   function extensionalities the judgement decides and the kernel replays as
//!   higher evaluations: that much is witnessed here, at the binary corolla.
//!   Its round-trip coherence fields relate two reflected round trips at a sum
//!   of units, where identity of elements is decidable; the kernel's record
//!   view of two certificates observes all four fields by replay, and its
//!   witness runs negation against a case-inlined triple negation at Bool, the
//!   binary corolla's code. Equivalent equivalences are related by those
//!   fields; distinct ones are refused at the first corolla whose translators
//!   differ at an element.
//! - **The pasting coherence.** The pasting-side analogue holds at every
//!   certified stratum by the same identity record. An automorphism `σ` of a
//!   corolla is a two-cell between the corolla's inclusion `ι` and `ι ∘ σ`; it
//!   acts on a certificate by conjugating its translators with `σ`'s action on
//!   the two codes, and the conjugate is identified with the certificate
//!   through translator fields that are the equivalence's naturality equations
//!   at `σ`, replayed as higher evaluations. The unit stages carry reflexivity,
//!   so the stages above degree one add no field. Witnessed at degree two: at
//!   the binary corolla's code the swap's certificate is identified with its
//!   conjugate by the input swap; on two binary generators the exchange's
//!   conjugate computes the exchange and is a certificate beside it, while the
//!   crossed exchange, which the stratum refuses, computes another table under
//!   conjugation. Function extensionality decides binary sums, so at a code of
//!   more than two elements the translator field is refused by name,
//!   `FunextUnsupported`, and the identification there is stated, not replayed.
//!   The substitutions that send a vertex to a sub-graph stay outside the
//!   alphabet, so their two-cells are not stated.
//! - **The target discipline.** As above: `Path_U`, never the ambient identity
//!   type.
//!
//! # Decisions
//!
//! - **Translators, not tables, as the input.** The certificate keeps the
//!   programs it was given, as `equiv(f, g)` does, so a path through
//!   [`derive()`] and one written by hand are the same artifact. The
//!   alternative, minting canonical case tables from the evaluated tables,
//!   makes equivalent equivalences convertible and so discharges the two-cell
//!   obligation by normalisation; it is a second identity of certificates
//!   beside the kernel's, and conversion would no longer be structural.
//!   Reversal: a kernel conversion that compares certificates by their tables.
//!   [`tabulate`] mints the canonical translator for a table, for a caller that
//!   holds tables.
//! - **The telescope's unit is explicit.** Degree zero is a component, so the
//!   telescope of a species with no generators is the unit and its path
//!   reflexivity. Reversal: a stratum whose empty shape holds more than one
//!   value.
//! - **One unit stage per degree above one.** A degree's stage is the product
//!   of its shapes' fibres over the stages below, each the unit at a certified
//!   stratum, so the stage is one unit whatever the degree's shape count, and
//!   the classifier names the degree it was derived at. The alternative, a unit
//!   per shape, grows the telescope with the catalogue and carries no more;
//!   omitting the stages makes `ua_n` one path at every degree, and the
//!   classifier forgets which Segal condition stood behind it. Reversal: a
//!   stratum certified by a weak Segal condition, whose fibres carry data.
//! - **The stratum in the statement's head.** `ua[n, k]` names its degree and
//!   its bound as instantiation arguments, so the stratum is fixed where the
//!   statement stands and the printer writes it back. The alternatives were a
//!   checker-wide stratum, which makes two modules' statements incomparable,
//!   and a bound inferred from the largest generator, a catalogue that grows
//!   silently with an edit. A degree the catalogue does not certify is refused
//!   by name, not unparsed. Reversal: a site whose catalogue the descriptions
//!   determine alone.
//! - **Labels key the translators.** A field names the generator whose corolla
//!   it translates; generators sharing a corolla share its translator, written
//!   once under any one of their labels, and a second is refused as
//!   [`UaDefect::Tables`]. The alternatives were a record keyed by corolla,
//!   which the surface has no spelling for, and a list by position, which a
//!   reordered signature silently re-wires. Reversal: a surface spelling for
//!   corollas.
//! - **Each stratum is certified once per process.** Building the catalogue and
//!   certifying its stratum take about a millisecond at bound four and degree
//!   one, most of a decision, and depend on the bound and the degree alone; an
//!   editor re-decides every accepted statement on each keystroke. Both are
//!   held in statics, raced into place by `once_cell`'s `OnceBox`, the
//!   ecosystem's `no_std` single-assignment cell, with `alloc` its only
//!   feature. The alternatives were a cache per checking context, which an
//!   editor rebuilds on each keystroke, a cache the caller threads through the
//!   incremental checker, which every face would have to own, and a spinning
//!   `Once` from `spin`, whose initialiser has carried an unsoundness advisory
//!   where a race loser here only drops its copy. Reversal: a bound the checker
//!   no longer fixes in advance, or an advisory against `once_cell`.
//!
//! # References
//!
//! - Iosif Petrakis. "Univalent Typoids." 2022. `arXiv:2205.06651` — a
//!   univalence map as a typoid function, equivalent equivalences to equal
//!   identifications.
//! - Michael Hedberg. "A Coherence Theorem for Martin-Löf's Type Theory."
//!   _Journal of Functional Programming_ 8, 4 (1998), pages 413–436.
//!   `doi:10.1017/S0956796898003153` — decidable equality makes identity a
//!   proposition, why the target is not the ambient identity type.
//! - Michael Shulman. "Univalence for Inverse Diagrams and Homotopy
//!   Canonicity." _Mathematical Structures in Computer Science_ 25, 5 (2015).
//!   `doi:10.1017/S0960129514000565` — diagrams built degree by degree, each
//!   stage over its matching object: the telescope.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::ua::Description;
use gandr_core_term::ua::Sides;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_theory_sites::Bijection;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Defect;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Element;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::Equivalence;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Species;
use gandr_theory_sites::Table;
use gandr_theory_sites::Uncertified;
use once_cell::race::OnceBox;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;

#[cfg(test)]
mod tests;

/// The two translators an equivalence gives at one corolla.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Translators
{
    /// From the source species' code to the target's.
    pub forward: ValueId,
    /// From the target species' code to the source's.
    pub backward: ValueId,
}

/// Why an equivalence has no path at the stratum.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UaRefusal
{
    /// The tables the translators compute are no equivalence of the species
    /// at the stratum, or a translator stands at a corolla the species do not
    /// inhabit or none stands at one they do.
    Species(Defect),
    /// A translator does not return an element of its target code at an
    /// element of its source.
    Stuck
    {
        /// The corolla.
        corolla: ShapeIndex,
        /// The element the translator was applied to.
        element: ElementIndex,
    },
    /// Code univalence refused a corolla's translators.
    Code
    {
        /// The corolla.
        corolla: ShapeIndex,
        /// The judgement's refusal.
        refusal: CheckRefusal,
    },
}

/// An equivalence of species as a path of the certificate universe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Universal
{
    /// The native path.
    path: ValueId,
    /// `⌜Tel a⌝`, the quote the path starts at.
    source: ValueId,
    /// `⌜Tel b⌝`, the quote the path ends at.
    target: ValueId,
    /// `Path_U(⌜Tel a⌝, ⌜Tel b⌝)`.
    classifier: ValueTypeId,
    /// The equivalence of species the translators compute.
    equivalence: Equivalence,
    /// The translators of each inhabited corolla, in catalogue order.
    corollas: Vec<(ShapeIndex, Translators)>,
}

impl Universal
{
    /// The native path: reflexivity at the unit, then each corolla's universe
    /// certificate, then reflexivity at the unit for each degree from two to
    /// the stratum's, under native path products.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn path(&self) -> ValueId
    {
        self.path
    }

    /// The classifier `Path_U(⌜Telₙ a⌝, ⌜Telₙ b⌝)` the path is checked at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn classifier(&self) -> ValueTypeId
    {
        self.classifier
    }

    /// The identity the path inhabits at the universe, `Path(Type, ⌜Tel a⌝,
    /// ⌜Tel b⌝)`, as `equiv(f, g)` inhabits its own.
    ///
    /// # Specification
    /// - ensures: a path type over the value universe at level zero whose
    ///   endpoints are the two quotes the classifier relates.
    /// - panics: none.
    /// - executable: none — the minted node is checked by the judgement that
    ///   compares it against the type it is checked at.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written statement synthesises the identity at the
    ///   universe between the quotes of its two telescopes, the type element
    ///   transport reads its endpoints from.
    /// - witness: `ua::tests::a_written_statement_derives_the_path_at_its_stratum`
    #[inline]
    pub fn identity(
        &self,
        arena: &mut CoreArena,
    ) -> ValueTypeId
    {
        let universe = arena.value_type_universe(
            gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
            gandr_kernel_strata::Level::zero(),
        );
        arena.value_type_path(universe, self.source, self.target)
    }

    /// The equivalence of species the translators compute.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn equivalence(&self) -> &Equivalence
    {
        &self.equivalence
    }

    /// The translators of each inhabited corolla, in catalogue order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn corollas(&self) -> &[(ShapeIndex, Translators)]
    {
        &self.corollas
    }
}

/// The code of `species` at the corolla of `profile`: one unit summand per
/// element, in the stratum's enumeration order.
///
/// # Specification
/// - ensures: a sum with as many unit summands as the species has elements at
///   the profile; no summand at a profile the species does not inhabit, a sum
///   no universe path admits.
/// - panics: none.
/// - executable: none — the minted node is read by the judgement that checks
///   the path declared over it.
///
/// # Adequacy
/// - hypothesis: L3 — the binary corolla's code has two summands and the
///   constant's one, and the derived path is admitted at the telescope built
///   from them.
/// - witness: `ua::tests::the_swap_of_a_binary_generator_is_a_path_of_the_certificate_universe`
#[inline]
pub fn code(
    arena: &mut CoreArena,
    species: &Species,
    profile: Profile,
) -> ValueTypeId
{
    let unit = arena.value_type_unit();
    let summands: Vec<ValueTypeId> = species.elements(profile).iter().map(|_| unit).collect();
    arena.value_type_sum(&summands)
}

/// The canonical translator of `table`: a thunk of a λ casing on its argument
/// and returning, at the `i`-th summand, the injection of the unit at the
/// `i`-th image.
///
/// # Specification
/// - ensures: a closed thunk; applied to the `i`-th injection of the unit, it
///   returns the injection the table names for `i`.
/// - panics: none.
/// - executable: none — the minted program is read by evaluation, which the
///   derivation's witnesses run.
///
/// # Adequacy
/// - hypothesis: L3 — the swap's table evaluates back to itself and the derived
///   path is admitted with it as both translators.
/// - witness: `ua::tests::the_swap_of_a_binary_generator_is_a_path_of_the_certificate_universe`
#[inline]
pub fn tabulate(
    arena: &mut CoreArena,
    table: &Table,
) -> ValueId
{
    let unit = arena.value_unit();
    let branches: Vec<_> = table
        .images()
        .iter()
        .map(|&image| {
            let injected = arena.value_injection(usize::from(image).into(), unit);
            arena.computation_return(injected)
        })
        .collect();
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_case(argument, &branches);
    let lambda = arena.computation_lambda(case);
    arena.value_thunk(lambda)
}

/// The table `translator` computes from `from` elements into `to`.
///
/// # Specification
/// - requires: `translator` is closed and checked at the function type between
///   the two codes.
/// - ensures: entry `i` is the summand of the injection `translator` returns
///   when applied to the `i`-th injection of the unit.
/// - fails: [`UaRefusal::Stuck`] at the first element where evaluation is stuck
///   or returns anything but an injection below `to`; [`UaRefusal::Code`] with
///   the evaluation's own refusal.
/// - panics: none.
///
/// # Errors
/// - [`UaRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the swap reads back as its table, and a translator
///   returning a summand past its code is stuck at its first element.
/// - witness: `ua::tests::what_the_stratum_does_not_admit_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(ref table) => table.images().len() == from.len() && table.images().iter().all(|&image| usize::from(image) < to.len()),
    | Err(UaRefusal::Stuck { corolla: found, element }) => found == corolla && usize::from(element) < from.len(),
    | Err(UaRefusal::Code { corolla: found, .. }) => found == corolla,
    | Err(UaRefusal::Species(_)) => false,
})]
fn tabulated(
    context: &mut CheckingContext<'_>,
    corolla: ShapeIndex,
    translator: ValueId,
    (from, to): (&[Element], &[Element]),
) -> Result<Table, UaRefusal>
{
    let mut images = Vec::with_capacity(from.len());
    for element in 0 .. from.len() {
        let stuck = UaRefusal::Stuck {
            corolla,
            element: ElementIndex::from(element),
        };
        let arena = context.arena_mut();
        let unit = arena.value_unit();
        let input = arena.value_injection(element.into(), unit);
        let forced = arena.computation_force(translator);
        let applied = arena.computation_application(forced, input);
        let claim = arena.value_thunk(applied);
        let Maybe::Present(evaluation) = context
            .evaluate_claim(claim)
            .map_err(|refusal| UaRefusal::Code { corolla, refusal })?
        else {
            return Err(stuck);
        };
        match context.arena().value(evaluation.returned()) {
            | Some(&Value::Injection(summand, _)) if usize::from(summand) < to.len() => {
                images.push(ElementIndex::from(usize::from(summand)));
            },
            | _ => return Err(stuck),
        }
    }
    Ok(Table::new(images))
}

/// One part of the telescope: a corolla's two codes and its path, or a
/// degree's unit and its reflexivity.
#[derive(Clone, Copy, Debug)]
struct Stage
{
    /// The source code.
    source: ValueTypeId,
    /// The target code.
    target: ValueTypeId,
    /// The path between them.
    path: ValueId,
}

/// `ua_n` at a certified stratum: the path of the certificate universe the
/// equivalence `translators` give is.
///
/// # Specification
/// - requires: every translator is closed and checked at the function type
///   between its corolla's two [`code`]s.
/// - ensures: on success, the path's classifier is `Path_U(⌜Telₙ a⌝, ⌜Telₙ b⌝)`
///   over the degree telescope of the corollas the species inhabit, in
///   catalogue order, and one unit per degree from two to the stratum's `n`;
///   each corolla's component is the universe certificate over its two codes
///   with the given translators and the round-trip traces code univalence
///   recorded, and each unit's is reflexivity; and the translators' tables are
///   an equivalence of the species at the stratum.
/// - fails: [`UaRefusal::Species`] with [`Defect::Tables`] for translators at a
///   shape that is no corolla of the stratum; [`UaRefusal::Stuck`] for a
///   translator that does not compute an element; [`UaRefusal::Species`] with
///   [`Equivalence::check`]'s refusal for tables that are no equivalence of the
///   species, a missing translator among them; [`UaRefusal::Code`] with code
///   univalence's refusal for a corolla whose round trips do not convert.
/// - panics: none.
///
/// # Errors
/// - [`UaRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the swap of a binary generator beside a constant is
///   admitted by the kernel at its telescope, at degree one and at degree two
///   with its unit stage; equivalent translators give paths the kernel keeps
///   apart and identifies through the extensionality of each corolla's
///   translators; at degree two the swap is identified with its conjugate by
///   the input swap, the exchange of two binary generators computes its
///   conjugate's table and the crossed exchange does not; crossed generators, a
///   non-inverse pair, a stuck translator and a missing one are refused by
///   name, the crossed pair passing code univalence alone.
/// - witness: `ua::tests::the_swap_of_a_binary_generator_is_a_path_of_the_certificate_universe`
/// - witness: `ua::tests::the_swap_at_degree_two_is_a_path_over_its_segal_telescope`
/// - witness: `ua::tests::equivalent_equivalences_go_to_identified_paths`
/// - witness: `ua::tests::a_corolla_automorphism_acts_on_a_certificate_by_conjugation`
/// - witness: `ua::tests::what_the_stratum_does_not_admit_it_refuses_by_name`
#[inline]
#[spec(ensures: |ret| match ret {
    | Ok(ref universal) => universal.corollas.iter().all(|&(index, given)| translators.get(&index) == Some(&given))
        && universal.equivalence.components().keys().copied().eq(universal.corollas.iter().map(|&(index, _)| index)),
    | Err(_) => true,
})]
pub fn derive(
    context: &mut CheckingContext<'_>,
    stratum: &SegalStratum<'_>,
    sides: (&Species, &Species),
    translators: &BTreeMap<ShapeIndex, Translators>,
) -> Result<Universal, UaRefusal>
{
    for &shape in translators.keys() {
        if !stratum
            .corollas()
            .iter()
            .any(|corolla| corolla.index() == shape)
        {
            return Err(UaRefusal::Species(Defect::Tables { shape }));
        }
    }
    let mut tables = BTreeMap::new();
    for corolla in stratum.corollas() {
        let elements = (
            sides.0.elements(corolla.profile()),
            sides.1.elements(corolla.profile()),
        );
        let Some(given) = translators.get(&corolla.index())
        else {
            continue;
        };
        if elements.0.len() != elements.1.len() {
            continue;
        }
        let forward = tabulated(
            context,
            corolla.index(),
            given.forward,
            (&elements.0, &elements.1),
        )?;
        let backward = tabulated(
            context,
            corolla.index(),
            given.backward,
            (&elements.1, &elements.0),
        )?;
        tables.insert(corolla.index(), Bijection { forward, backward });
    }
    let equivalence = Equivalence::check(stratum, sides, tables).map_err(UaRefusal::Species)?;
    let mut corollas = Vec::new();
    let mut stages = Vec::new();
    for corolla in stratum.corollas() {
        let index = corolla.index();
        if !equivalence.components().contains_key(&index) {
            continue;
        }
        let Some(&given) = translators.get(&index)
        else {
            continue;
        };
        let source = code(context.arena_mut(), sides.0, corolla.profile());
        let target = code(context.arena_mut(), sides.1, corolla.profile());
        let decided = crate::equiv::decide(
            context,
            given.forward,
            (given.forward, given.backward),
            (source, target),
        )
        .map_err(|refusal| UaRefusal::Code {
            corolla: index,
            refusal,
        })?;
        let path = context.arena_mut().value_path_equiv(
            decided.classifier(),
            given.forward,
            given.backward,
            alloc::sync::Arc::clone(decided.evidence()),
        );
        corollas.push((index, given));
        stages.push(Stage {
            source,
            target,
            path,
        });
    }
    let arena = context.arena_mut();
    let unit = arena.value_type_unit();
    let quoted = arena.value_quote(unit);
    let reflexivity = arena.value_path_refl(quoted);
    let matched = Stage {
        source: unit,
        target: unit,
        path: reflexivity,
    };
    let above = usize::from(stratum.degree()).saturating_sub(1);
    stages.extend(core::iter::repeat_n(matched, above));
    let mut telescope = matched;
    if let Some((last, earlier)) = stages.split_last() {
        let mut rest = *last;
        for stage in earlier.iter().rev() {
            rest = Stage {
                source: arena.value_type_product(&[stage.source, rest.source]),
                target: arena.value_type_product(&[stage.target, rest.target]),
                path: arena.value_path_product(stage.path, rest.path),
            };
        }
        telescope = Stage {
            source: arena.value_type_product(&[unit, rest.source]),
            target: arena.value_type_product(&[unit, rest.target]),
            path: arena.value_path_product(reflexivity, rest.path),
        };
    }
    let source = arena.value_quote(telescope.source);
    let target = arena.value_quote(telescope.target);
    let classifier = arena.value_type_path_universe(source, target);
    Ok(Universal {
        path: telescope.path,
        source,
        target,
        classifier,
        equivalence,
        corollas,
    })
}

/// The largest catalogue bound a `ua` statement may name.
///
/// economy: the catalogue grows about threefold per size — 31 shapes at 4,
/// 81 at 5, 223 at 6 — and building it at 6 takes a third of a second
/// optimised; 5 reaches every corolla of up to four legs.
const ALLOWANCE: usize = 5;

/// The catalogue at each bound within the allowance, built on first use.
static CATALOGUES: [OnceBox<Catalogue>; ALLOWANCE + 1] = [const { OnceBox::new() }; ALLOWANCE + 1];

/// The stratum of each catalogue in [`CATALOGUES`] at each degree up to the
/// allowance, by bound then degree, certified on first use. No shape is of a
/// degree past its size, so a degree past the allowance is past every bound.
static STRATA: [[OnceBox<SegalStratum<'static>>; ALLOWANCE + 1]; ALLOWANCE + 1] =
    [const { [const { OnceBox::new() }; ALLOWANCE + 1] }; ALLOWANCE + 1];

/// The stratum of `degree` over the catalogue at `bound`, certified once per
/// process.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the stratum [`SegalStratum::certify`] gives at `degree` over
///   [`Catalogue::build`] at `bound`; every call at one bound and one degree
///   within the allowance answers the same stratum.
/// - fails: [`StratumDefect::Allowance`] for a bound past [`ALLOWANCE`] or a
///   catalogue that does not build; [`StratumDefect::Degree`] and
///   [`StratumDefect::Condition`] as [`SegalStratum::certify`] refuses.
/// - panics: none.
/// - intension: the first call at a bound builds its catalogue and the first at
///   a degree within the allowance certifies; a degree past it is certified
///   anew, and a refusal is not held, so a refused stratum is checked again.
///
/// # Errors
/// [`StratumDefect`] as above.
///
/// # Adequacy
/// - hypothesis: L3 — every written statement is decided over the stratum this
///   answers; a wrong bound or degree refuses or derives another path, and the
///   degree, condition and allowance refusals are each written in the corpus.
/// - witness: `ua::tests::a_written_statement_derives_the_path_at_its_stratum`
/// - witness: `ua::tests::a_written_statement_refuses_each_defect_by_name`
#[spec(ensures: |ref ret| match *ret {
    | Ok(ref stratum) => usize::from(bound) <= ALLOWANCE && stratum.degree() == degree,
    | Err(StratumDefect::Allowance { bound: refused }) => refused == bound,
    | Err(StratumDefect::Degree { degree: refused }) => refused == degree,
    | Err(StratumDefect::Condition { degree: failing }) => failing <= degree,
})]
fn certified(
    bound: ShapeSize,
    degree: Degree,
) -> Result<Cow<'static, SegalStratum<'static>>, StratumDefect>
{
    let Some(catalogue) = CATALOGUES.get(usize::from(bound))
    else {
        return Err(StratumDefect::Allowance { bound });
    };
    let catalogue = catalogue
        .get_or_try_init(|| Catalogue::build(bound).map(Box::new))
        .map_err(|_obstruction| StratumDefect::Allowance { bound })?;
    let certify = || {
        SegalStratum::certify(catalogue, degree).map_err(|refused| match refused {
            | Uncertified::Degree { degree: refused } => StratumDefect::Degree { degree: refused },
            | Uncertified::Condition {
                degree: failing, ..
            } => StratumDefect::Condition { degree: failing },
        })
    };
    match STRATA
        .get(usize::from(bound))
        .and_then(|row| row.get(usize::from(degree)))
    {
        | Some(held) => held
            .get_or_try_init(|| certify().map(Box::new))
            .map(Cow::Borrowed),
        | None => certify().map(Cow::Owned),
    }
}

/// Why the stratum a `ua` statement names is not certified.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StratumDefect
{
    /// The degree asked for is zero, or above every shape of the catalogue.
    Degree
    {
        /// The degree asked for.
        degree: Degree,
    },
    /// The catalogue's site fails a condition the stratum rests on: the
    /// corolla condition, or the Segal condition at a shape of degree two or
    /// more.
    Condition
    {
        /// The degree whose condition fails: one for the corolla condition,
        /// the failing shape's own for the Segal condition.
        degree: Degree,
    },
    /// The bound is past the largest catalogue the checker enumerates.
    Allowance
    {
        /// The bound asked for.
        bound: ShapeSize,
    },
}

/// Which way a translator record reads.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Way
{
    /// From the source description to the target.
    Forward,
    /// From the target description to the source.
    Backward,
}

/// Why a `ua` statement's translators are no equivalence of its species at
/// its stratum.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UaDefect
{
    /// A translator record is no record, or names a generator the description
    /// it reads from does not declare.
    UnknownGenerator
    {
        /// The record.
        way: Way,
    },
    /// A generator's corolla is larger than the catalogue's bound.
    PastTheBound
    {
        /// The generator's profile.
        profile: Profile,
    },
    /// The species have different numbers of elements at a corolla.
    Cardinality
    {
        /// The corolla.
        corolla: ShapeIndex,
    },
    /// A corolla's translators are missing on one side or given twice.
    Tables
    {
        /// The corolla.
        corolla: ShapeIndex,
    },
    /// The backward table does not return an element the forward one sends.
    NotInverse
    {
        /// The corolla.
        corolla: ShapeIndex,
        /// The element on the source side.
        element: ElementIndex,
    },
    /// The forward tables do not commute with an automorphism of a corolla.
    NotNatural
    {
        /// The corolla.
        corolla: ShapeIndex,
        /// The element on the source side.
        element: ElementIndex,
    },
    /// A translator does not return an element of its target code.
    Stuck
    {
        /// The corolla.
        corolla: ShapeIndex,
        /// The element it was applied to.
        element: ElementIndex,
    },
}

impl UaDefect
{
    /// The defect `defect` names, at the corollas and elements it names.
    ///
    /// # Specification
    /// - ensures: each defect maps to the variant of its own name with the
    ///   corolla, profile and element it carries; a naturality defect keeps the
    ///   corolla and the element and drops the map and the shape it reaches,
    ///   which name no node of the statement.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — crossed generators and a non-inverse pair are refused
    ///   under their own names at the binary corolla.
    /// - witness: `ua::tests::a_written_statement_refuses_each_defect_by_name`
    #[spec(ensures: |ret| !matches!(ret, Self::UnknownGenerator { .. } | Self::Stuck { .. }))]
    fn of(defect: &Defect) -> Self
    {
        match *defect {
            | Defect::PastTheBound { profile } => Self::PastTheBound { profile },
            | Defect::Cardinality { shape } => Self::Cardinality { corolla: shape },
            | Defect::Tables { shape } => Self::Tables { corolla: shape },
            | Defect::NotInverse { shape, element } => Self::NotInverse {
                corolla: shape,
                element,
            },
            | Defect::NotNatural {
                corolla, element, ..
            } => Self::NotNatural { corolla, element },
        }
    }
}

/// What a `ua` node holds: its stratum, its descriptions and its two
/// translator records.
#[derive(Debug)]
struct Statement
{
    /// The degree and the catalogue bound.
    stratum: Stratum,
    /// The two descriptions, shared with the node.
    sides: Arc<Sides>,
    /// The forward and the backward translator records.
    records: (ValueId, ValueId),
}

/// The parts of the `ua` node at `at`.
///
/// # Specification
/// - ensures: the parts of the `ua` at `at`, the descriptions shared.
/// - fails: a node that is no `ua`.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::DanglingNode`] for an id naming no value, and
/// [`CheckRefusal::MachineInvariant`] for a value that is no `ua`: the
/// judgement only asks this of a node it matched as one.
///
/// # Adequacy
/// - hypothesis: L3 — a written statement's parts are read as written by its
///   premises and its decision.
/// - witness: `ua::tests::a_written_statement_derives_the_path_at_its_stratum`
#[spec(ensures: |ret| ret.is_err() || matches!(arena.value(at), Some(Value::Ua { .. })))]
fn statement(
    arena: &CoreArena,
    at: ValueId,
) -> Result<Statement, CheckRefusal>
{
    match arena.value(at) {
        | Some(&Value::Ua {
            stratum,
            ref sides,
            forward,
            backward,
        }) => Ok(Statement {
            stratum,
            sides: Arc::clone(sides),
            records: (forward, backward),
        }),
        | Some(_) => Err(CheckRefusal::MachineInvariant),
        | None => Err(CheckRefusal::DanglingNode {
            node: crate::CoreNode::Term(crate::TermNode::Value(at)),
        }),
    }
}

/// Each translator `record` gives, with the profile of the generator its
/// label names in `description`, in label order.
///
/// # Specification
/// - ensures: one entry per field of the record, at the profile of the
///   generator of the field's label.
/// - fails: a record operand that is no record, or a label no generator of
///   `description` carries.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::UaInequivalent`] with [`UaDefect::UnknownGenerator`] at
/// `at`.
///
/// # Adequacy
/// - hypothesis: L3 — a misspelt generator is refused before any translator is
///   checked.
/// - witness: `ua::tests::a_written_statement_refuses_each_defect_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |labelled| matches!(arena.value(record), Some(Value::Record(fields)) if fields.len() == labelled.len())))]
fn labelled(
    arena: &CoreArena,
    at: ValueId,
    (way, record): (Way, ValueId),
    description: &Description,
) -> Result<Vec<(Profile, ValueId)>, CheckRefusal>
{
    let unknown = CheckRefusal::UaInequivalent {
        at,
        defect: UaDefect::UnknownGenerator { way },
    };
    let Some(value) = arena.value(record)
    else {
        return Err(unknown);
    };
    let Value::Record(ref fields) = *value
    else {
        return Err(unknown);
    };
    let mut labelled = Vec::with_capacity(fields.len());
    for (label, &translator) in fields {
        let Maybe::Present(generator) = description.generator(label)
        else {
            return Err(unknown);
        };
        labelled.push((generator.profile, translator));
    }
    Ok(labelled)
}

/// The premises of the `ua` at `at`: each of its two records, with the record
/// type it is checked against — one field per label it writes, at the
/// function type between the two [`code`]s of the corolla the label names —
/// the forward record first.
///
/// # Specification
/// - ensures: two premises, the forward record's then the backward one's; each
///   record type has one field per field of its record, a forward translator at
///   a generator of profile `P` at `U(⌜a(P)⌝ → F ⌜b(P)⌝)`, a backward one at
///   `U(⌜b(P)⌝ → F ⌜a(P)⌝)`, and a field naming no generator at the unknown
///   type, so the record is judged whole and [`decide`] refuses the label by
///   name once it is.
/// - provides: the record judged whole, through the one judgement every record
///   passes, so the record and each translator in it are judged where they were
///   written.
/// - fails: as [`labelled`] does, for a record that is no record.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::UaInequivalent`] with [`UaDefect::UnknownGenerator`] for a
/// record that is no record.
///
/// # Adequacy
/// - hypothesis: L3 — the swap and the constant's identity are checked at their
///   corollas' function types and a translator at the wrong code is refused as
///   a mismatch.
/// - witness: `ua::tests::a_written_statement_derives_the_path_at_its_stratum`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |premises| premises.len() == 2_usize))]
pub(crate) fn premises(
    context: &mut CheckingContext<'_>,
    at: ValueId,
) -> Result<Vec<(ValueId, ValueTypeId)>, CheckRefusal>
{
    let Statement {
        sides,
        records: (forward, backward),
        ..
    } = statement(context.arena(), at)?;
    let species = (sides.source.species(), sides.target.species());
    let ways = [
        (
            Way::Forward,
            forward,
            &sides.source,
            (&species.0, &species.1),
        ),
        (
            Way::Backward,
            backward,
            &sides.target,
            (&species.1, &species.0),
        ),
    ];
    let mut premises = Vec::with_capacity(2);
    for (way, record, description, (from, to)) in ways {
        let named: Vec<(FieldLabel, Option<Profile>)> = match context.arena().value(record) {
            | Some(&Value::Record(ref fields)) => fields
                .keys()
                .map(|label| {
                    let profile = match description.generator(label) {
                        | Maybe::Present(generator) => Some(generator.profile),
                        | Maybe::Absent(_) => None,
                    };
                    (label.clone(), profile)
                })
                .collect(),
            | _ => {
                let _refused = labelled(context.arena(), at, (way, record), description)?;
                Vec::new()
            },
        };
        let mut fields = BTreeMap::new();
        for (label, profile) in named {
            let expected = match profile {
                | Some(profile) => {
                    let source = code(context.arena_mut(), from, profile);
                    let target = code(context.arena_mut(), to, profile);
                    crate::equiv::translator(context, (source, target))
                },
                | None => context.arena_mut().value_type_unknown(),
            };
            let _prior = fields.insert(label, expected);
        }
        premises.push((record, context.arena_mut().value_type_record(fields)));
    }
    Ok(premises)
}

/// `ua[n, k](a, b, f, g)` decided: the stratum certified, each record read as
/// the translators of the corollas its labels name, and [`derive()`] run over
/// them.
///
/// # Specification
/// - requires: the statement's [`premises`] checked.
/// - ensures: the path [`derive()`] gives at the catalogue of the bound, the
///   stratum of the degree certified there, the two descriptions' species and
///   one pair of translators per corolla a label names.
/// - fails: a stratum that is not certified; translators that are no
///   equivalence of the species there; code univalence's own refusal.
/// - panics: none.
/// - intension: the stratum comes from [`certified`], certified once per bound,
///   degree and process and shared by every statement decided after.
///
/// # Errors
/// [`CheckRefusal::UaUncertified`] for a bound past the allowance, a degree
/// zero or above every shape of the catalogue and a site failing the corolla
/// or the Segal condition;
/// [`CheckRefusal::UaInequivalent`] for a record naming no generator, a
/// generator past the bound, a corolla given twice or on one side only,
/// tables that are not mutually inverse or not natural, a stuck translator
/// and species of different sizes; a refusal of [`crate::equiv::decide`] as
/// it raises it.
///
/// # Adequacy
/// - hypothesis: L3 — the swap of a binary generator beside a constant derives
///   the path the kernel admits; each defect of the stratum and of the
///   translators is refused under its own name.
/// - witness: `ua::tests::a_written_statement_derives_the_path_at_its_stratum`
/// - witness: `ua::tests::a_written_statement_refuses_each_defect_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::UaUncertified { at: site, .. } | CheckRefusal::UaInequivalent { at: site, .. }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub(crate) fn decide(
    context: &mut CheckingContext<'_>,
    at: ValueId,
) -> Result<Universal, CheckRefusal>
{
    let Statement {
        stratum,
        sides,
        records: (forward, backward),
    } = statement(context.arena(), at)?;
    let uncertified = |stratum| CheckRefusal::UaUncertified { at, stratum };
    let inequivalent = |defect| CheckRefusal::UaInequivalent { at, defect };
    let certified = certified(stratum.bound, stratum.degree).map_err(uncertified)?;
    let ways = [
        (Way::Forward, forward, &sides.source),
        (Way::Backward, backward, &sides.target),
    ];
    let mut given: BTreeMap<ShapeIndex, (Option<ValueId>, Option<ValueId>)> = BTreeMap::new();
    for (way, record, description) in ways {
        for (profile, translator) in labelled(context.arena(), at, (way, record), description)? {
            let corolla = match certified.corolla(profile) {
                | Maybe::Present(corolla) => corolla.index(),
                | Maybe::Absent(_) => return Err(inequivalent(UaDefect::PastTheBound { profile })),
            };
            let slot = given.entry(corolla).or_default();
            let held = match way {
                | Way::Forward => &mut slot.0,
                | Way::Backward => &mut slot.1,
            };
            if held.replace(translator).is_some() {
                return Err(inequivalent(UaDefect::Tables { corolla }));
            }
        }
    }
    let mut translators = BTreeMap::new();
    for (corolla, held) in given {
        let (Some(forward), Some(backward)) = held
        else {
            return Err(inequivalent(UaDefect::Tables { corolla }));
        };
        translators.insert(corolla, Translators { forward, backward });
    }
    let species = (sides.source.species(), sides.target.species());
    derive(context, &certified, (&species.0, &species.1), &translators).map_err(|refused| {
        match refused {
            | UaRefusal::Species(ref defect) => inequivalent(UaDefect::of(defect)),
            | UaRefusal::Stuck { corolla, element } => {
                inequivalent(UaDefect::Stuck { corolla, element })
            },
            | UaRefusal::Code { refusal, .. } => refusal,
        }
    })
}
