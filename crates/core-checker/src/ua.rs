//! `ua_n` at the corolla stratum, derived from code univalence.
//!
//! An equivalence of graphical species, given by its translators at each
//! corolla, is a path of the certificate universe between the two species'
//! degree telescopes, derived corolla by corolla.
//!
//! # The statement
//!
//! Fix a catalogue whose corolla stratum `gandr-theory-sites` certifies at
//! degree one. The quantifier range is every corolla of that catalogue; the
//! alphabet is the corollas' automorphisms. For two species `a` and `b` and an
//! equivalence `e : Equiv a b` given, at each corolla `C` the species inhabit,
//! by a pair of closed translators between the codes `⌜a(C)⌝` and `⌜b(C)⌝`,
//! [`derive()`] returns a value of `Path_U(⌜Tel a⌝, ⌜Tel b⌝)` whose every
//! component the kernel replays. A stratum the site does not certify has no
//! [`CorollaStratum`] to pass, so `ua_n` there is refused before it is asked:
//! [`gandr_theory_sites::Uncertified`] names the degree or the failing shape.
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
//! order. `⌜Tel a⌝` is `() × (⌜a(C₁)⌝ × (… × ⌜a(Cₖ)⌝))`, nested to the right as
//! the kernel's binary path product nests; one corolla gives `() × ⌜a(C₁)⌝`,
//! none gives `()`.
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
//! codes with the given translators, and the native path product over them.
//! Declared at its classifier and checked, it crosses the bridge as the
//! kernel's native path, and admission replays every corolla's round trips.
//!
//! # Obligations
//!
//! - **The corolla restriction.** `ua-desc : Terms a ≅ Terms b → a ≅ b` is not
//!   full faithfulness alone: an isomorphism of the free algebras is reflected
//!   to the generating species by restricting it to the corollas. That lemma is
//!   `gandr_theory_sites::restrict`, with its own witness; it is why an
//!   equivalence given at the corollas is the whole of `Equiv a b` at this
//!   stratum, and why [`derive()`] reads nothing past them.
//! - **The two-cell coherence.** A univalence map must be a typoid function
//!   (Petrakis): equivalent equivalences go to identified paths. Two
//!   equivalences whose translators agree pointwise give certificates the
//!   kernel's structural conversion keeps apart, so the identification is not
//!   conversion; it is the identity record of the two certificates at each
//!   corolla. Its translator fields are function extensionalities the judgement
//!   decides and the kernel replays as higher evaluations: that much is
//!   witnessed here, at the binary corolla. Its round-trip coherence fields
//!   relate two reflected round trips at a sum of units, where identity of
//!   elements is decidable; the kernel's record view of two certificates
//!   observes all four fields by replay, and its witness runs negation against
//!   a case-inlined triple negation at Bool, the binary corolla's code.
//!   Equivalent equivalences are related by those fields; distinct ones are
//!   refused at the first corolla whose translators differ at an element.
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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_sites::Bijection;
use gandr_theory_sites::CorollaStratum;
use gandr_theory_sites::Defect;
use gandr_theory_sites::Element;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::Equivalence;
use gandr_theory_sites::Profile;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::Species;
use gandr_theory_sites::Table;
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
    /// certificate, under native path products.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn path(&self) -> ValueId
    {
        self.path
    }

    /// The classifier `Path_U(⌜Tel a⌝, ⌜Tel b⌝)` the path is checked at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn classifier(&self) -> ValueTypeId
    {
        self.classifier
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

/// One corolla's part of the telescope: its two codes and its path.
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

/// `ua_n` at the corolla stratum: the path of the certificate universe the
/// equivalence `translators` give is.
///
/// # Specification
/// - requires: every translator is closed and checked at the function type
///   between its corolla's two [`code`]s.
/// - ensures: on success, the path's classifier is `Path_U(⌜Tel a⌝, ⌜Tel b⌝)`
///   over the degree telescope of the corollas the species inhabit, in
///   catalogue order; each corolla's component is the universe certificate over
///   its two codes with the given translators and the round-trip traces code
///   univalence recorded; and the translators' tables are an equivalence of the
///   species at the stratum.
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
///   admitted by the kernel at its telescope; equivalent translators give paths
///   the kernel keeps apart and identifies through the extensionality of each
///   corolla's translators; crossed generators, a non-inverse pair, a stuck
///   translator and a missing one are refused by name, the crossed pair passing
///   code univalence alone.
/// - witness: `ua::tests::the_swap_of_a_binary_generator_is_a_path_of_the_certificate_universe`
/// - witness: `ua::tests::equivalent_equivalences_go_to_identified_paths`
/// - witness: `ua::tests::what_the_stratum_does_not_admit_it_refuses_by_name`
#[inline]
#[spec(ensures: |ret| match ret {
    | Ok(ref universal) => universal.corollas.iter().all(|&(index, given)| translators.get(&index) == Some(&given))
        && universal.equivalence.components().keys().copied().eq(universal.corollas.iter().map(|&(index, _)| index)),
    | Err(_) => true,
})]
pub fn derive(
    context: &mut CheckingContext<'_>,
    stratum: &CorollaStratum<'_>,
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
    let mut telescope = Stage {
        source: unit,
        target: unit,
        path: reflexivity,
    };
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
        classifier,
        equivalence,
        corollas,
    })
}
