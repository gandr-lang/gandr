use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::ua::Description;
use gandr_core_term::ua::Generator;
use gandr_core_term::ua::Sides;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_theory_levitation::Name;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::ClassCount;
use gandr_theory_sites::Defect;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::Family;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::ShapeBudget;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Species;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Table;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::Unreplayed;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathStratum;
use quenchant_shape::shape::Maybe;

use super::StratumAt;
use super::StratumDefect;
use super::StratumLevel;
use super::StratumStore;
use super::Translators;
use super::UaDefect;
use super::UaRefusal;
use super::Universal;
use super::Way;
use super::code;
use super::derive;
use super::recalled;
use super::tabulate;
use crate::bridge::Outcome;
use crate::bridge::Readmission;
use crate::bridge::readmit;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;

/// A profile's legs: its inputs, then its outputs.
#[derive(Clone, Copy, Debug)]
struct Legs(usize, usize);

/// A translator's table: the image of each element, by position.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Images<'images>(&'images [usize]);

/// A declaration's position in its module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// Two constants of a module, by position.
#[derive(Clone, Copy, Debug)]
struct Constants(usize, usize);

/// Text a fixture spells: a field label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spelled<'text>(&'text str);

/// A statement's head `ua[degree, bound]`: its degree and its catalogue
/// bound.
#[derive(Clone, Copy, Debug)]
struct Head(usize, usize);

/// Whether a module came through whole.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admission
{
    /// Every declaration checked and the kernel admitted every one.
    Whole,
    /// The judgement or the kernel refused a declaration.
    Partial,
}

/// The profile of `inputs` input legs and `outputs` output legs.
///
/// # Specification
/// trivial.
fn profile(Legs(inputs, outputs): Legs) -> Profile
{
    Profile {
        inputs: PortCount::from(inputs),
        outputs: PortCount::from(outputs),
    }
}

/// A binary operation and a constant: `mul : 2 → 1` and `e : 0 → 1`.
///
/// # Specification
/// trivial.
fn monoid() -> Species
{
    Species::new(BTreeMap::from([
        (profile(Legs(2, 1)), GeneratorCount::from(1)),
        (profile(Legs(0, 1)), GeneratorCount::from(1)),
    ]))
}

/// Two binary generators and nothing else: at the binary corolla four
/// elements, generator by generator, each attached in order and then crossed.
///
/// # Specification
/// trivial.
fn two() -> Species
{
    Species::new(BTreeMap::from([(
        profile(Legs(2, 1)),
        GeneratorCount::from(2),
    )]))
}

/// The catalogue at size four: the binary corolla is its largest.
///
/// # Specification
/// trivial.
fn catalogue() -> Arc<Catalogue>
{
    Arc::new(Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds"))
}

/// The catalogue position of the corolla of `legs`.
///
/// # Specification
/// trivial.
fn corolla(
    stratum: &SegalStratum,
    legs: Legs,
) -> ShapeIndex
{
    match stratum.corolla(profile(legs)) {
        Maybe::Present(corolla) => corolla.index(),
        Maybe::Absent(reason) => panic!("the corolla is within the bound: {reason:?}"),
    }
}

/// The canonical translator of the table `images`.
///
/// # Specification
/// trivial.
fn table(
    arena: &mut CoreArena,
    Images(images): Images<'_>,
) -> ValueId
{
    tabulate(
        arena,
        &Table::new(images.iter().copied().map(ElementIndex::from).collect()),
    )
}

/// The swap of a sum of two units written a second way: each branch cases on
/// the argument again, so the program is not the swap's case table but agrees
/// with it at both injections.
///
/// # Specification
/// trivial.
fn recased_swap(arena: &mut CoreArena) -> ValueId
{
    let unit = arena.value_unit();
    let [first, second] = [0_usize, 1_usize].map(|summand| {
        let injected = arena.value_injection(summand.into(), unit);
        arena.computation_return(injected)
    });
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let again = arena.computation_case(argument, &[second, first]);
    let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_case(scrutinee, &[again, again]);
    let lambda = arena.computation_lambda(case);
    arena.value_thunk(lambda)
}

/// `automorphism ∘ translator ∘ automorphism` as one program over two
/// synthesising translators, a module's constants: a thunk of a λ that
/// applies `automorphism` to its argument, `translator` to the result, and
/// `automorphism` again, each step bound.
///
/// # Specification
/// trivial.
fn conjugated(
    arena: &mut CoreArena,
    automorphism: ValueId,
    translator: ValueId,
) -> ValueId
{
    let nearest = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let [first, second, third] = [automorphism, translator, automorphism].map(|program| {
        let forced = arena.computation_force(program);
        arena.computation_application(forced, nearest)
    });
    let inner = arena.computation_bind(second, third);
    let body = arena.computation_bind(first, inner);
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// The type of a translator at the corolla of `legs`: a thunk of a function
/// from `species`' code there to itself.
///
/// # Specification
/// trivial.
fn translator_type(
    arena: &mut CoreArena,
    species: &Species,
    legs: Legs,
) -> ValueTypeId
{
    let operation = code(arena, species, profile(legs));
    let returns = arena.comp_type_returner(operation);
    let arrow = arena.comp_type_arrow(operation, returns);
    arena.value_type_thunk(arrow)
}

/// The declaration at `position` of the extensionality between the module's
/// constants `first` and `second`, at their path type over `function`.
///
/// # Specification
/// trivial.
fn extensionality(
    arena: &mut CoreArena,
    function: ValueTypeId,
    Constants(first, second): Constants,
    position: At,
) -> Declaration
{
    let first = arena.value_constant(ConstantIndex::from(first));
    let second = arena.value_constant(ConstantIndex::from(second));
    let path = arena.value_type_path(function, first, second);
    let funext = arena.value_funext(first, second);
    declaration(position, path, funext)
}

/// The declaration at `position`, its origin the position itself.
///
/// # Specification
/// trivial.
fn declaration(
    At(position): At,
    declared: ValueTypeId,
    defined: ValueId,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        Maybe::Present(declared),
        Maybe::Present(defined),
        OriginToken::from(position),
    )
}

/// `module`, judged and offered to the kernel.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> (ModuleReport, Readmission)
{
    let report = {
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        check_module(&mut context, module)
    };
    let readmission = readmit(arena, &report);
    (report, readmission)
}

/// `ua_n` of `translators` between the two `species`.
///
/// # Specification
/// trivial.
fn universal(
    arena: &mut CoreArena,
    stratum: &SegalStratum,
    species: (&Species, &Species),
    translators: &BTreeMap<ShapeIndex, Translators>,
) -> Result<Universal, UaRefusal>
{
    universal_after(arena, &[], stratum, species, translators)
}

/// A context over `arena` that has checked `prelude`, every declaration
/// checking, so a later program may name its constants.
///
/// # Specification
/// trivial.
fn prepared<'arena>(
    arena: &'arena mut CoreArena,
    prelude: &[Declaration],
) -> CheckingContext<'arena>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, prelude);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the prelude checks: {report:?}"
    );
    context
}

/// `ua_n` of `translators` between the two `species`, in a context that has
/// checked `prelude`, so a translator may name its constants.
///
/// # Specification
/// trivial.
fn universal_after(
    arena: &mut CoreArena,
    prelude: &[Declaration],
    stratum: &SegalStratum,
    species: (&Species, &Species),
    translators: &BTreeMap<ShapeIndex, Translators>,
) -> Result<Universal, UaRefusal>
{
    let mut context = prepared(arena, prelude);
    derive(&mut context, stratum, species, translators)
}

/// Whether every declaration checked and the kernel admitted every one.
///
/// # Specification
/// trivial.
fn admission(
    report: &ModuleReport,
    readmission: &Readmission,
) -> Admission
{
    let checked = report
        .judged()
        .iter()
        .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. }));
    let defined = readmission
        .readmitted()
        .iter()
        .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. }));
    if checked && defined {
        Admission::Whole
    }
    else {
        Admission::Partial
    }
}

#[test]
fn the_swap_of_a_binary_generator_is_a_path_of_the_certificate_universe()
{
    let catalogue = catalogue();
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
    let (binary, constant) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 1)));
    let monoid = monoid();
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let translators = BTreeMap::from([
        (binary, Translators {
            forward: swap,
            backward: swap,
        }),
        (constant, Translators {
            forward: keep,
            backward: keep,
        }),
    ]);
    let universal = universal(&mut arena, &stratum, (&monoid, &monoid), &translators)
        .expect("the swap is a path");
    assert_eq!(
        universal
            .equivalence()
            .components()
            .get(&binary)
            .map(|bijection| bijection.forward.images().to_vec()),
        Some(Vec::from([ElementIndex::from(1), ElementIndex::from(0)])),
        "the translator's table is the swap"
    );
    assert_eq!(
        universal
            .corollas()
            .iter()
            .map(|&(shape, ref translators)| (shape, translators.forward, translators.backward))
            .collect::<Vec<_>>(),
        [(constant, keep, keep), (binary, swap, swap)],
        "each inhabited corolla keeps its translators, in catalogue order"
    );
    let Some(&Value::PathProduct(unit, rest)) = arena.value(universal.path())
    else {
        panic!("degree zero, then the corollas");
    };
    assert!(
        matches!(arena.value(unit), Some(&Value::PathRefl(_))),
        "the empty shape's unit"
    );
    let Some(&Value::PathProduct(first, second)) = arena.value(rest)
    else {
        panic!("the two corollas the monoid inhabits");
    };
    assert!(
        matches!(arena.value(first), Some(&Value::PathEquiv { forward, .. }) if forward == keep),
        "the constant's corolla comes first in catalogue order"
    );
    let Some(&Value::PathEquiv {
        forward,
        ref evidence,
        ..
    }) = arena.value(second)
    else {
        panic!("the binary corolla's certificate");
    };
    assert_eq!(forward, swap);
    assert_eq!(
        (evidence.source.len(), evidence.target.len()),
        (2, 2),
        "one round trip per element on each side"
    );
    let (report, readmission) = judged(&mut arena, &[declaration(
        At(0),
        universal.classifier(),
        universal.path(),
    )]);
    assert_eq!(
        admission(&report, &readmission),
        Admission::Whole,
        "the judgement checks the path at its classifier and the kernel replays every round trip: \
         {report:?} {:?}",
        readmission.readmitted()
    );
    let empty = Species::default();
    let nothing = universal_of_nothing(&mut arena, &stratum, &empty);
    assert!(
        matches!(arena.value(nothing.path()), Some(&Value::PathRefl(_))),
        "a species with no generators has the unit as its telescope"
    );
    let (report, readmission) = judged(&mut arena, &[declaration(
        At(0),
        nothing.classifier(),
        nothing.path(),
    )]);
    assert_eq!(
        admission(&report, &readmission),
        Admission::Whole,
        "{report:?}"
    );
}

/// `ua_n` between `species` and itself with no translators.
///
/// # Specification
/// trivial.
fn universal_of_nothing(
    arena: &mut CoreArena,
    stratum: &SegalStratum,
    species: &Species,
) -> Universal
{
    universal(arena, stratum, (species, species), &BTreeMap::new())
        .expect("the empty equivalence is a path")
}

#[test]
fn equivalent_equivalences_go_to_identified_paths()
{
    let catalogue = catalogue();
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
    let (binary, constant) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 1)));
    let monoid = monoid();
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let recased = recased_swap(&mut arena);
    let same = table(&mut arena, Images(&[0, 1]));
    let keep = table(&mut arena, Images(&[0]));
    let mut at_binary = |translator: ValueId| {
        let translators = BTreeMap::from([
            (binary, Translators {
                forward: translator,
                backward: translator,
            }),
            (constant, Translators {
                forward: keep,
                backward: keep,
            }),
        ]);
        universal(&mut arena, &stratum, (&monoid, &monoid), &translators)
            .expect("an involution is a path")
    };
    let [left, right, identity] = [swap, recased, same].map(&mut at_binary);
    assert_eq!(
        left.equivalence(),
        right.equivalence(),
        "the two programs compute one equivalence of species"
    );
    assert_eq!(
        equal_certificate_syntax(&arena, left.path(), right.path()),
        CertificateEquality::Different,
        "the certificates keep their programs, so structural conversion keeps them apart"
    );
    let function = translator_type(&mut arena, &monoid, Legs(2, 1));
    let module = [
        declaration(At(0), function, swap),
        declaration(At(1), function, recased),
        declaration(At(2), left.classifier(), left.path()),
        declaration(At(3), right.classifier(), right.path()),
        extensionality(&mut arena, function, Constants(0, 1), At(4)),
    ];
    let (report, readmission) = judged(&mut arena, &module);
    assert_eq!(
        admission(&report, &readmission),
        Admission::Whole,
        "both paths are admitted, and at the binary corolla the translators, declared at their \
         function type, relate pointwise, replayed as a higher evaluation; each is an \
         involution, so the one extensionality is both the forward and the backward field, and \
         the constant's translators are one program: {report:?} {:?}",
        readmission.readmitted()
    );
    let module = [
        declaration(At(0), function, swap),
        declaration(At(1), function, same),
        declaration(At(2), identity.classifier(), identity.path()),
        extensionality(&mut arena, function, Constants(0, 1), At(3)),
    ];
    let (report, _) = judged(&mut arena, &module);
    assert!(
        matches!(
            report.judged().get(3).map(Judged::verdict),
            Some(Verdict::Refused(CheckRefusal::PointwiseDistinct { .. }))
        ),
        "the swap and the identity are two equivalences, refused at the binary corolla: {report:?}"
    );
}

/// At degree two the swap's path is the degree-one path with degree two's
/// unit stage last, and the kernel replays it at its classifier; so does the
/// path at every degree the catalogue reaches.
#[test]
fn the_swap_at_degree_two_is_a_path_over_its_segal_telescope()
{
    let catalogue = catalogue();
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(2))
        .expect("degree two is certified");
    let (binary, constant) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 1)));
    let monoid = monoid();
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let translators = BTreeMap::from([
        (binary, Translators {
            forward: swap,
            backward: swap,
        }),
        (constant, Translators {
            forward: keep,
            backward: keep,
        }),
    ]);
    let derived = universal(&mut arena, &stratum, (&monoid, &monoid), &translators)
        .expect("the swap is a path at degree two");
    let Some(&Value::PathProduct(unit, rest)) = arena.value(derived.path())
    else {
        panic!("degree zero, then the rest");
    };
    assert!(
        matches!(arena.value(unit), Some(&Value::PathRefl(_))),
        "the empty shape's unit"
    );
    let Some(&Value::PathProduct(first, rest)) = arena.value(rest)
    else {
        panic!("the constant's corolla, then the rest");
    };
    assert!(
        matches!(arena.value(first), Some(&Value::PathEquiv { forward, .. }) if forward == keep),
        "the constant's certificate"
    );
    let Some(&Value::PathProduct(second, above)) = arena.value(rest)
    else {
        panic!("the binary corolla, then degree two");
    };
    assert!(
        matches!(arena.value(second), Some(&Value::PathEquiv { forward, .. }) if forward == swap),
        "the binary corolla's certificate"
    );
    assert!(
        matches!(arena.value(above), Some(&Value::PathRefl(_))),
        "degree two's unit stage carries reflexivity"
    );
    let (report, readmission) = judged(&mut arena, &[declaration(
        At(0),
        derived.classifier(),
        derived.path(),
    )]);
    assert_eq!(
        admission(&report, &readmission),
        Admission::Whole,
        "the judgement checks the path at its classifier and the kernel replays every round trip: \
         {report:?} {:?}",
        readmission.readmitted()
    );
    for degree in [3_usize, 4] {
        let higher = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(degree))
            .expect("every degree the catalogue reaches is certified");
        let path = universal(&mut arena, &higher, (&monoid, &monoid), &translators)
            .expect("the swap is a path at every certified degree");
        let (report, readmission) = judged(&mut arena, &[declaration(
            At(0),
            path.classifier(),
            path.path(),
        )]);
        assert_eq!(
            admission(&report, &readmission),
            Admission::Whole,
            "degree {degree}: {report:?}"
        );
    }
}

/// The pasting coherence at degree two. The input swap `σ` of the binary
/// corolla is a two-cell between its inclusion and the inclusion through `σ`;
/// it acts on a certificate by conjugating its translators, `σ ∘ t ∘ σ`, one
/// program over the module's constants. At the monoid's binary code the
/// swap's certificate and its conjugate are two certificates the kernel keeps
/// apart and identifies through the extensionality of their translators,
/// replayed as a higher evaluation. On two binary generators `σ` acts on the
/// four elements as `[1, 0, 3, 2]`: the exchange's conjugate computes the
/// exchange and is admitted as a certificate beside it, while the crossed
/// exchange, which the stratum refuses, computes another table under
/// conjugation. The extensionality at a code of four summands is past the
/// rule's binary sums, and refused by name.
#[test]
fn a_corolla_automorphism_acts_on_a_certificate_by_conjugation()
{
    let catalogue = catalogue();
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(2))
        .expect("degree two is certified");
    let (binary, constant) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 1)));
    let mut arena = CoreArena::new();
    let [automorphism, translator, second] =
        [0_usize, 1, 2].map(|position| arena.value_constant(ConstantIndex::from(position)));

    let monoid = monoid();
    let function = translator_type(&mut arena, &monoid, Legs(2, 1));
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let conjugate = conjugated(&mut arena, automorphism, translator);
    let prelude = [
        declaration(At(0), function, swap),
        declaration(At(1), function, swap),
        declaration(At(2), function, conjugate),
    ];
    let at_binary = |forward: ValueId| {
        BTreeMap::from([
            (binary, Translators {
                forward,
                backward: forward,
            }),
            (constant, Translators {
                forward: keep,
                backward: keep,
            }),
        ])
    };
    let [left, right] = [swap, conjugate].map(|forward| {
        universal_after(
            &mut arena,
            &prelude,
            &stratum,
            (&monoid, &monoid),
            &at_binary(forward),
        )
        .expect("the swap and its conjugate are paths")
    });
    assert_eq!(
        left.equivalence(),
        right.equivalence(),
        "conjugating by an automorphism fixes a natural equivalence's tables"
    );
    assert_eq!(
        equal_certificate_syntax(&arena, left.path(), right.path()),
        CertificateEquality::Different,
        "the conjugate is another program, so structural conversion keeps the certificates apart"
    );
    let mut module = prelude.to_vec();
    module.extend([
        declaration(At(3), left.classifier(), left.path()),
        declaration(At(4), right.classifier(), right.path()),
        extensionality(&mut arena, function, Constants(1, 2), At(5)),
    ]);
    let (report, readmission) = judged(&mut arena, &module);
    assert_eq!(
        admission(&report, &readmission),
        Admission::Whole,
        "both certificates are admitted at degree two, and the translator relates pointwise to \
         its conjugate, the naturality equation at the swap, replayed as a higher evaluation; \
         the unit stages are one reflexivity: {report:?} {:?}",
        readmission.readmitted()
    );

    let two = two();
    let elements = two.elements(profile(Legs(2, 1)));
    let action = [1_usize, 0, 3, 2];
    for (element, &image) in elements.iter().zip(&action) {
        let swapped = elements.get(image).expect("the action stays in the code");
        assert_eq!(
            swapped.generator(),
            element.generator(),
            "the swap keeps each element's generator"
        );
        assert!(
            swapped.inputs().iter().eq(element.inputs().iter().rev()),
            "the swap crosses each element's inputs"
        );
    }
    let function = translator_type(&mut arena, &two, Legs(2, 1));
    let swap = table(&mut arena, Images(&action));
    let exchange = table(&mut arena, Images(&[2, 3, 0, 1]));
    let crossed = table(&mut arena, Images(&[2, 1, 0, 3]));
    let [conjugate, recrossed] =
        [translator, second].map(|translator| conjugated(&mut arena, automorphism, translator));
    let prelude = [
        declaration(At(0), function, swap),
        declaration(At(1), function, exchange),
        declaration(At(2), function, crossed),
        declaration(At(3), function, conjugate),
        declaration(At(4), function, recrossed),
    ];
    let alone = |forward: ValueId| {
        BTreeMap::from([(binary, Translators {
            forward,
            backward: forward,
        })])
    };
    let [left, right] = [exchange, conjugate].map(|forward| {
        universal_after(
            &mut arena,
            &prelude,
            &stratum,
            (&two, &two),
            &alone(forward),
        )
        .expect("the exchange and its conjugate are paths")
    });
    assert_eq!(
        left.equivalence(),
        right.equivalence(),
        "the exchange commutes with the swap"
    );
    let mut module = prelude.to_vec();
    module.extend([
        declaration(At(5), left.classifier(), left.path()),
        declaration(At(6), right.classifier(), right.path()),
    ]);
    let (report, readmission) = judged(&mut arena, &module);
    assert_eq!(
        admission(&report, &readmission),
        Admission::Whole,
        "{report:?}"
    );
    assert!(
        matches!(
            universal(&mut arena, &stratum, (&two, &two), &alone(crossed)),
            Err(UaRefusal::Species(Defect::NotNatural { corolla, .. })) if corolla == binary
        ),
        "the crossed exchange is no equivalence at the stratum"
    );
    let tables = {
        let mut context = prepared(&mut arena, &prelude);
        [crossed, recrossed].map(|translator| {
            super::tabulated(&mut context, binary, translator, (&elements, &elements))
        })
    };
    let read = |images: &[usize]| {
        Ok(Table::new(
            images.iter().copied().map(ElementIndex::from).collect(),
        ))
    };
    assert_eq!(
        tables,
        [read(&[2, 1, 0, 3]), read(&[0, 3, 2, 1])],
        "the swap moves the crossed exchange"
    );
    let mut module = prelude.to_vec();
    module.push(extensionality(&mut arena, function, Constants(1, 3), At(5)));
    let (report, _) = judged(&mut arena, &module);
    assert!(
        matches!(
            report.judged().get(5).map(Judged::verdict),
            Some(Verdict::Refused(CheckRefusal::FunextUnsupported { .. }))
        ),
        "a code of four summands is past the extensionality rule's binary sums: {report:?}"
    );
}

#[test]
fn what_the_stratum_does_not_admit_it_refuses_by_name()
{
    let catalogue = catalogue();
    assert!(
        matches!(
            SegalStratum::certify(Arc::clone(&catalogue), Degree::from(5)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(5)
        ),
        "no stratum, so no ua_n, past every shape of the catalogue"
    );
    assert!(
        matches!(
            SegalStratum::certify(Arc::clone(&catalogue), Degree::from(0)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(0)
        ),
        "nor below the corollas"
    );
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
    let (binary, constant) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 1)));
    let monoid = monoid();
    let two = two();
    let mut arena = CoreArena::new();
    let crossed = table(&mut arena, Images(&[2, 1, 0, 3]));
    let crossing = BTreeMap::from([(binary, Translators {
        forward: crossed,
        backward: crossed,
    })]);
    assert!(
        matches!(
            universal(&mut arena, &stratum, (&two, &two), &crossing),
            Err(UaRefusal::Species(Defect::NotNatural { corolla, element, .. }))
                if corolla == binary && element == ElementIndex::from(0)
        ),
        "exchanging two generators at one attachment ignores the corolla's swap"
    );
    let four = code(&mut arena, &two, profile(Legs(2, 1)));
    let decided = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        crate::equiv::decide(&mut context, crossed, (crossed, crossed), (four, four))
    };
    assert!(
        decided.is_ok(),
        "the same translators pass code univalence alone: the refusal is the stratum's alphabet"
    );
    let swap = table(&mut arena, Images(&[1, 0]));
    let same = table(&mut arena, Images(&[0, 1]));
    let keep = table(&mut arena, Images(&[0]));
    let past = table(&mut arena, Images(&[5, 5]));
    let at_binary = |forward: ValueId, backward: ValueId| {
        BTreeMap::from([
            (binary, Translators { forward, backward }),
            (constant, Translators {
                forward: keep,
                backward: keep,
            }),
        ])
    };
    assert_eq!(
        universal(
            &mut arena,
            &stratum,
            (&monoid, &monoid),
            &at_binary(swap, same)
        ),
        Err(UaRefusal::Species(Defect::NotInverse {
            shape: binary,
            element: ElementIndex::from(0),
        }))
    );
    assert_eq!(
        universal(
            &mut arena,
            &stratum,
            (&monoid, &monoid),
            &at_binary(past, past)
        ),
        Err(UaRefusal::Stuck {
            corolla: binary,
            element: ElementIndex::from(0),
        })
    );
    let edge = table(&mut arena, Images(&[2, 2]));
    assert_eq!(
        universal(
            &mut arena,
            &stratum,
            (&monoid, &monoid),
            &at_binary(edge, edge)
        ),
        Err(UaRefusal::Stuck {
            corolla: binary,
            element: ElementIndex::from(0),
        }),
        "a summand at the code's length is already past it"
    );
    let alone = BTreeMap::from([(binary, Translators {
        forward: swap,
        backward: swap,
    })]);
    assert_eq!(
        universal(&mut arena, &stratum, (&monoid, &monoid), &alone),
        Err(UaRefusal::Species(Defect::Tables { shape: constant })),
        "the constant's corolla is inhabited and has no translators"
    );
    let stray = BTreeMap::from([(ShapeIndex::from(0), Translators {
        forward: keep,
        backward: keep,
    })]);
    assert_eq!(
        universal(&mut arena, &stratum, (&monoid, &monoid), &stray),
        Err(UaRefusal::Species(Defect::Tables {
            shape: ShapeIndex::from(0)
        })),
        "the empty shape is no corolla"
    );
}

/// The magma's description: `mul : 2 → 1`, then `one : 0 → 1`.
///
/// # Specification
/// trivial.
fn magma() -> Description
{
    Description {
        name: Name::from("Magma"),
        generators: Box::from([
            Generator {
                label: label(Spelled("mul")),
                profile: profile(Legs(2, 1)),
            },
            Generator {
                label: label(Spelled("one")),
                profile: profile(Legs(0, 1)),
            },
        ]),
    }
}

/// The field label `text` spells.
///
/// # Specification
/// trivial.
fn label(Spelled(text): Spelled<'_>) -> FieldLabel
{
    FieldLabel::from(String::from(text))
}

/// The written statement `ua[degree, bound](Magma, Magma, forward,
/// backward)`, each record keyed by the labels beside its translators.
///
/// # Specification
/// trivial.
fn written(
    arena: &mut CoreArena,
    Head(degree, bound): Head,
    forward: &[(Spelled<'_>, ValueId)],
    backward: &[(Spelled<'_>, ValueId)],
) -> ValueId
{
    let [forward, backward] = [forward, backward].map(|fields| {
        arena.value_record(
            fields
                .iter()
                .map(|&(text, translator)| (label(text), translator))
                .collect(),
        )
    });
    arena.value_ua(
        Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        Arc::new(Sides {
            source: magma(),
            target: magma(),
        }),
        forward,
        backward,
    )
}

#[test]
fn a_written_statement_derives_the_path_at_its_stratum()
{
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let fields = [(Spelled("mul"), swap), (Spelled("one"), keep)];
    let statement = written(&mut arena, Head(1, 4), &fields, &fields);
    let unsigned = Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Absent(crate::declaration::signature::Absent::Unsigned),
        Maybe::Present(statement),
        OriginToken::from(0_usize),
    );
    let (report, readmission) = judged(&mut arena, &[unsigned]);
    let [ref judged] = *report.judged()
    else {
        panic!("one declaration, one verdict");
    };
    let Verdict::Synthesised { synthesised, .. } = judged.verdict()
    else {
        panic!("the statement synthesises its type: {report:?}");
    };
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = arena.value_type(synthesised.produced().id())
    else {
        panic!("the statement inhabits an identity");
    };
    assert!(
        matches!(arena.value_type(carrier), Some(&ValueType::Universe { .. })),
        "the identity is at the universe, as `equiv`'s is"
    );
    assert!(
        matches!(arena.value(left), Some(&Value::Quote(_)))
            && matches!(arena.value(right), Some(&Value::Quote(_))),
        "between the quotes of the two telescopes"
    );
    let Some(&path) = report.natives().get(&statement)
    else {
        panic!("the checker records the derived path");
    };
    let Some(&Value::PathProduct(unit, rest)) = arena.value(path)
    else {
        panic!("degree zero, then the corollas");
    };
    assert!(matches!(arena.value(unit), Some(&Value::PathRefl(_))));
    assert!(
        matches!(
            arena.value(rest),
            Some(&Value::PathProduct(constant, binary))
                if matches!(arena.value(constant), Some(&Value::PathEquiv { forward, .. }) if forward == keep)
                    && matches!(arena.value(binary), Some(&Value::PathEquiv { forward, .. }) if forward == swap)
        ),
        "each corolla's certificate carries the translator its label names"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the bridge erases the statement to its derived path and the kernel admits it: {:?}",
        readmission.readmitted()
    );
}

/// Bound six, past the five a fixed allowance once held, at degree six: its
/// 223 classes are within the stratum budget, so the statement derives its
/// path and the kernel admits it.
#[test]
fn a_statement_past_bound_five_derives_its_path()
{
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let fields = [(Spelled("mul"), swap), (Spelled("one"), keep)];
    let statement = written(&mut arena, Head(6, 6), &fields, &fields);
    let unsigned = Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Absent(crate::declaration::signature::Absent::Unsigned),
        Maybe::Present(statement),
        OriginToken::from(0_usize),
    );
    let (report, readmission) = judged(&mut arena, &[unsigned]);
    assert!(
        matches!(
            report.judged().first().map(Judged::verdict),
            Some(Verdict::Synthesised { .. })
        ),
        "the statement at bound six synthesises its type: {report:?}"
    );
    assert!(
        report.natives().contains_key(&statement),
        "the checker records the derived path"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel admits it: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn a_statement_stands_in_a_product_as_its_derived_path()
{
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let fields = [(Spelled("mul"), swap), (Spelled("one"), keep)];
    let statement = written(&mut arena, Head(1, 4), &fields, &fields);
    let unit = arena.value_type_unit();
    let unit_code = arena.value_quote(unit);
    let here = arena.value_here(unit_code);
    let product = arena.value_path_product(statement, here);
    let unsigned = Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Absent(crate::declaration::signature::Absent::Unsigned),
        Maybe::Present(product),
        OriginToken::from(0_usize),
    );
    let (report, readmission) = judged(&mut arena, &[unsigned]);
    assert!(
        matches!(report.judged()[0].verdict(), Verdict::Synthesised { .. }),
        "a product of a statement and reflexivity synthesises its identity: {report:?}"
    );
    let (Some(&derived), Some(&native)) = (
        report.natives().get(&statement),
        report.natives().get(&product),
    )
    else {
        panic!("the statement and the product each record their native path");
    };
    assert!(
        matches!(arena.value(native), Some(&Value::PathProduct(first, _)) if first == derived),
        "the statement's certificate in the product is the path derived for it"
    );
    assert!(
        matches!(
            readmission.readmitted()[0].outcome(),
            Outcome::Defined { .. }
        ),
        "and the kernel admits the product: {:?}",
        readmission.readmitted()[0].outcome()
    );
}

#[test]
fn a_written_statement_refuses_each_defect_by_name()
{
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let same = table(&mut arena, Images(&[0, 1]));
    let keep = table(&mut arena, Images(&[0]));
    let fields = [(Spelled("mul"), swap), (Spelled("one"), keep)];
    let refusal = |arena: &mut CoreArena, statement: ValueId| {
        let unsigned = Declaration::new(
            ConstantIndex::from(0_usize),
            Maybe::Absent(crate::declaration::signature::Absent::Unsigned),
            Maybe::Present(statement),
            OriginToken::from(0_usize),
        );
        let (report, _readmission) = judged(arena, &[unsigned]);
        match report.judged().first().map(Judged::verdict) {
            Some(Verdict::Refused(refusal)) => refusal,
            other => panic!("the statement is refused: {other:?}"),
        }
    };
    let cases = [
        (
            written(&mut arena, Head(5, 4), &fields, &fields),
            "a degree above every shape of the catalogue",
        ),
        (
            written(&mut arena, Head(1, 0), &fields, &fields),
            "a catalogue whose site fails the corolla condition",
        ),
        (
            written(&mut arena, Head(1, 65), &fields, &fields),
            "a bound past the largest a catalogue builds at",
        ),
        (
            written(&mut arena, Head(1, 8), &fields, &fields),
            "a catalogue past the stratum budget",
        ),
        (
            written(&mut arena, Head(1, 3), &fields, &fields),
            "a binary corolla past the bound",
        ),
        (
            written(
                &mut arena,
                Head(1, 4),
                &[(Spelled("mul"), swap), (Spelled("unit"), keep)],
                &fields,
            ),
            "a label the description does not declare",
        ),
        (
            written(&mut arena, Head(1, 4), &[(Spelled("mul"), swap)], &fields),
            "a corolla with no forward translator",
        ),
        (
            written(&mut arena, Head(1, 4), &fields, &[
                (Spelled("mul"), same),
                (Spelled("one"), keep),
            ]),
            "a backward table that is not the forward one's inverse",
        ),
    ];
    let refusals = cases.map(|(statement, case)| (refusal(&mut arena, statement), case));
    let expected = [
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaUncertified {
                stratum: StratumDefect::Degree { degree },
                ..
            } if degree == Degree::from(5))
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaUncertified {
                stratum: StratumDefect::Condition { degree },
                ..
            } if degree == Degree::from(1))
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaUncertified {
                stratum: StratumDefect::Allowance { bound },
                ..
            } if bound == ShapeSize::from(65))
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaUncertified {
                stratum: StratumDefect::Budget { bound, counted },
                ..
            } if bound == ShapeSize::from(8) && counted == ClassCount::from(1001))
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaInequivalent {
                defect: UaDefect::PastTheBound { profile: found },
                ..
            } if found == profile(Legs(2, 1)))
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaInequivalent {
                defect: UaDefect::UnknownGenerator { way: Way::Forward },
                ..
            })
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaInequivalent {
                defect: UaDefect::Tables { .. },
                ..
            })
        },
        |refusal: CheckRefusal| {
            matches!(refusal, CheckRefusal::UaInequivalent {
                defect: UaDefect::NotInverse { element, .. },
                ..
            } if element == ElementIndex::from(0))
        },
    ];
    for ((refusal, case), expected) in refusals.into_iter().zip(expected) {
        assert!(expected(refusal), "{case}: {refusal:?}");
    }
}

/// What a test store was handed: the strata kept, the refusals heard as
/// expected, and the others.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Counts
{
    /// The strata handed to keep.
    kept: usize,
    /// The refusals heard as expected.
    refused: usize,
    /// The refusals heard otherwise.
    other: usize,
}

/// A store answering one image, or none, at every stratum, counting the
/// strata it is handed to keep and the refusals it hears, as expected or not.
#[derive(Debug)]
struct Answering
{
    /// The image answered.
    image: Maybe<StratumImage, recalled::Absent>,
    /// The refusal the store expects to hear.
    expected: Unreplayed,
    /// The strata handed to keep.
    kept: AtomicUsize,
    /// The refusals heard as expected.
    refused: AtomicUsize,
    /// The refusals heard otherwise.
    other: AtomicUsize,
}

impl Answering
{
    /// The store answering `image`, expecting `expected` when it refuses.
    ///
    /// # Specification
    /// trivial.
    fn new(
        image: Maybe<StratumImage, recalled::Absent>,
        expected: Unreplayed,
    ) -> Arc<Self>
    {
        Arc::new(Self {
            image,
            expected,
            kept: AtomicUsize::new(0),
            refused: AtomicUsize::new(0),
            other: AtomicUsize::new(0),
        })
    }

    /// The strata kept, the expected refusals and the others.
    ///
    /// # Specification
    /// trivial.
    fn counts(&self) -> Counts
    {
        Counts {
            kept: self.kept.load(Ordering::Relaxed),
            refused: self.refused.load(Ordering::Relaxed),
            other: self.other.load(Ordering::Relaxed),
        }
    }
}

impl StratumStore for Answering
{
    /// The image the store answers.
    ///
    /// # Specification
    /// trivial.
    fn recall(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
    ) -> Maybe<StratumImage, recalled::Absent>
    {
        self.image.clone()
    }

    /// Count one stratum kept.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
        _image: &StratumImage,
    )
    {
        let _before = self.kept.fetch_add(1, Ordering::Relaxed);
    }

    /// Count one refusal, as expected or not.
    ///
    /// # Specification
    /// trivial.
    fn refuse(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
        why: Unreplayed,
    )
    {
        let count = if why == self.expected {
            &self.refused
        }
        else {
            &self.other
        };
        let _before = count.fetch_add(1, Ordering::Relaxed);
    }
}

/// #4034: two statements at one stratum, checked in one context handed a
/// store. A store holding nothing is handed the stratum once, which the
/// context then holds. A store holding its image replays it and is handed
/// nothing to keep, so no certification ran. A store holding a damaged image
/// hears it refused as malformed, and is handed the stratum certified afresh.
/// Each statement derives its path under every store.
#[test]
fn a_stored_stratum_replays_and_a_damaged_one_is_certified_afresh_4034()
{
    let sub_site = Catalogue::profiles(ShapeSize::from(4), magma_profiles(), ShapeBudget::EVERY)
        .expect("the magma's sub-site builds");
    let image = SegalStratum::certify(Arc::new(sub_site), Degree::from(2))
        .expect("degree two is certified")
        .image();
    let mut damaged = Vec::from(image.clone());
    let _last = damaged.pop();
    let stores = [
        (
            Answering::new(
                Maybe::Absent(recalled::Absent::Unkept),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 0,
                other: 0,
            },
            "a store holding nothing keeps the stratum once",
        ),
        (
            Answering::new(Maybe::Present(image), Unreplayed::Malformed),
            Counts {
                kept: 0,
                refused: 0,
                other: 0,
            },
            "a stored image replays, and nothing is certified",
        ),
        (
            Answering::new(
                Maybe::Present(StratumImage::from(damaged)),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 1,
                other: 0,
            },
            "a damaged image is refused by name and certified afresh",
        ),
    ];
    for (store, counts, case) in stores {
        let mut arena = CoreArena::new();
        let swap = table(&mut arena, Images(&[1, 0]));
        let keep = table(&mut arena, Images(&[0]));
        let fields = [(Spelled("mul"), swap), (Spelled("one"), keep)];
        let module = [0_usize, 1].map(|position| {
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Absent(crate::declaration::signature::Absent::Unsigned),
                Maybe::Present(written(&mut arena, Head(2, 4), &fields, &fields)),
                OriginToken::from(position),
            )
        });
        let report = {
            let shared: Arc<dyn StratumStore> = Arc::<Answering>::clone(&store);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.keep_strata_in(shared);
            check_module(&mut context, &module)
        };
        assert!(
            report
                .judged()
                .iter()
                .all(|judged| matches!(judged.verdict(), Verdict::Synthesised { .. })),
            "{case}: each statement derives its path: {report:?}"
        );
        assert_eq!(store.counts(), counts, "{case}");
    }
}

/// #4123: level two over the chains at total size nine and degree four,
/// asked for twice of one context handed a store. A store holding nothing is
/// handed level two once, and never level one's chain stratum. A store
/// holding its image replays it and is handed nothing to keep. A store
/// holding a damaged image hears it refused as malformed, and is handed level
/// two certified afresh. A degree past every object is refused by the degree.
#[test]
fn level_two_is_kept_recalled_and_refused_by_the_store_4123()
{
    let at = StratumAt {
        bound: ShapeSize::from(9),
        degree: Degree::from(4),
    };
    let chains = Arc::new(Catalogue::chains(at.bound).expect("the chains build"));
    let below = SegalStratum::certify(Arc::clone(&chains), chains.reach())
        .expect("level one is certified at the chains' reach");
    let level: &Catalogue = &chains;
    let wreath = Arc::new(Wreath::build(level, level, at.bound));
    let image = WreathStratum::certify(wreath, at.degree, below)
        .expect("level two is certified at degree four")
        .image();
    let mut damaged = Vec::from(image.clone());
    let _last = damaged.pop();
    let stores = [
        (
            Answering::new(
                Maybe::Absent(recalled::Absent::Unkept),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 0,
                other: 0,
            },
            "a store holding nothing keeps level two once",
        ),
        (
            Answering::new(Maybe::Present(image.clone()), Unreplayed::Malformed),
            Counts {
                kept: 0,
                refused: 0,
                other: 0,
            },
            "a stored image replays, and nothing is certified",
        ),
        (
            Answering::new(
                Maybe::Present(StratumImage::from(damaged)),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 1,
                other: 0,
            },
            "a damaged image is refused by name and certified afresh",
        ),
    ];
    for (store, counts, case) in stores {
        let mut arena = CoreArena::new();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_strata_in(Arc::<Answering>::clone(&store));
        for _asked in 0_usize .. 2_usize {
            let stratum = context.level_two(at).expect("level two is answered");
            assert_eq!(stratum.image(), image, "{case}: level two's own image");
        }
        assert_eq!(store.counts(), counts, "{case}");
    }
    let past = Degree::from(100);
    let mut arena = CoreArena::new();
    assert!(
        matches!(
            CheckingContext::new(&mut arena, CheckBudget::DEFAULT)
                .level_two(StratumAt { degree: past, ..at }),
            Err(StratumDefect::Degree { degree }) if degree == past
        ),
        "a degree past every object"
    );
}

/// The profiles of the magma's corollas: its binary operation and its
/// constant.
///
/// # Specification
/// trivial.
fn magma_profiles() -> BTreeSet<Profile>
{
    BTreeSet::from([profile(Legs(2, 1)), profile(Legs(0, 1))])
}

/// #4035: a statement's sub-site, the shapes whose every vertex is a corolla
/// its species inhabit, derives the path the whole catalogue gives. The swap
/// of a binary generator beside a constant at degrees one, two and four, and
/// the exchange of two binary generators, give equal certificates over both;
/// the crossed exchange is refused as not natural over both. The written
/// statement at bound seven and degree seven derives its path over the
/// magma's eleven classes, and the kernel admits it.
#[test]
fn a_statement_derives_over_its_sub_site_the_path_the_wirings_give_4035()
{
    let mut arena = CoreArena::new();
    let swap = table(&mut arena, Images(&[1, 0]));
    let keep = table(&mut arena, Images(&[0]));
    let exchange = table(&mut arena, Images(&[2, 3, 0, 1]));
    let crossed = table(&mut arena, Images(&[2, 1, 0, 3]));
    let monoid = monoid();
    let two = two();
    let magma: &[(Legs, ValueId)] = &[(Legs(2, 1), swap), (Legs(0, 1), keep)];
    let cases = [
        (&monoid, magma, Head(1, 4), "the swap at degree one"),
        (&monoid, magma, Head(2, 4), "the swap at degree two"),
        (&monoid, magma, Head(4, 5), "the swap at degree four"),
        (
            &two,
            &[(Legs(2, 1), exchange)][..],
            Head(1, 4),
            "the exchange",
        ),
        (
            &two,
            &[(Legs(2, 1), crossed)][..],
            Head(1, 4),
            "the crossed exchange",
        ),
    ];
    for (species, given, Head(degree, bound), case) in cases {
        let profiles: BTreeSet<Profile> = species.profiles().map(|(held, _count)| held).collect();
        let answers = [
            Catalogue::build(ShapeSize::from(bound)),
            Catalogue::profiles(ShapeSize::from(bound), profiles, ShapeBudget::EVERY),
        ]
        .map(|built| {
            let catalogue = Arc::new(built.expect("the catalogue builds"));
            let stratum = SegalStratum::certify(catalogue, Degree::from(degree))
                .expect("the stratum is certified");
            let translators = given
                .iter()
                .map(|&(legs, translator)| {
                    (corolla(&stratum, legs), Translators {
                        forward: translator,
                        backward: translator,
                    })
                })
                .collect();
            universal(&mut arena, &stratum, (species, species), &translators)
        });
        match answers {
            [Ok(ref whole), Ok(ref sub)] => assert_eq!(
                equal_certificate_syntax(&arena, whole.path(), sub.path()),
                CertificateEquality::Equal,
                "{case}: the sub-site derives the whole catalogue's path"
            ),
            [
                Err(UaRefusal::Species(Defect::NotNatural { .. })),
                Err(UaRefusal::Species(Defect::NotNatural { .. })),
            ] => assert_eq!(
                case, "the crossed exchange",
                "only the crossed exchange is refused"
            ),
            ref other => panic!("{case}: both catalogues answer alike: {other:?}"),
        }
    }
    let fields = [(Spelled("mul"), swap), (Spelled("one"), keep)];
    let statement = written(&mut arena, Head(7, 7), &fields, &fields);
    let unsigned = Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Absent(crate::declaration::signature::Absent::Unsigned),
        Maybe::Present(statement),
        OriginToken::from(0_usize),
    );
    let (report, readmission) = judged(&mut arena, &[unsigned]);
    assert!(
        report.natives().contains_key(&statement),
        "the statement at bound seven derives its path: {report:?}"
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel admits it: {:?}",
        readmission.readmitted()
    );
}
