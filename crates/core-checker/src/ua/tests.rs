use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

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
use gandr_theory_sites::Defect;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Species;
use gandr_theory_sites::Table;
use gandr_theory_sites::Uncertified;
use quenchant_shape::shape::Maybe;

use super::StratumDefect;
use super::Translators;
use super::UaDefect;
use super::UaRefusal;
use super::Universal;
use super::Way;
use super::code;
use super::derive;
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
fn catalogue() -> Catalogue
{
    Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds")
}

/// The catalogue position of the corolla of `legs`.
///
/// # Specification
/// trivial.
fn corolla(
    stratum: &SegalStratum<'_>,
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
    stratum: &SegalStratum<'_>,
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
    stratum: &SegalStratum<'_>,
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
    let stratum =
        SegalStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
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
    stratum: &SegalStratum<'_>,
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
    let stratum =
        SegalStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
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
    let stratum =
        SegalStratum::certify(&catalogue, Degree::from(2)).expect("degree two is certified");
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
        let higher = SegalStratum::certify(&catalogue, Degree::from(degree))
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
    let stratum =
        SegalStratum::certify(&catalogue, Degree::from(2)).expect("degree two is certified");
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
        let crossed: Vec<_> = element.inputs().iter().rev().copied().collect();
        assert_eq!(
            (swapped.generator(), swapped.inputs()),
            (element.generator(), crossed.as_slice()),
            "the swap crosses each element's inputs and keeps its generator"
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
            SegalStratum::certify(&catalogue, Degree::from(5)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(5)
        ),
        "no stratum, so no ua_n, past every shape of the catalogue"
    );
    assert!(
        matches!(
            SegalStratum::certify(&catalogue, Degree::from(0)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(0)
        ),
        "nor below the corollas"
    );
    let stratum =
        SegalStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
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
            written(&mut arena, Head(1, 6), &fields, &fields),
            "a catalogue past the allowance",
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
            } if bound == ShapeSize::from(6))
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
