use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::CorollaStratum;
use gandr_theory_sites::Defect;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Species;
use gandr_theory_sites::Table;
use gandr_theory_sites::Uncertified;
use quenchant_shape::shape::Maybe;

use super::Translators;
use super::UaRefusal;
use super::Universal;
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
    stratum: &CorollaStratum<'_>,
    legs: Legs,
) -> ShapeIndex
{
    match stratum.corolla(profile(legs)) {
        | Maybe::Present(corolla) => corolla.index(),
        | Maybe::Absent(reason) => panic!("the corolla is within the bound: {reason:?}"),
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

/// `ua_n` of `translators` between `monoid` and itself.
///
/// # Specification
/// trivial.
fn universal(
    arena: &mut CoreArena,
    stratum: &CorollaStratum<'_>,
    species: (&Species, &Species),
    translators: &BTreeMap<ShapeIndex, Translators>,
) -> Result<Universal, UaRefusal>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
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
        CorollaStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
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
    stratum: &CorollaStratum<'_>,
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
        CorollaStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
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
    let operation = code(&mut arena, &monoid, profile(Legs(2, 1)));
    let returns = arena.comp_type_returner(operation);
    let arrow = arena.comp_type_arrow(operation, returns);
    let function = arena.value_type_thunk(arrow);
    let cell = |arena: &mut CoreArena, position: At| {
        let first = arena.value_constant(ConstantIndex::from(0_usize));
        let second = arena.value_constant(ConstantIndex::from(1_usize));
        let path = arena.value_type_path(function, first, second);
        let funext = arena.value_funext(first, second);
        declaration(position, path, funext)
    };
    let module = [
        declaration(At(0), function, swap),
        declaration(At(1), function, recased),
        declaration(At(2), left.classifier(), left.path()),
        declaration(At(3), right.classifier(), right.path()),
        cell(&mut arena, At(4)),
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
        cell(&mut arena, At(3)),
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

#[test]
fn what_the_stratum_does_not_admit_it_refuses_by_name()
{
    let catalogue = catalogue();
    assert!(
        matches!(
            CorollaStratum::certify(&catalogue, Degree::from(2)),
            Err(Uncertified::Degree { .. })
        ),
        "no stratum, so no ua_n, above the corollas"
    );
    let stratum =
        CorollaStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
    let (binary, constant) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 1)));
    let monoid = monoid();
    let two = Species::new(BTreeMap::from([(
        profile(Legs(2, 1)),
        GeneratorCount::from(2),
    )]));
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
