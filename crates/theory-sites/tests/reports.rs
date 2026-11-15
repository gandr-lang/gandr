//! What a condition's report writes: a map in its documented notation, a
//! case and a chain of cases, the verdict with its case count, and each
//! defect named with the maps it carries.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Leg;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::WiringObstruction;
use gandr_theory_sites::Chain;
use gandr_theory_sites::ClassCount;
use gandr_theory_sites::FactorizationDefect;
use gandr_theory_sites::FactorizationFailure;
use gandr_theory_sites::MapCase;
use gandr_theory_sites::MapObstruction;
use gandr_theory_sites::Outcome;
use gandr_theory_sites::SegalDefect;
use gandr_theory_sites::SegalFailure;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::Verdict;
use quenchant_shape::shape::Maybe;

/// A map writes its vertex images, then its wire images, each list in
/// position order; a case writes its source and target around the map, a
/// chain its cases in order between ` ; `, and an outcome its verdict with
/// the count of cases it examined and, when it failed, the counter-example,
/// which it also hands back.
#[test]
fn a_report_writes_its_maps_cases_and_verdict_in_order()
{
    let first = site_map!([{ 0 }, {}], [0, 1]);
    let second = site_map!([{1, 0}], []);
    assert_eq!(first.to_string(), "S={0},{} φ=0,1");
    assert_eq!(second.to_string(), "S={0,1} φ=");
    let earlier = MapCase::new(shape!(1; o > 0), shape!(2; o > 0, 0 > 1), first);
    let later = MapCase::new(shape!(1), shape!(0), second);
    assert_eq!(
        earlier.to_string(),
        "[1v; ·→0] → [2v; ·→0, 0→1] by S={0},{} φ=0,1"
    );
    assert_eq!(
        Chain::new(Vec::from([earlier.clone(), later.clone()])).to_string(),
        format!("{earlier} ; {later}")
    );
    let holds = Outcome::<MapCase>::Holds { cases: 3.into() };
    let fails = Outcome::Fails {
        cases: 4.into(),
        witness: later.clone(),
    };
    let verdicts = [Verdict::Holds, Verdict::Fails].map(|verdict| verdict.to_string());
    assert_ne!(verdicts[0], verdicts[1]);
    let (held, failed) = (holds.to_string(), fails.to_string());
    assert!(
        held.starts_with(&verdicts[0]) && held.contains('3'),
        "{held}"
    );
    assert!(
        failed.starts_with(&verdicts[1])
            && failed.contains('4')
            && failed.ends_with(&later.to_string()),
        "{failed}"
    );
    assert!(matches!(holds.witness(), Maybe::Absent(_)));
    assert!(matches!(fails.witness(), Maybe::Present(witness) if *witness == later));
    let missing = FactorizationFailure {
        case: later.clone(),
        defect: FactorizationDefect::Missing,
    }
    .to_string();
    assert!(
        missing.ends_with(&later.to_string()) && missing != later.to_string(),
        "{missing}"
    );
}

/// Each defect a condition reports reads apart from the others: the four
/// ways a factorization fails, the seven clauses a candidate map breaks, the
/// five refusals of a shape, the stick with its wire, and the four ways a
/// shape fails to be a colimit, each of these last with the vertex or the
/// maps it names, and a failure with its shape and test shape before it.
#[test]
fn every_defect_reads_apart_and_names_what_it_carries()
{
    let distinct = |written: &[String]| {
        assert_eq!(
            written.iter().collect::<BTreeSet<_>>().len(),
            written.len(),
            "{written:?}"
        );
    };
    distinct(
        &[
            FactorizationDefect::Missing,
            FactorizationDefect::SeveralMiddles,
            FactorizationDefect::Unrelated,
            FactorizationDefect::NotUniquelyRelated,
        ]
        .map(|defect| defect.to_string()),
    );
    let (vertex, wire) = (Edge::from(0_usize), Wire::from(0_usize));
    distinct(
        &[
            MapObstruction::ImageCount {
                expected: EdgeCount::from(1_usize),
                found: EdgeCount::from(2_usize),
            },
            MapObstruction::WireImageCount {
                expected: WireCount::from(1_usize),
                found: WireCount::from(2_usize),
            },
            MapObstruction::ImageOutOfRange { vertex },
            MapObstruction::WireOutOfRange { wire },
            MapObstruction::Overlap {
                first: vertex,
                second: Edge::from(1_usize),
            },
            MapObstruction::Boundary {
                vertex,
                leg: Leg::Input,
            },
            MapObstruction::Fusion { wire },
        ]
        .map(|obstruction| obstruction.to_string()),
    );
    let shapes = [
        ShapeObstruction::TooManyVertices {
            vertices: EdgeCount::from(65_usize),
        },
        ShapeObstruction::UnknownVertex {
            wire,
            vertex: Edge::from(1_usize),
        },
        ShapeObstruction::Stick {
            wire: Wire::from(3_usize),
        },
        ShapeObstruction::UnknownWire { wire },
        ShapeObstruction::Carrier(WiringObstruction::DirectedCycle { through: vertex }),
        ShapeObstruction::PastTheBudget {
            counted: ClassCount::from(31_usize),
        },
    ]
    .map(|refusal| refusal.to_string());
    distinct(&shapes);
    assert!(shapes[2].contains('3'), "{}", shapes[2]);
    assert!(shapes[5].contains("31"), "{}", shapes[5]);
    let (first, second) = (site_map!([{ 0 }], []), site_map!([{ 1 }], [0]));
    let family = || Box::from([first.clone(), second.clone()]);
    let defects = [
        SegalDefect::Uncovered {
            vertex: Edge::from(2_usize),
        },
        SegalDefect::Stray {
            map: second.clone(),
        },
        SegalDefect::Ambiguous { family: family() },
        SegalDefect::Unmediated { family: family() },
    ];
    let written = defects.clone().map(|defect| defect.to_string());
    distinct(&written);
    assert!(written[0].ends_with(" 2"), "{}", written[0]);
    assert!(written[1].ends_with(&second.to_string()), "{}", written[1]);
    let pair = format!(" {first} ; {second}");
    for family in &written[2 ..] {
        assert!(family.ends_with(&pair), "{family}");
    }
    let [uncovered, ..] = defects;
    assert_eq!(
        SegalFailure {
            shape: shape!(1),
            test: shape!(0),
            defect: uncovered,
        }
        .to_string(),
        format!("{} against {}: {}", shape!(1), shape!(0), written[0])
    );
}
