//! A block's rule certificate, decided by the kernel's reading of it.

use alloc::vec::Vec;

use gandr_kernel_term::CriticalPeak;
use gandr_kernel_term::SidePosition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use super::*;
use crate::coincide::Decisions;
use crate::desc_cells::CellReport;
use crate::desc_cells::elaborate_desc_cells;
use crate::description::DescriptionReport;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::unit::Unit;

/// The descriptions `source` writes, and the cells the cell gate reads off
/// them, each block decided afresh.
///
/// # Specification
/// trivial.
fn celled(source: SourceText<'_>) -> (DescriptionReport, CellReport)
{
    let grammar = grammar();
    let tree = parse(&grammar, source).unwrap().into_tree();
    let described = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    let cells = elaborate_desc_cells(&described.declarations, &mut Decisions::none());
    (described, cells)
}

/// The one block's certificate, and the kernel's verdict on the rules it
/// states.
///
/// # Specification
/// trivial.
fn certified(
    described: &DescriptionReport,
    report: &CellReport,
) -> (
    RuleCertificate,
    Result<(), gandr_kernel_term::TheoryRuleRefusal>,
)
{
    let [ref cells] = *report.declarations.as_slice()
    else {
        panic!("one block")
    };
    let description = &described
        .declarations
        .first()
        .expect("one described block")
        .description;
    let certificate = rule_certificate(description, cells);
    let mut symbols = Symbols::new(&certificate.ranks);
    let written: Vec<TheoryRule> = cells
        .oriented
        .iter()
        .map(|face| symbols.face(face, Nameable(false)))
        .collect();
    let faces: Vec<TheoryRule> = certificate
        .derived
        .iter()
        .map(|face| symbols.rule(&face.left, &face.right, &[], Nameable(false)))
        .collect();
    let mut rules = TheoryRules::new(symbols.table(), written);
    for (face, rule) in certificate.derived.iter().zip(faces) {
        rules.derive(rule, CriticalPeak {
            outer: gandr_kernel_term::RuleIndex::from(usize::from(face.peak.outer)),
            position: SidePosition::from(usize::from(face.peak.position)),
            inner: gandr_kernel_term::RuleIndex::from(usize::from(face.peak.inner)),
        });
    }
    let verdict = rules.decide(&mut RewriteFuel::from(gandr_kernel_term::PRESENTATION_FUEL));
    (certificate, verdict)
}

#[test]
fn a_groups_certificate_replays_in_the_kernel()
{
    let derived = |report: &CellReport| match report.declarations[0].coincidence {
        Coincidence::Joined(ref certificates) => certificates.derived_terms.len(),
        Coincidence::Unexamined | Coincidence::Orthogonal | Coincidence::Refused(_) => 0,
    };
    let (described, cells) = celled(SourceText::from(include_str!(
        "tests/unformatted/a-groups-certificate-replays-in-the-kernel-group.gandr"
    )));
    let (certificate, verdict) = certified(&described, &cells);
    let completed = derived(&cells);
    assert!(completed > 0, "the inverse law completes");
    assert_eq!(
        certificate.derived.len(),
        completed,
        "every derived rule is found at a peak: {certificate:?}"
    );
    assert_eq!(certificate.turns, [RuleTurn::AsWritten; 3]);
    assert_eq!(verdict, Ok(()), "{certificate:?}");
    let (described, cells) = celled(SourceText::from(include_str!(
        "tests/unformatted/a-groups-certificate-replays-in-the-kernel-unital.gandr"
    )));
    let (certificate, verdict) = certified(&described, &cells);
    assert_eq!((derived(&cells), certificate.derived.len()), (0, 0));
    assert_eq!(
        certificate.turns,
        [RuleTurn::Turned],
        "a law written growing rewrites right to left"
    );
    assert_eq!(verdict, Ok(()));
    let (described, cells) = celled(SourceText::from(include_str!(
        "tests/unformatted/a-groups-certificate-replays-in-the-kernel-pointed.gandr"
    )));
    let (certificate, verdict) = certified(&described, &cells);
    assert!(
        certificate.turns.is_empty()
            && certificate.derived.is_empty()
            && certificate.ranks.is_empty(),
        "a block with no rule carries nothing: {certificate:?}"
    );
    assert_eq!(verdict, Ok(()));
}
