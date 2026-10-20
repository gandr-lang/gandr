//! A block's rule certificate, decided by the kernel's reading of it.

use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_kernel_term::CriticalPeak;
use gandr_kernel_term::SidePosition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use super::*;
use crate::LoweredModule;
use crate::LoweringBudget;
use crate::fixture::grammar;
use crate::lower_module;
use crate::namespace::Recognition;

/// Lower `source` and hand the module to `inspect`.
///
/// # Specification
/// trivial.
fn lowered<R>(
    source: SourceText<'_>,
    inspect: impl FnOnce(&LoweredModule<'_>) -> R,
) -> R
{
    let grammar = grammar();
    let tree = parse(&grammar, source).unwrap().into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    inspect(&module)
}

/// The one block's certificate, and the kernel's verdict on the rules it
/// states.
///
/// # Specification
/// trivial.
fn certified(
    module: &LoweredModule<'_>
) -> (
    RuleCertificate,
    Result<(), gandr_kernel_term::TheoryRuleRefusal>,
)
{
    let [ref cells] = *module.cells().declarations.as_slice()
    else {
        panic!("one block")
    };
    let description = &module.descriptions().declarations[0].description;
    let certificate = rule_certificate(description, cells);
    let mut symbols = Symbols::new(&certificate.ranks);
    let written: Vec<TheoryRule> = cells
        .oriented
        .iter()
        .map(|face| symbols.rule(&face.lhs, &face.rhs))
        .collect();
    let faces: Vec<TheoryRule> = certificate
        .derived
        .iter()
        .map(|face| symbols.rule(&face.left, &face.right))
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
    let derived = |module: &LoweredModule<'_>| match module.cells().declarations[0].coincidence {
        Coincidence::Joined(ref certificates) => certificates.derived_terms.len(),
        Coincidence::Unexamined | Coincidence::Orthogonal | Coincidence::Refused(_) => 0,
    };
    let group = r#"theory Group {
    sort G : Type;
    oper e : G;
    oper inv : (x : G) --> G;
    oper mul : (x : G, y : G) --> G;
    rule unitL : mul(e(), x) <=> x;
    rule assoc : mul(mul(x, y), z) <=> mul(x, mul(y, z));
    rule invL : mul(inv(x), x) <=> e();
}"#;
    lowered(SourceText::from(group), |module| {
        let (certificate, verdict) = certified(module);
        let derived = derived(module);
        assert!(derived > 0, "the inverse law completes");
        assert_eq!(
            certificate.derived.len(),
            derived,
            "every derived rule is found at a peak: {certificate:?}"
        );
        assert_eq!(certificate.turns, [RuleTurn::AsWritten; 3]);
        assert_eq!(verdict, Ok(()), "{certificate:?}");
    });
    let unital = r#"theory Unital {
    sort M : Type;
    oper e : M;
    oper mul : (x : M, y : M) --> M;
    rule unitL : x <=> mul(e(), x);
}"#;
    lowered(SourceText::from(unital), |module| {
        let (certificate, verdict) = certified(module);
        let derived = derived(module);
        assert_eq!((derived, certificate.derived.len()), (0, 0));
        assert_eq!(
            certificate.turns,
            [RuleTurn::Turned],
            "a law written growing rewrites right to left"
        );
        assert_eq!(verdict, Ok(()));
    });
}
