//! A block's rules decided as one rewriting system, through the production
//! lowering route.

use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_theory_computads::ElaborateError;

use super::*;
use crate::DeclarationOutcome;
use crate::LoweredModule;
use crate::LoweringBudget;
use crate::desc_cells::CellFault;
use crate::fixture::grammar;
use crate::lower_module;
use crate::namespace::Recognition;

/// Addition with both unit laws: the two unit rules overlap at `add(Zero,
/// Zero)`, the right unit and the successor rule at `add(Succ(m), Zero)`, and
/// both pairs join.
const BOTH_UNITS: &str = r#"data NatUnits : Type {
    Zero : NatUnits;
    Succ : (n : NatUnits) --> NatUnits;
    oper add(m : NatUnits, n : NatUnits) -> NatUnits;
    rule add(Zero, n) ==> n;
    rule add(m, Zero) ==> m;
    rule add(Succ(m), n) ==> Succ(add(m, n));
}"#;

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

/// The source text a span covers.
///
/// # Specification
/// trivial.
fn text(
    source: SourceText<'_>,
    span: ByteSpan,
) -> SourceFragment<'_>
{
    source.fragment(span).unwrap()
}

#[test]
fn an_overlap_that_joins_is_certified_and_runs_either_way()
{
    lowered(SourceText::from(BOTH_UNITS), |module| {
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one family")
        };
        let Coincidence::Joined(ref certificates) = cells.coincidence
        else {
            panic!("the overlaps join: {:?}", cells.coincidence)
        };
        assert_eq!(
            certificates.commands.len(),
            2,
            "`add(Zero, Zero)` and `add(Succ(m), Zero)` are the two critical pairs"
        );
        assert!(certificates.terms.is_empty(), "no rule is read over terms");
        let rewriting = cells.rewriting();
        assert!(
            certificates
                .commands
                .iter()
                .all(|certificate| bool::from(certificate.replay(&rewriting))),
            "every certificate replays over the rewriting it was decided over"
        );
        assert!(module.cells().diagnostics.is_empty());
        let names: Vec<_> = module
            .declarations()
            .iter()
            .map(|declaration| String::from(declaration.name().as_ref()))
            .collect();
        assert_eq!(
            names,
            ["NatUnits", "add"],
            "the family stands and its operation runs"
        );
        let family = module.declarations().iter().next().unwrap();
        for (call, normal) in [
            ("add(Zero, Zero)", "Zero"),
            ("add(Succ(Zero), Zero)", "Succ(Zero)"),
            (
                "add(Succ(Zero), Succ(Succ(Zero)))",
                "Succ(Succ(Succ(Zero)))",
            ),
        ] {
            let reached = module
                .normal_form(family, CallText::from(call))
                .unwrap_or_else(|fault| panic!("{call}: {fault}"));
            assert_eq!(reached.spelling(), normal, "{call}");
            assert!(
                matches!(reached.path, NormalPath::Commands(ref path) if !path.is_empty()),
                "{call}: the normal form is reached by a path of commands that replayed"
            );
        }
    });
}

/// The circle presented by its two cancellations.
const CIRCLE: &str = r#"data Circle : Type {
    Base : Circle;
    Loop : (c : Circle) --> Circle;
    Unloop : (c : Circle) --> Circle;
    rule Loop(Unloop(x)) ==> x;
    rule Unloop(Loop(x)) ==> x;
}"#;

#[test]
fn the_circles_cancellations_join_below_the_root()
{
    lowered(SourceText::from(CIRCLE), |module| {
        assert!(
            module.cells().diagnostics.is_empty(),
            "{:?}",
            module.cells().diagnostics
        );
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one family")
        };
        assert!(
            cells.faces.is_empty() && cells.declined_faces.is_empty(),
            "no cancellation is a sequent cell"
        );
        let Maybe::Present(ref presented) = cells.presented
        else {
            panic!("the circle is read over terms")
        };
        let Coincidence::Joined(ref certificates) = cells.coincidence
        else {
            panic!("the cancellations join: {:?}", cells.coincidence)
        };
        assert!(certificates.commands.is_empty(), "no sequent pair");
        let peaks: Vec<String> = certificates
            .terms
            .iter()
            .map(|certificate| match certificate.overlap.peak.read() {
                Maybe::Present(term) => term.to_string(),
                Maybe::Absent(reason) => panic!("a peak spells a term: {reason:?}"),
            })
            .collect();
        assert_eq!(
            peaks,
            ["Loop(Unloop(Loop(x')))", "Unloop(Loop(Unloop(x')))"],
            "each cancellation meets the other inside its left-hand side"
        );
        assert!(
            certificates
                .terms
                .iter()
                .all(|certificate| bool::from(certificate.replay(&presented.store))),
            "every certificate replays over the term store"
        );
        let family = module.declarations().iter().next().unwrap();
        assert!(
            matches!(family.outcome(), DeclarationOutcome::Data(_)),
            "the family stands"
        );
        for (call, normal, steps) in [
            ("Loop(Unloop(Loop(Base)))", "Loop(Base)", 1_usize),
            ("Unloop(Loop(Base))", "Base", 1),
            ("Loop(Loop(Unloop(Unloop(Loop(Base)))))", "Loop(Base)", 2),
            ("Loop(Loop(Base))", "Loop(Loop(Base))", 0),
        ] {
            let reached = module
                .normal_form(family, CallText::from(call))
                .unwrap_or_else(|fault| panic!("{call}: {fault}"));
            assert_eq!(reached.spelling(), normal, "{call}");
            assert!(
                matches!(reached.path, NormalPath::Terms(ref path) if path.len() == steps),
                "{call}: {steps} steps over terms, replayed"
            );
        }
    });
}

#[test]
fn a_third_cancellation_parts_the_circles_readings()
{
    let source = SourceText::from(
        r#"@[ checks ]
data Circle : Type {
    Base : Circle;
    Loop : (c : Circle) --> Circle;
    Unloop : (c : Circle) --> Circle;
    rule Loop(Unloop(x)) ==> x;
    rule Unloop(Loop(x)) ==> x;
    rule Loop(Loop(x)) ==> x;
}"#,
    );
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        let CellFault::Coherence(ref fault @ CoherenceFault::Diverges { first, .. }) =
            diagnostic.fault
        else {
            panic!("the pair diverges: {:?}", diagnostic.fault)
        };
        assert_eq!(
            text(source, diagnostic.span).as_ref(),
            "rule Loop(Loop(x)) ==> x",
            "the refusal stands at the third rule"
        );
        assert_eq!(
            text(source, first).as_ref(),
            "rule Loop(Unloop(x)) ==> x",
            "and names the cancellation it parts from"
        );
        assert_eq!(
            fault.to_string(),
            "both rules rewrite `Loop(Loop(Unloop(x')))`, one to `Loop(x')` and the other to \
             `Unloop(x')`"
        );
        let [family] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the refused family")
        };
        assert_eq!(
            family.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesDiverge {
                span: diagnostic.span,
                first
            }),
            "the family is refused under its own name"
        );
        assert_eq!(
            module.normal_form(family, CallText::from("Loop(Loop(Base))")),
            Err(NormalFormFault::Incoherent)
        );
    });
}

/// The circle's shape: the presentation the circle's constructors present,
/// read as a signature whose models interpret it.
const CIRCLE_SHAPE: &str = r#"theory CircleShape {
    sort Pt : Type;
    oper base : Pt;
    oper turn : (x : Pt) --> Pt;
    oper unturn : (x : Pt) --> Pt;
    rule turnUnturn : turn(unturn(x)) ==> x;
    rule unturnTurn : unturn(turn(x)) ==> x;
}"#;

/// The peaks of a block's term certificates, spelled, or the block's cell
/// diagnostics.
///
/// # Specification
/// trivial.
fn term_peaks(module: &LoweredModule<'_>) -> Result<Vec<String>, Vec<CellFault>>
{
    let diagnostics = &module.cells().diagnostics;
    if !diagnostics.is_empty() {
        return Err(diagnostics
            .iter()
            .map(|diagnostic| diagnostic.fault.clone())
            .collect());
    }
    let [ref cells] = *module.cells().declarations.as_slice()
    else {
        panic!("one block")
    };
    let Coincidence::Joined(ref certificates) = cells.coincidence
    else {
        panic!("the block joins: {:?}", cells.coincidence)
    };
    Ok(certificates
        .terms
        .iter()
        .map(|certificate| match certificate.overlap.peak.read() {
            Maybe::Present(term) => term.to_string(),
            Maybe::Absent(reason) => panic!("a peak spells a term: {reason:?}"),
        })
        .collect())
}

#[test]
fn the_circles_shape_joins_where_the_circle_does()
{
    let shape = lowered(SourceText::from(CIRCLE_SHAPE), |module| {
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one presentation")
        };
        assert!(
            cells.faces.is_empty() && cells.declined_faces.is_empty(),
            "no law is a sequent cell, and none is declined"
        );
        assert!(
            matches!(cells.presented, Maybe::Present(ref presented) if presented.faces.len() == 2),
            "both laws are read over terms"
        );
        term_peaks(module)
    })
    .expect("the laws join");
    assert_eq!(
        shape,
        ["turn(unturn(turn(x')))", "unturn(turn(unturn(x')))"],
        "each law meets the other inside its left-hand side"
    );
    let circle = lowered(SourceText::from(CIRCLE), term_peaks).expect("the rules join");
    let renamed: Vec<String> = circle
        .iter()
        .map(|peak| peak.replace("Unloop(", "unturn(").replace("Loop(", "turn("))
        .collect();
    assert_eq!(
        shape, renamed,
        "the presentation meets where the presented type does"
    );
    let tampered = CIRCLE_SHAPE.replace('}', "    rule twice : turn(turn(x)) ==> x;\n}");
    let derived = lowered(SourceText::from(tampered.as_str()), |module| {
        let _peaks = term_peaks(module).expect("a third law completes");
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one block")
        };
        let (&Maybe::Present(ref presented), &Coincidence::Joined(ref certificates)) =
            (&cells.presented, &cells.coincidence)
        else {
            panic!("the laws are read over terms and complete")
        };
        certificates
            .derived_terms
            .iter()
            .map(|rule| {
                let Maybe::Present(cell) = presented.store.get(rule.cell)
                else {
                    panic!("a derived rule is a cell of the store")
                };
                match (cell.lhs().read(), cell.rhs().read()) {
                    (Maybe::Present(lhs), Maybe::Present(rhs)) => format!("{lhs} ==> {rhs}"),
                    sides => panic!("a derived rule spells two terms: {sides:?}"),
                }
            })
            .collect::<Vec<String>>()
    });
    assert_eq!(
        derived,
        ["unturn(x') ==> turn(x')"],
        "a turn that undoes itself makes the two turns one, and the completion says so"
    );
}

#[test]
fn two_rules_rewriting_one_term_apart_refuse_the_block()
{
    let source = SourceText::from(
        r#"@[ checks ]
data NatApart : Type {
    Zero : NatApart;
    Succ : (n : NatApart) --> NatApart;
    oper add(m : NatApart, n : NatApart) -> NatApart;
    rule add(Zero, n) ==> n;
    rule add(m, Zero) ==> Succ(m);
    rule add(Succ(m), n) ==> Succ(add(m, n));
}
def later = 7;"#,
    );
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        let CellFault::Coherence(ref fault @ CoherenceFault::Diverges { first, .. }) =
            diagnostic.fault
        else {
            panic!("the pair diverges: {:?}", diagnostic.fault)
        };
        assert_eq!(
            text(source, diagnostic.span).as_ref(),
            "rule add(m, Zero) ==> Succ(m)",
            "the refusal stands at the later rule"
        );
        assert_eq!(
            text(source, first).as_ref(),
            "rule add(Zero, n) ==> n",
            "and names the earlier one"
        );
        assert_eq!(
            fault.to_string(),
            "both rules rewrite `add(Zero, Zero)`, one to `Zero` and the other to `Succ(Zero)`"
        );
        assert!(matches!(
            module.cells().declarations[0].coincidence,
            Coincidence::Refused(CellDiagnosticIndex(0))
        ));
        let [family, later] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the refused family and the later declaration, and no operation")
        };
        assert_eq!(
            family.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesDiverge {
                span: diagnostic.span,
                first
            }),
            "the family is refused under its own name"
        );
        assert!(matches!(later.outcome(), DeclarationOutcome::Bodied { .. }));
        assert_eq!(
            module.normal_form(family, CallText::from("add(Zero, Zero)")),
            Err(NormalFormFault::Incoherent)
        );
    });
}

/// A group's laws with the left inverse: associativity and the inverse law
/// meet at `mul(mul(inv(x), x), z)`, which they leave at `z` and at
/// `mul(inv(x), mul(x, z))`.
const GROUP: &str = r#"theory Group {
    sort G : Type;
    oper e : G;
    oper a : G;
    oper b : G;
    oper inv : (x : G) --> G;
    oper mul : (x : G, y : G) --> G;
    rule unitL : mul(e(), x) <=> x;
    rule assoc : mul(mul(x, y), z) <=> mul(x, mul(y, z));
    rule invL : mul(inv(x), x) <=> e();
}"#;

#[test]
fn a_groups_inverse_law_completes_to_the_rules_it_derives()
{
    lowered(SourceText::from(GROUP), |module| {
        assert!(
            module.cells().diagnostics.is_empty(),
            "{:?}",
            module.cells().diagnostics
        );
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one block")
        };
        let Maybe::Present(ref presented) = cells.presented
        else {
            panic!("the laws are read over terms")
        };
        let Coincidence::Joined(ref certificates) = cells.coincidence
        else {
            panic!("the laws complete: {:?}", cells.coincidence)
        };
        assert!(
            certificates
                .derived_terms
                .iter()
                .all(|derived| bool::from(derived.replay(&presented.store))),
            "every derived rule follows from the cells before it"
        );
        assert!(
            certificates
                .terms
                .iter()
                .all(|certificate| bool::from(certificate.replay(&presented.store))),
            "every critical pair of the completed rules joins"
        );
        let [ref first, ..] = *certificates.derived_terms
        else {
            panic!("a derived rule")
        };
        let mut retargeted = first.clone();
        retargeted.cell = CellId::from(usize::from(presented.store.len()));
        assert!(
            !bool::from(retargeted.replay(&presented.store)),
            "a certificate names its own cell"
        );
        let mut cut = first.clone();
        let _dropped = cut.certificate.path_a.pop();
        let _dropped = cut.certificate.path_b.pop();
        assert!(
            !bool::from(cut.replay(&presented.store)),
            "a certificate fires its rule"
        );
        let family = module.declarations().iter().next().unwrap();
        for (call, normal) in [
            ("mul(inv(a), mul(a, b))", "b"),
            ("mul(a, inv(a))", "e"),
            ("inv(mul(a, b))", "mul(inv(b), inv(a))"),
        ] {
            let reached = module
                .normal_form(family, CallText::from(call))
                .unwrap_or_else(|fault| panic!("{call}: {fault}"));
            assert_eq!(reached.spelling(), normal, "{call}");
        }
    });
}

/// A scope-extrusion block: completion joins `par(nu(nil()), q)` by
/// `nu(par(nil, q)) ==> par(nil, q)`, that rule and `scope` by the same rule
/// with `nil` wrapped in `par(□, q')`, and so on, one wrapping deeper every
/// round (#1604).
const SCOPE_EXTRUSION: &str = "theory S {
  sort Proc : Type;
  oper nil : () --> Proc;
  oper par : (p : Proc, q : Proc) --> Proc;
  oper nu : (p : Proc) --> Proc;
  rule gc : nu(nil()) ==> nil();
  rule scope : par(nu(p), q) ==> nu(par(p, q));
";

#[test]
fn a_scope_extrusion_family_never_completes()
{
    let block = alloc::format!("{SCOPE_EXTRUSION}}}");
    let source = SourceText::from(block.as_str());
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        let CellFault::Coherence(ref fault @ CoherenceFault::NeverCompletes { first, .. }) =
            diagnostic.fault
        else {
            panic!("the family never completes: {:?}", diagnostic.fault)
        };
        assert_eq!(
            text(source, first).as_ref(),
            "rule scope : par(nu(p), q) ==> nu(par(p, q))",
            "the refusal names the written rule the family overlaps"
        );
        assert_eq!(
            fault.to_string(),
            "the rule completion derives at round 2, `nu(par(par(nil, q'), q)) ==> par(par(nil, \
             q'), q)`, is the rule it derived at round 1, `nu(par(nil, q)) ==> par(nil, q)`, with \
             one subterm wrapped, and no rule rewrites a further wrapping, so every round derives \
             a longer rule",
            "the second derived rule is refused, naming the first"
        );
        let [family, ..] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the refused family")
        };
        assert_eq!(
            family.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesNeverComplete {
                span: diagnostic.span,
                first
            }),
            "the family is refused under its own name"
        );
    });
    // A rule flattening the third wrapping, or the fourth, stops the family
    // after the second or the third derived rule, though each derived rule
    // wraps the one before.
    for flat in [
        "rule flat : par(par(par(nil(), p), q), r) ==> par(par(nil(), q), r);",
        "rule flat : par(par(par(par(nil(), p), q), r), s) ==> par(par(par(nil(), q), r), s);",
    ] {
        let block = alloc::format!("{SCOPE_EXTRUSION}  {flat}\n}}");
        lowered(SourceText::from(block.as_str()), |module| {
            assert!(
                module.cells().diagnostics.is_empty(),
                "{flat}: {:?}",
                module.cells().diagnostics
            );
            let [ref cells] = *module.cells().declarations.as_slice()
            else {
                panic!("one block")
            };
            assert!(
                matches!(cells.coincidence, Coincidence::Joined(_)),
                "{flat}: the rules complete"
            );
        });
    }
}

#[test]
fn a_permuted_call_no_order_orients_is_uncompleted()
{
    let source = SourceText::from(
        r#"data Nat : Type {
    Zero : Nat;
    Succ : (n : Nat) --> Nat;
    oper plus(m : Nat, n : Nat) -> Nat;
    oper pick(m : Nat, n : Nat) -> Nat;
    rule pick(m, n) ==> plus(m, n);
    rule pick(Zero, n) ==> plus(n, Zero);
}"#,
    );
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        let CellFault::Coherence(ref fault @ CoherenceFault::Uncompleted { first, .. }) =
            diagnostic.fault
        else {
            panic!("the pair is uncompleted: {:?}", diagnostic.fault)
        };
        assert_eq!(
            text(source, diagnostic.span).as_ref(),
            "rule pick(Zero, n) ==> plus(n, Zero)",
            "the refusal stands at the later rule"
        );
        assert_eq!(
            text(source, first).as_ref(),
            "rule pick(m, n) ==> plus(m, n)",
            "and names the earlier one"
        );
        assert_eq!(
            fault.to_string(),
            "both rules rewrite `pick(Zero, n')`, one to `plus(Zero, n')` and the other to \
             `plus(n', Zero)`, and the path order orients no rule from an operation call between \
             the two"
        );
        let [family, ..] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the refused family")
        };
        assert_eq!(
            family.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesUncompleted {
                span: diagnostic.span,
                first
            }),
            "the family is refused under its own name"
        );
    });
}

#[test]
fn a_data_blocks_derived_rule_is_a_pattern_rule()
{
    let completed = SourceText::from(
        r#"data NatSwap : Type {
    Zero : NatSwap;
    Succ : (n : NatSwap) --> NatSwap;
    oper add(m : NatSwap, n : NatSwap) -> NatSwap;
    oper swap(m : NatSwap, n : NatSwap) -> NatSwap;
    rule add(Zero, n) ==> n;
    rule add(Succ(m), n) ==> Succ(add(m, n));
    rule swap(m, n) ==> add(m, n);
    rule swap(Zero, n) ==> add(n, Zero);
}"#,
    );
    lowered(completed, |module| {
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one block")
        };
        let Coincidence::Joined(ref certificates) = cells.coincidence
        else {
            panic!("the rules complete: {:?}", cells.coincidence)
        };
        let derived: Vec<String> = certificates
            .derived_commands
            .iter()
            .map(|derived| format!("{} ==> {}", derived.rule.0, derived.rule.1))
            .collect();
        assert_eq!(
            derived,
            ["add(n', Zero) ==> n'"],
            "the pair's call rewrites to its variable, over constructor patterns"
        );
        let reached = module
            .normal_form(
                module.declarations().iter().next().unwrap(),
                CallText::from("swap(Zero, Succ(Zero))"),
            )
            .unwrap_or_else(|fault| panic!("{fault}"));
        assert_eq!(reached.spelling(), "Succ(Zero)");
    });
    let repeated = SourceText::from(
        r#"data NatTwice : Type {
    Zero : NatTwice;
    Succ : (n : NatTwice) --> NatTwice;
    oper add(m : NatTwice, n : NatTwice) -> NatTwice;
    oper pick(m : NatTwice, n : NatTwice) -> NatTwice;
    rule add(Zero, n) ==> n;
    rule add(Succ(m), n) ==> Succ(add(m, n));
    rule pick(m, n) ==> n;
    rule pick(Zero, n) ==> add(n, n);
}"#,
    );
    lowered(repeated, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        assert!(
            matches!(
                diagnostic.fault,
                CellFault::Coherence(CoherenceFault::Uncompleted { .. })
            ),
            "the one rule joining `n'` and `add(n', n')` repeats a variable in its pattern: {:?}",
            diagnostic.fault
        );
    });
}

#[test]
fn two_rules_written_the_other_way_round_are_refused_at_the_later_one_all_the_same()
{
    let source = SourceText::from(
        r#"@[ checks ]
data NatApart : Type {
    Zero : NatApart;
    Succ : (n : NatApart) --> NatApart;
    oper add(m : NatApart, n : NatApart) -> NatApart;
    rule add(m, Zero) ==> Succ(m);
    rule add(Zero, n) ==> n;
    rule add(Succ(m), n) ==> Succ(add(m, n));
}"#,
    );
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        let CellFault::Coherence(ref fault @ CoherenceFault::Diverges { first, .. }) =
            diagnostic.fault
        else {
            panic!("the pair diverges: {:?}", diagnostic.fault)
        };
        assert_eq!(
            text(source, diagnostic.span).as_ref(),
            "rule add(Zero, n) ==> n",
            "the refusal stands at the later rule"
        );
        assert_eq!(
            text(source, first).as_ref(),
            "rule add(m, Zero) ==> Succ(m)",
            "and names the earlier one"
        );
        assert_eq!(
            fault.to_string(),
            "both rules rewrite `add(Zero, Zero)`, one to `Succ(Zero)` and the other to `Zero`"
        );
    });
}

#[test]
fn a_pinned_rule_orients_only_the_way_it_is_pinned()
{
    use crate::description::written::RuleDirection::LeftToRight;
    use crate::description::written::RuleDirection::RightToLeft;
    use crate::description::written::RuleOrientation::Pinned;
    use crate::description::written::RuleOrientation::Unpinned;

    let source = SourceText::from(
        r#"data Int : Type {
    Z : Int;
    S : (x : Int) --> Int;
    P : (x : Int) --> Int;
    rule x <=> S(P(x));
    rule P(S(x)) <=> x;
}"#,
    );
    lowered(source, |module| {
        let description = &module
            .described()
            .next()
            .expect("one described block")
            .description;
        let orient = |orientations: &[RuleOrientation]| {
            orient_block(description, orientations).map(|block| block.directions)
        };
        assert_eq!(
            orient(&[Pinned(RightToLeft), Pinned(LeftToRight)]),
            Ok(Vec::from([RightToLeft, LeftToRight])),
            "each rule pinned the way it runs"
        );
        assert_eq!(
            orient(&[Pinned(LeftToRight), Unpinned]),
            Err(RuleIndex::from(0_usize)),
            "a rule pinned against its order"
        );
        assert_eq!(
            orient(&[Unpinned, Pinned(RightToLeft)]),
            Err(RuleIndex::from(1_usize)),
            "and the other"
        );
    });
    let commuting = SourceText::from(
        r#"data Pair : Type {
    Z : Pair;
    oper add(m : Pair, n : Pair) -> Pair;
    rule add(m, n) <=> add(n, m);
}"#,
    );
    lowered(commuting, |module| {
        let description = &module
            .described()
            .next()
            .expect("one described block")
            .description;
        assert_eq!(
            orient_block(description, &[Unpinned]).map(|block| block.directions),
            Err(RuleIndex::from(0_usize)),
            "a rule the order runs neither way orients neither way"
        );
    });
}

#[test]
fn a_call_lends_the_text_it_was_written_as()
{
    assert_eq!(
        CallText::from("add(Succ(Zero), Zero)").as_ref(),
        "add(Succ(Zero), Zero)"
    );
}

#[test]
fn a_rule_that_rebuilds_its_own_call_refuses_the_block()
{
    let source = SourceText::from(
        r#"data NatGrow : Type {
    Zero : NatGrow;
    Succ : (n : NatGrow) --> NatGrow;
    oper grow(n : NatGrow) -> NatGrow;
    rule grow(n) ==> Succ(grow(n));
}"#,
    );
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        assert_eq!(
            diagnostic.fault,
            CellFault::Coherence(CoherenceFault::Unoriented)
        );
        assert_eq!(
            text(source, diagnostic.span).as_ref(),
            "rule grow(n) ==> Succ(grow(n))"
        );
        assert_eq!(
            module.declarations().iter().next().unwrap().outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesUnoriented {
                span: diagnostic.span
            })
        );
    });
}

#[test]
fn a_second_order_rule_overlapping_another_refuses_the_block()
{
    let theory = |rules: &str| {
        format!(
            "theory Let {{
    sort Tm : Type+;
    oper zero : () --> Tm;
    oper f : (a : Tm) --> Tm;
    oper let : (u : Tm, t : pi+ (x : Tm) . Tm) --> Tm;
    rule zeta : let(u, t) <=> t(u);
    {rules}
}}"
        )
    };
    let joins = theory("rule zetaZero : let(zero(), t) <=> t(zero());");
    lowered(SourceText::from(joins.as_str()), |module| {
        assert_eq!(
            module.cells().diagnostics,
            [],
            "ζ and ζ at `zero()` overlap at the root and both reducts are `t(zero())`"
        );
    });
    for (rules, later) in [
        (
            "rule toZero : let(zero(), t) <=> zero();",
            "rule toZero : let(zero(), t) <=> zero()",
        ),
        (
            "rule under : f(let(u, t)) <=> f(u);",
            "rule under : f(let(u, t)) <=> f(u)",
        ),
    ] {
        let source = theory(rules);
        let source = SourceText::from(source.as_str());
        lowered(source, |module| {
            let [ref diagnostic] = *module.cells().diagnostics.as_slice()
            else {
                panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
            };
            let CellFault::Coherence(CoherenceFault::OverlapsSecondOrder { first }) =
                diagnostic.fault
            else {
                panic!("{later} parts from ζ: {:?}", diagnostic.fault)
            };
            assert_eq!(text(source, diagnostic.span).as_ref(), later);
            assert_eq!(
                text(source, first).as_ref(),
                "rule zeta : let(u, t) <=> t(u)",
                "{later} names ζ"
            );
            assert_eq!(
                module.declarations().iter().next().unwrap().outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::RulesOverlapSecondOrder {
                    span: diagnostic.span,
                    first
                })
            );
        });
    }
    let apart = theory("rule fZero : f(zero()) <=> zero();");
    lowered(SourceText::from(apart.as_str()), |module| {
        assert_eq!(
            module.cells().diagnostics,
            [],
            "ζ overlaps no left side of a rule over `f` alone, nor its own below the root"
        );
    });
}

/// #2115: a metavariable applied to the names its abstractions bind reads
/// as a pattern, so a get-get rule overlaps its own left side below the
/// root; in the second-order reading the pair joins.
#[test]
fn a_pattern_overlapping_its_own_rule_joins_2115()
{
    let theory = |rule: &str| {
        format!(
            "theory State {{
    sort S : Type+;
    sort C : Type;
    oper ret : (a : S) --> C;
    oper ext : (m : C, k : pi+ (x : S) . C) --> C;
    oper get : (k : pi+ (s : S) . C) --> C;
    {rule}
}}"
        )
    };
    let get_get =
        theory("rule getGet : get(bind s . get(bind t . k(s, t))) <=> get(bind s . k(s, s));");
    lowered(SourceText::from(get_get.as_str()), |module| {
        assert_eq!(
            module.cells().diagnostics,
            [],
            "the inner `get` is an instance of the rule's own left side, and both reducts \
             normalize to `get(bind s . k(s, s, s))`"
        );
    });
    let right_unit = theory("rule unitR : ext(m, bind x . ret(x)) <=> m;");
    lowered(SourceText::from(right_unit.as_str()), |module| {
        assert_eq!(
            module.cells().diagnostics,
            [],
            "the right unit law abstracts `x` at `ext`'s port and overlaps nothing"
        );
    });
}

/// #2448: where a port takes the channel, a conditioned rule's overlap is
/// decided in the second-order reading under the freshness it composes: a pair
/// joins there, parts there, or has no instance the conditions admit.
#[test]
fn conditioned_rules_join_under_the_condition_their_overlap_composes_2448()
{
    let theory = |channel: &str, rules: &str| {
        format!(
            "theory Pi {{
    sort Name : Atom;
    sort Proc : Type;
    oper nil : () --> Proc;
    oper par : (p : Proc, q : Proc) --> Proc;
    oper out : (c : {channel}, p : Proc) --> Proc;
    oper nu : (p : bind (a : Name) . Proc) --> Proc;
    {rules}
}}"
        )
    };
    let scope = "rule scope : par(nu(bind a . p), q) <=> nu(bind a . par(p, q)) where a # q;";
    let gc = "rule gc : nu(bind a . p) <=> p where a # p;";
    for channel in ["Name", "Proc"] {
        let collecting = theory(channel, &format!("{scope}\n    {gc}"));
        lowered(SourceText::from(collecting.as_str()), |module| {
            assert_eq!(
                module.cells().diagnostics,
                [],
                "collection below extrusion joins under `a # q, a # p` where `out` takes a \
                 {channel}"
            );
        });
    }
    let quiet = theory(
        "Name",
        &format!("{gc}\n    rule quiet : nu(bind a . out(a, nil())) <=> nil();"),
    );
    lowered(SourceText::from(quiet.as_str()), |module| {
        assert_eq!(
            module.cells().diagnostics,
            [],
            "collection's instance may not name the channel `quiet` sends on: no instance \
             overlaps"
        );
    });
    let vacant = theory(
        "Name",
        &format!("{scope}\n    rule vacant : nu(bind a . nil()) <=> nil();"),
    );
    let source = SourceText::from(vacant.as_str());
    lowered(source, |module| {
        let [ref diagnostic] = *module.cells().diagnostics.as_slice()
        else {
            panic!("one cell diagnostic: {:?}", module.cells().diagnostics)
        };
        let CellFault::Coherence(CoherenceFault::OverlapsCondition { first }) = diagnostic.fault
        else {
            panic!(
                "a vacant restriction parts from extrusion: {:?}",
                diagnostic.fault
            )
        };
        assert_eq!(
            text(source, diagnostic.span).as_ref(),
            "rule vacant : nu(bind a . nil()) <=> nil()"
        );
        assert_eq!(
            text(source, first).as_ref(),
            "rule scope : par(nu(bind a . p), q) <=> nu(bind a . par(p, q)) where a # q",
            "the vacant restriction names extrusion"
        );
        assert_eq!(
            module.declarations().iter().next().unwrap().outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesOverlapCondition {
                span: diagnostic.span,
                first
            })
        );
    });
}

#[test]
fn an_equation_written_backwards_orients_forwards()
{
    let source = SourceText::from(
        r#"data Int : Type {
    Z : Int;
    S : (x : Int) --> Int;
    P : (x : Int) --> Int;
    rule x <=> S(P(x));
    rule P(S(x)) <=> x;
}"#,
    );
    lowered(source, |module| {
        let described = module.described().next().expect("one described block");
        let printed: Vec<_> = described.rules().map(|rule| rule.print_data()).collect();
        assert_eq!(printed, ["rule x <=> S(P(x))", "rule P(S(x)) <=> x"]);
        assert_eq!(
            described
                .rules()
                .next()
                .unwrap()
                .print_theory(&gandr_theory_levitation::Name::from("cancel")),
            "rule cancel : x <=> S(P(x))"
        );
        let cells = &module.cells().declarations[0];
        assert_eq!(cells.directions, [
            crate::description::written::RuleDirection::RightToLeft,
            crate::description::written::RuleDirection::LeftToRight,
        ]);
        assert!(
            matches!(
                cells.oriented[0].lhs.view(),
                gandr_theory_levitation::TermView::Ctor { name, .. } if name.as_ref() == "S"
            ),
            "the kernel-facing rule runs forwards"
        );
        let family = module.declarations().iter().next().unwrap();
        assert_eq!(
            module
                .normal_form(family, CallText::from("S(P(Z))"))
                .map(|form| form.normal),
            Ok(gandr_theory_levitation::FreeTerm::ctor("Z", []))
        );
    });
}

#[test]
fn a_congruence_is_no_rewrite_of_its_own()
{
    let source = SourceText::from(
        r#"theory Nat {
  sort Nat : Type;
  oper add : (Nat, Nat) --> Nat;

  rule cong1 : (
    rule p : Nat ==> Nat,
    data x : Nat,
    data y : Nat
  ) ==> (z : Nat) {
    node : p(x) ==> (x′);
    node : add(x′, y) --> (z);
  };
}"#,
    );
    lowered(source, |module| {
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one block")
        };
        assert!(
            matches!(cells.circuits.as_slice(), [CircuitCell::Admitted { .. }]),
            "the congruence is admitted: {:?}",
            module.cells().diagnostics
        );
        assert_eq!(cells.coincidence, Coincidence::Orthogonal);
        assert!(
            usize::from(cells.rewriting().len()) < usize::from(cells.store.len()),
            "the congruence's cell is left out of the rewriting"
        );
    });
    lowered(SourceText::from(BOTH_UNITS), |module| {
        let cells = &module.cells().declarations[0];
        assert!(
            matches!(cells.rewriting(), Cow::Borrowed(_)),
            "a family with no congruence is read in place"
        );
    });
    let with_a_rule = SourceText::from(
        r#"theory Nat {
  sort Nat : Type;
  oper add : (Nat, Nat) --> Nat;
  rule left : add(x, y) ==> x;

  rule cong1 : (
    rule p : Nat ==> Nat,
    data x : Nat,
    data y : Nat
  ) ==> (z : Nat) {
    node : p(x) ==> (x′);
    node : add(x′, y) --> (z);
  };
}"#,
    );
    lowered(with_a_rule, |module| {
        let [ref cells] = *module.cells().declarations.as_slice()
        else {
            panic!("one block")
        };
        assert!(
            !cells.faces.is_empty(),
            "the rule is a face: {:?}",
            module.cells().diagnostics
        );
        assert!(
            usize::from(cells.rewriting().len()) < usize::from(cells.store.len()),
            "the congruence's cell is left out beside a face"
        );
    });
}

#[test]
fn a_call_reads_its_normal_form_or_says_why_not()
{
    let source = SourceText::from(
        r#"data NatDiv : Type {
  Zero : NatDiv;
  Succ : (n : NatDiv) --> NatDiv;
  oper walk(m : NatDiv, g : NatDiv, d : NatDiv, q : NatDiv, r : NatDiv) -> (quot : NatDiv, rem : NatDiv);
  oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);
  rule walk(Zero, g, d, q, r) ==> (q, r);
  rule walk(Succ(m), Zero, d, q, r) ==> walk(m, d, d, Succ(q), Zero);
  rule walk(Succ(m), Succ(g), d, q, r) ==> walk(m, g, d, q, Succ(r));
  rule divmod(m, Zero) ==> (Zero, m);
  rule divmod(m, Succ(d)) ==> walk(m, d, d, Zero, Zero);
}
def later = 7;"#,
    );
    lowered(source, |module| {
        assert_eq!(
            module.cells().declarations[0].coincidence,
            Coincidence::Orthogonal
        );
        let [family, walk, .., later] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the family, its operations and the later declaration")
        };
        let five_by_two =
            CallText::from("divmod(Succ(Succ(Succ(Succ(Succ(Zero))))), Succ(Succ(Zero)))");
        let reached = module.normal_form(family, five_by_two).unwrap();
        assert_eq!(reached.spelling(), "(Succ(Succ(Zero)), Succ(Zero))");
        assert_eq!(
            module.normal_form(walk, five_by_two),
            Ok(reached),
            "an operation of the block reads a call under the block's rules"
        );
        assert_eq!(
            module
                .normal_form(family, CallText::from(" divmod ( Zero , Zero ) "))
                .map(|reached| reached.spelling()),
            Ok(String::from("(Zero, Zero)")),
            "space between the tokens is read past"
        );
        for (call, fault) in [
            ("divmod(Zero", NormalFormFault::Unread),
            ("divmod(Zero, Zero) Zero", NormalFormFault::Unread),
            ("divmod(Zero,)", NormalFormFault::Unread),
            ("plus(Zero, Zero)", NormalFormFault::UnknownSymbol),
            (
                "Succ(Zero)",
                NormalFormFault::NotACall(ElaborateError::LhsNotOperation),
            ),
        ] {
            assert_eq!(
                module
                    .normal_form(family, CallText::from(call))
                    .map(|reached| reached.spelling()),
                Err(fault),
                "{call}"
            );
        }
        assert_eq!(
            module.normal_form(later, CallText::from("divmod(Zero, Zero)")),
            Err(NormalFormFault::Undescribed)
        );
        assert_ne!(
            NormalFormFault::Unread.to_string(),
            NormalFormFault::Incoherent.to_string()
        );
    });
    let restriction = SourceText::from(
        r#"theory Unheard {
  sort Name : Atom;
  sort Proc : Type;
  oper nil : () --> Proc;
  oper out : (c : Name, p : Proc) --> Proc;
  oper nu : (p : bind (a : Name) . Proc) --> Proc;
  rule unheard : nu(bind a . out(a, p)) ==> nil();
}"#,
    );
    lowered(restriction, |module| {
        let [theory, ..] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the theory")
        };
        for (call, reached) in [
            ("nu(bind b . out(b, nil))", Ok("nil")),
            (
                "nu(bind a . nu(bind b . out(a, nil)))",
                Ok("nu(bind a0 . nu(bind a1 . out(a0, nil)))"),
            ),
            (
                "nu(bind b . out(c, nil))",
                Err(NormalFormFault::UnknownSymbol),
            ),
            (
                "out(b, nu(bind b . nil))",
                Err(NormalFormFault::UnknownSymbol),
            ),
            ("nu(bind b . out(b, nil)", Err(NormalFormFault::Unread)),
        ] {
            assert_eq!(
                module
                    .normal_form(theory, CallText::from(call))
                    .map(|reached| reached.spelling()),
                reached.map(String::from),
                "{call}: a name is the atom an enclosing abstraction binds, and only there"
            );
        }
    });
}

/// A call of operations over operations reads over terms: over a plain sort,
/// and over a graded sort carrying the grade its failure stands at, where a
/// failure passed for a cut is ill sorted. Over 2-cells a vertical composite
/// reads with its 1-cells, and a whiskered one, whose index composes homs, is
/// refused apart from an ill-sorted call (#1510).
#[test]
fn a_call_nesting_operations_reads_over_terms_1510()
{
    let choices = SourceText::from(
        r#"theory Cut {
  sort Grade : Type;
  oper bot : () --> Grade;
  oper top : () --> Grade;
  sort M(g : Grade) : Type;
  oper cut : () --> M(bot());
  oper fail : () --> M(top());
  oper orBot : (x : M(bot()), y : M(e)) --> M(bot());
  rule cutLeft : orBot(x, y) ==> x;
}"#,
    );
    let plain = SourceText::from(
        r#"theory Plain {
  sort N : Type;
  oper first : () --> N;
  oper second : () --> N;
  oper choose : (x : N, y : N) --> N;
  rule left : choose(x, y) ==> x;
}"#,
    );
    let two_cells = SourceText::from(
        r#"theory TwoCells {
  sort Ob : Type;
  sort Hom(dom : Ob, cod : Ob) : Type;
  sort Two(src : Hom(x, y), tgt : Hom(x, y)) : Type;
  oper o : () --> Ob;
  oper e : () --> Hom(o(), o());
  oper alpha : () --> Two(e(), e());
  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);
  oper vcomp : (s : Two(f, g), t : Two(g, k)) --> Two(f, k);
  oper whiskerR : (s : Two(f, g), h : Hom(b, c)) --> Two(comp(f, h), comp(g, h));
  rule vassoc : vcomp(vcomp(s, t), u) ==> vcomp(s, vcomp(t, u));
}"#,
    );
    for (source, calls) in [
        (
            choices,
            &[
                ("orBot(cut, fail)", Ok("cut")),
                ("orBot(cut, orBot(cut, fail))", Ok("cut")),
                (
                    "orBot(fail, cut)",
                    Err(NormalFormFault::Unsorted(Unsorted::Clash)),
                ),
            ][..],
        ),
        (plain, &[("choose(second, first)", Ok("second"))][..]),
        (
            two_cells,
            &[
                (
                    "vcomp(vcomp(alpha, alpha), alpha)",
                    Ok("vcomp(alpha, vcomp(alpha, alpha))"),
                ),
                (
                    "vcomp(whiskerR(alpha, e), whiskerR(alpha, e))",
                    Err(NormalFormFault::Unsorted(Unsorted::Nested)),
                ),
            ][..],
        ),
    ] {
        lowered(source, |module| {
            let [theory, ..] = *module.declarations().iter().collect::<Vec<_>>()
            else {
                panic!("the theory")
            };
            for &(call, ref reached) in calls {
                assert_eq!(
                    module
                        .normal_form(theory, CallText::from(call))
                        .map(|reached| reached.spelling()),
                    reached.clone().map(String::from),
                    "{call}: the call reads over terms"
                );
            }
        });
    }
    assert_ne!(
        NormalFormFault::Unsorted(Unsorted::Clash).to_string(),
        NormalFormFault::NotACall(ElaborateError::UnsupportedShape).to_string(),
        "an ill-sorted call reads apart from one that does not elaborate"
    );
    assert_ne!(
        NormalFormFault::Unsorted(Unsorted::Nested).to_string(),
        NormalFormFault::Unsorted(Unsorted::Clash).to_string(),
        "an index nesting an indexed operation reads apart from an ill-sorted call"
    );
}

/// #2966: a block holding a rule that instantiates a variable reads a call in
/// the kernel's second-order reading. β fires at a binding field and answers
/// `post(z)`, not the instance `k(z)` the term cells wrote, below a binder
/// too; a rule instantiating a continuation fires beside its block's
/// first-order rule; a binder the normal form keeps reads back at its depth.
#[test]
fn an_instantiating_rule_fires_at_an_inspected_call_2966()
{
    let beta = SourceText::from(
        r#"theory Beta {
  sort V : Type+;
  sort C : Type;
  oper z : () --> V;
  oper post : (v : V) --> C;
  oper app : (k : pi+ (x : V). C, a : V) --> C;
  rule beta : app(k, a) ==> k(a);
}"#,
    );
    let continued = SourceText::from(
        r#"theory Continued {
  sort N : Type;
  sort V : Type+;
  sort E : Type;
  sort C : Type;
  oper z : () --> N;
  oper int : (n : N) --> V;
  oper lit : (n : N) --> E;
  oper ret : (e : E) --> E;
  oper hole : () --> E;
  oper post : (v : V) --> C;
  oper wp : (e : E, k : pi+ (v : V). C, r : pi+ (v : V). C) --> C;
  rule literal : wp(lit(n), k, r) ==> k(int(n));
  rule returned : wp(ret(e), k, r) ==> wp(e, r, r);
}"#,
    );
    for (source, calls) in [
        (
            beta,
            &[
                ("app(bind v . post(v), z)", "post(z)"),
                ("app(bind v . app(bind u . post(u), v), z)", "post(z)"),
            ][..],
        ),
        (
            continued,
            &[
                (
                    "wp(lit(z), bind v . post(v), bind w . post(w))",
                    "post(int(z))",
                ),
                (
                    "wp(ret(lit(z)), bind v . post(v), bind w . post(w))",
                    "post(int(z))",
                ),
                (
                    "wp(ret(hole), bind v . post(v), bind w . post(w))",
                    "wp(hole, bind a0 . post(a0), bind a0 . post(a0))",
                ),
            ][..],
        ),
    ] {
        lowered(source, |module| {
            let [theory, ..] = *module.declarations().iter().collect::<Vec<_>>()
            else {
                panic!("the theory")
            };
            for &(call, normal) in calls {
                let reached = module
                    .normal_form(theory, CallText::from(call))
                    .unwrap_or_else(|fault| panic!("{call}: {fault}"));
                assert_eq!(reached.spelling(), normal, "{call}");
                assert_eq!(
                    reached.path,
                    NormalPath::SecondOrder,
                    "{call}: the kernel's second-order reading fired the rules"
                );
            }
        });
    }
}
