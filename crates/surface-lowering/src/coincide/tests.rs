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
        let family = &module.declarations()[0];
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
                | Maybe::Present(term) => term.to_string(),
                | Maybe::Absent(reason) => panic!("a peak spells a term: {reason:?}"),
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
        let family = &module.declarations()[0];
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
            "rule Unloop(Loop(x)) ==> x",
            "and names the cancellation it parts from"
        );
        assert_eq!(
            fault.to_string(),
            "both rules rewrite `Unloop(Loop(Loop(x')))`, one to `Loop(x')` and the other to \
             `Unloop(x')`"
        );
        let [ref family] = *module.declarations()
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
const CIRCLE_SHAPE: &str = r#"sign CircleShape {
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
            | Maybe::Present(term) => term.to_string(),
            | Maybe::Absent(reason) => panic!("a peak spells a term: {reason:?}"),
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
    let faults = lowered(SourceText::from(tampered.as_str()), term_peaks)
        .expect_err("a third law parts the readings");
    assert!(
        matches!(*faults.as_slice(), [CellFault::Coherence(
            CoherenceFault::Diverges { .. }
        )]),
        "the third law diverges: {faults:?}"
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
        let [ref family, ref later] = *module.declarations()
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
            module.declarations()[0].outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesUnoriented {
                span: diagnostic.span
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
        let described = &module.descriptions().declarations[0];
        let printed: Vec<_> = described.rules().map(|rule| rule.print_data()).collect();
        assert_eq!(printed, ["rule x <=> S(P(x))", "rule P(S(x)) <=> x"]);
        assert_eq!(
            described
                .rules()
                .next()
                .unwrap()
                .print_sign(&gandr_theory_levitation::Name::from("cancel")),
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
        let family = &module.declarations()[0];
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
        r#"sign Nat {
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
        let [ref family, ref walk, .., ref later] = *module.declarations()
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
}
