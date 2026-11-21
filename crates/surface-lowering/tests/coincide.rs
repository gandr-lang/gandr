//! A block's rules decided as one rewriting system, read where the lowering
//! answers for them: a block whose rules part refuses its family under the
//! family's own name, and a call reads its normal form through the lowered
//! module. The cases that read the decision alone are in the base crate's
//! integration target, `tests::coincide`.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_lowering::coincide::CoherenceFault;
use gandr_surface_lowering::coincide::Coincidence;
use gandr_surface_lowering::coincide::NormalFormFault;
use gandr_surface_lowering::desc_cells::CellDiagnosticIndex;
use gandr_surface_lowering::desc_cells::CellFault;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_theory_computads::ElaborateError;

/// Lower `source` and hand the module to `inspect`.
///
/// # Specification
/// trivial.
fn lowered<R>(
    source: SourceText<'_>,
    inspect: impl FnOnce(&LoweredModule<'_>) -> R,
) -> R
{
    let grammar = built_in().unwrap();
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
fn two_rules_rewriting_one_term_apart_refuse_the_block()
{
    let source = SourceText::from(include_str!(
        "coincide/unformatted/two-rules-rewriting-one-term-apart-refuse-the-block.gandr"
    ));
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
            "rule : add m Zero ==> Succ m",
            "the refusal stands at the later rule"
        );
        assert_eq!(
            text(source, first).as_ref(),
            "rule : add Zero n ==> n",
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

#[test]
fn a_call_reads_its_normal_form_or_says_why_not()
{
    let source = SourceText::from(include_str!(
        "../../surface-lowering-base/src/coincide/tests/unformatted/a-call-reads-its-normal-form-or-says-why-not.gandr"
    ));
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
    let restriction = SourceText::from(include_str!(
        "../../surface-lowering-base/src/coincide/tests/unformatted/a-call-reads-its-normal-form-or-says-why-not-restriction.gandr"
    ));
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
