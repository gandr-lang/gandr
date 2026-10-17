use alloc::format;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::SourceText;
use gandr_theory_sites::Degree;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::ShapeSize;

use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::lower::identity::tests::lowered;
use crate::lower::identity::tests::outcome_of;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::judged;
use crate::module::DeclarationOutcome;
use crate::resolve::OperandCount;

/// A magma, the opposite multiplication's translator at its binary corolla
/// and the identity at its constant one.
const MAGMA: &str = r"sign Magma {
  sort M : Type;
  oper mul : (x : M, y : M) --> (z : M);
  oper one : () --> (z : M);
}
def exchange(b : Bool) -> -F Bool {
  case b {
    true => return +{.1 = unit},
    false => return +{.0 = unit}
  }
}
def keep(e : +{Unit}) -> -F +{Unit} {
  return e
}
";

/// Text a fixture spells: a statement or a label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spelled<'text>(&'text str);

/// The input and output leg counts of a corolla.
#[derive(Clone, Copy, Debug)]
struct Legs(usize, usize);

/// The outcome of the declaration `statement` names after [`MAGMA`].
///
/// # Specification
/// trivial.
fn statement(
    Spelled(statement): Spelled<'_>,
    arena: &mut CoreArena,
) -> DeclarationOutcome<'static>
{
    let source = format!("{MAGMA}def opposite = {statement};\n").leak();
    outcome_of(
        &lowered(SourceText::from(&*source), arena),
        "opposite".into(),
    )
}

/// The profile of a corolla with the legs `legs` counts.
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

/// The field label `text` spells.
///
/// # Specification
/// trivial.
fn label(Spelled(text): Spelled<'_>) -> FieldLabel
{
    FieldLabel::from(alloc::string::String::from(text))
}

#[test]
fn a_statement_lowers_to_univalence_at_its_stratum()
{
    let mut arena = CoreArena::new();
    let source = format!(
        "{MAGMA}def opposite = ua[1, 4](Magma, Magma, #{{mul = exchange, one = keep}}, #{{mul = exchange, one = keep}});\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let outcome = outcome_of(&module, "opposite".into());
    let DeclarationOutcome::Bodied { body } = outcome
    else {
        panic!("the statement lowers: {outcome:?}");
    };
    let Some(&Value::Ua {
        stratum,
        ref sides,
        forward,
        backward,
    }) = arena.value(body)
    else {
        panic!("`ua[1, 4](…)` is univalence at a stratum");
    };
    assert_eq!(stratum, Stratum {
        degree: Degree::from(1_usize),
        bound: ShapeSize::from(4_usize),
    });
    let read: Vec<_> = sides
        .source
        .generators
        .iter()
        .map(|generator| (generator.label.clone(), generator.profile))
        .collect();
    assert_eq!(
        read,
        [
            (label(Spelled("mul")), profile(Legs(2, 1))),
            (label(Spelled("one")), profile(Legs(0, 1))),
        ],
        "the description's generators, in written order, at their corollas"
    );
    assert_eq!(sides.source, sides.target);
    for record in [forward, backward] {
        assert!(
            matches!(
                arena.value(record),
                Some(Value::Record(fields))
                    if fields.keys().eq([&label(Spelled("mul")), &label(Spelled("one"))])
            ),
            "each translator record keeps its labels"
        );
    }
    let starts = module
        .origins()
        .sides()
        .iter()
        .find(|&&(statement, _)| statement == body)
        .map(|&(_, named)| named.map(|origin| usize::from(origin.span().start())));
    let first = source
        .find("(Magma")
        .expect("the call names its sides")
        .saturating_add(1);
    assert_eq!(
        starts,
        Some([first, first.saturating_add("Magma, ".len())]),
        "each description is named where it is written, the source's first"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    assert!(
        report.natives().contains_key(&body),
        "the checker derives the statement's path"
    );
}

#[test]
fn a_statement_the_syntax_cannot_read_is_refused()
{
    let refused = |written: &str| {
        let mut arena = CoreArena::new();
        match statement(Spelled(written), &mut arena) {
            DeclarationOutcome::Refused(refusal) => refusal,
            other @ (DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World) => panic!("`{written}` is refused: {other:?}"),
        }
    };
    let records = "#{mul = exchange, one = keep}";
    assert!(matches!(
        refused(&format!("ua[1](Magma, Magma, {records}, {records})")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Arity(count),
            ..
        } if count == OperandCount::from(1_usize)
    ));
    assert!(matches!(
        refused(&format!(
            "ua[1, Integer](Magma, Magma, {records}, {records})"
        )),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unadmitted,
            ..
        }
    ));
    assert!(matches!(
        refused(&format!("ua[1, 4](Magma, Magma, {records})")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Arity(count),
            ..
        } if count == OperandCount::from(3_usize)
    ));
    assert!(matches!(
        refused(&format!("ua[1, 4](Monoid, Magma, {records}, {records})")),
        LoweringRefusal::UnresolvedName { name, .. } if name.as_ref() == "Monoid"
    ));
}

/// #633: a module member named `ua`, declared after a statement that writes
/// `ua[n, k]`, is a forward reference at the name, as a later `here` is.
#[test]
fn a_later_member_named_ua_is_a_forward_reference()
{
    let source = "sign S { sort M : Type; }\nmodule M { def o = ua[1, 4](S, S, #{}, #{}); def ua = 1; \
                  }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let refused = outcome_of(&module, "o".into());
    let DeclarationOutcome::Refused(LoweringRefusal::ForwardMemberReference { span, name, .. }) =
        refused
    else {
        panic!("the statement names the later member: {refused:?}");
    };
    assert_eq!(
        (
            source.get(usize::from(span.start()) .. usize::from(span.end())),
            name.as_ref()
        ),
        (Some("ua"), "ua"),
        "the refusal stands at the name the statement writes"
    );
}

#[test]
fn a_description_outside_the_stratum_is_refused_at_its_name()
{
    for (sign, name) in [
        (
            "sign Two {\n  sort Ob : Type;\n  sort Ar : Type;\n  oper f : (a : Ob) --> (b : Ob);\n}\n",
            "Two",
        ),
        (
            "sign Old {\n  sort Nat : Type;\n  oper f(x : Nat) -> Nat;\n  oper g : (a : Nat) --> (b : Nat);\n}\n",
            "Old",
        ),
    ] {
        let mut arena = CoreArena::new();
        let source = format!(
            "{MAGMA}{sign}def opposite = ua[1, 4](Magma, {name}, #{{mul = exchange}}, #{{f = exchange}});\n"
        );
        let module = lowered(SourceText::from(source.as_str()), &mut arena);
        let refused = outcome_of(&module, "opposite".into());
        let DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
            span,
            boundary: FragmentBoundary::Unadmitted,
            ..
        }) = refused
        else {
            panic!("`{name}` is refused at its name: {refused:?}");
        };
        assert_eq!(
            source.get(usize::from(span.start()) .. usize::from(span.end())),
            Some(name),
            "the refusal names the description"
        );
    }
}
