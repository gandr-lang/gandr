use alloc::format;
use alloc::string::String;

use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::hole::HoleOrigin;
use gandr_core_term::tactic::Tactic;
use gandr_surface_syntax::SourceText;

use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::lower::native::tests::assert_checked;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::resolve::SurfaceName;

#[test]
fn a_splice_is_a_hole_carrying_its_tactic_2762()
{
    // A splice whose whole definition it is lowers to the hole its tactic
    // fills, the tactic in the hole's name; the checker answers each.
    let source = "\
def id : (Integer) => Integer = ~intro(assumption) ;
def second : (Integer, Unit) => Integer = ~intro(intro(assumption)) ;
def pick(a : Integer, u : Unit) -> -F Integer { return ~assumption }
";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let [once, twice] = [1_u8, 2].map(|intros| Tactic::try_from(intros).expect("under the limit"));
    for (name, tactic) in [("id", once), ("second", twice)] {
        let body = body_named(&module, SurfaceName::from(name));
        let Some(&Value::Hole(hole)) = arena.value(body)
        else {
            panic!("`{name}` is a hole: {:?}", arena.value(body));
        };
        assert_eq!(
            (hole.origin(), hole.tactic()),
            (HoleOrigin::Spliced, Some(tactic)),
            "`{name}`'s hole carries its tactic"
        );
    }
    assert_checked(&module, &mut arena);
}

#[test]
fn an_operand_writing_no_tactic_is_refused_2762()
{
    // A name other than the two tactics, an `intro` of two arguments, a
    // call of another name, a literal, and an introduction past the limit are
    // each refused at the operand; a splice where a computation is read is of
    // the wrong sort.
    let deep = format!(
        "{}assumption{}",
        "intro(".repeat(usize::from(Tactic::INTROS)),
        ")".repeat(usize::from(Tactic::INTROS)),
    );
    let source = format!(
        "\
def named(x : Integer) -> -F Integer {{ return ~x }}
def pair : (Integer) => Integer = ~intro(assumption, assumption) ;
def other : (Integer) => Integer = ~apply(assumption) ;
def literal : Integer = ~3 ;
def deep : (Integer) => Integer = ~{deep} ;
def head(x : Integer) -> -F Integer {{ become ~assumption }}
"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (name, operand) in [
        ("named", String::from("x }")),
        ("pair", String::from("intro(assumption, assumption)")),
        ("other", String::from("apply(assumption)")),
        ("literal", String::from("3 ;")),
        ("deep", deep),
    ] {
        let refusal = refusal_of(&module, SurfaceName::from(name));
        let LoweringRefusal::UnknownTactic { span } = refusal
        else {
            panic!("`{name}` is refused as no tactic: {refusal:?}");
        };
        assert_eq!(
            usize::from(span.start()),
            source.find(operand.as_str()).unwrap(),
            "`{name}` is refused at its operand"
        );
    }
    let refusal = refusal_of(&module, SurfaceName::from("head"));
    assert!(
        matches!(refusal, LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::WrongSort,
            ..
        }),
        "a splice where a computation is read is of the wrong sort: {refusal:?}"
    );
}
