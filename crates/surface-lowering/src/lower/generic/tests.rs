use alloc::string::String;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::equal_type_syntax;
use gandr_core_term::generic::Uncovered;
use gandr_surface_syntax::SourceText;

use crate::error::LoweringRefusal;
use crate::lower::native::tests::assert_checked;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::preluded;
use crate::lower::native::tests::refusal_of;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::resolve::SurfaceName;
use crate::unit::Unit;

/// A point, unary naturals and a declaration holding a function.
const DATA: &str = "\
data Point : Type { Point : (x : Integer, y : Integer) --> Point; }
data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }
data Shape : Type { Shape : (f : (Integer) => Integer) --> Shape; }
data Box(a : Type) : Type { Box : (x : a) --> Box(a); }
";

/// `source`, after [`DATA`], laid out after the prelude.
///
/// # Specification
/// trivial.
fn laid(source: SourceText<'_>) -> (String, Unit)
{
    let text = alloc::format!("{DATA}{source}");
    crate::prelude::lay(SourceText::from(text.as_str()), &Unit::single()).unwrap()
}

/// The declared type of `name`, which lowers complete.
///
/// # Specification
/// trivial.
fn declared(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> gandr_core_term::ValueTypeId
{
    let outcome = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
        .map(crate::module::LoweredDeclaration::outcome);
    let Some(DeclarationOutcome::Completed { declared_type, .. }) = outcome
    else {
        panic!("`{name:?}` lowers complete: {outcome:?}");
    };
    declared_type
}

#[test]
fn a_generic_equality_lowers_to_the_derived_declaration_2302()
{
    // Unsigned, the derived type stands; signed, the written one, which is
    // the same type. A recursive declaration's equality derives too. The
    // prelude's `Eq.generic` yields no declaration of its own.
    let (text, unit) = laid(SourceText::from(
        "\
def eqPoint = Eq.generic(Point) ;
def stated : (Point, Point) => Bool = Eq.generic(Point) ;
def eqNat = Eq.generic(Nat) ;
",
    ));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    assert!(
        module
            .declarations()
            .iter()
            .all(|declaration| declaration.name() != SurfaceName::from("generic")),
        "the prelude's derivation is no declaration"
    );
    assert_eq!(
        equal_type_syntax(
            &arena,
            declared(&module, SurfaceName::from("eqPoint")),
            declared(&module, SurfaceName::from("stated"))
        ),
        CertificateEquality::Equal,
        "the derived type is the written one"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_leaf_reads_a_source_s_family_before_the_prelude_s_3287()
{
    // The prelude declares binary naturals as `Nat`. A field naming `Nat` in
    // a source that declares unary naturals as `Nat` reads the source's, as
    // resolution does, so the derived equality compares unary naturals and
    // checks rather than meeting the prelude's at the field.
    let (text, unit) = laid(SourceText::from(
        "\
data Tagged : Type { Tagged : (shown : Bool, count : Nat) --> Tagged; }
def eqTagged = Eq.generic(Tagged) ;
",
    ));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    assert_checked(&module, &mut arena);
}

#[test]
fn a_derived_law_lowers_to_its_proof_2302()
{
    // A point's laws, alone and as a model's members: each proof checks
    // against its own derived statement, and the model's against `Eq`'s, so
    // `==` reaches points through it.
    let (text, unit) = laid(SourceText::from(
        "\
def reflPoint = Eq.generic.refl(Point) ;
def symPoint = Eq.generic.sym(Point) ;
module EqPoint : Model(Eq) with sort Carrier = Point {
  def eq = Eq.generic(Point) ;
  def refl = Eq.generic.refl(Point) ;
  def sym = Eq.generic.sym(Point) ;
}
def same() -> Bool { Point(1, 2) == Point(1, 2) }
",
    ));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    for name in ["reflPoint", "symPoint"] {
        let _stated = declared(&module, SurfaceName::from(name));
    }
    assert_checked(&module, &mut arena);
}

/// Each data case a derived equality holds names the declaration it
/// eliminates, as a written `case` does, so a printer reads its branches as
/// that declaration's constructors (#2363): naturals case on the first side,
/// then on the second under each of its two constructors.
#[test]
fn a_generic_equality_names_the_declaration_each_case_eliminates_2363()
{
    let (text, unit) = laid(SourceText::from("def eqNat = Eq.generic(Nat) ;\n"));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    // The source's own naturals, declared after the prelude's binary `Nat`.
    let nat = module
        .declarations()
        .iter()
        .rev()
        .find(|declaration| declaration.name() == SurfaceName::from("Nat"))
        .map(crate::module::LoweredDeclaration::constant)
        .expect("the naturals are declared");
    assert_eq!(
        module
            .origins()
            .eliminations()
            .filter(|&(_, family)| family == nat)
            .count(),
        3,
        "every case of the derived equality names the naturals"
    );
}

#[test]
fn a_source_s_own_eq_module_is_no_derivation_2302()
{
    // With no prelude, `Eq.generic` is whatever the source declares.
    let source = "\
module Eq { def generic(a : Integer) -> -F Integer { return a } }
def one() -> -F Integer { Eq.generic(1) }
";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert_checked(&module, &mut arena);
}

#[test]
fn a_misplaced_generic_is_refused_at_the_call_2302()
{
    // Inside a larger body, at a type that is no data declaration, and read
    // as a value, each refused at the form.
    let (text, unit) = laid(SourceText::from(
        "\
def inside() -> Bool { Eq.generic(Point)(Point(1, 2), Point(1, 2)) }
def integers = Eq.generic(Integer) ;
def bare = Eq.generic ;
def reflIntegers = Eq.generic.refl(Integer) ;
",
    ));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    for (name, written) in [
        ("inside", "Eq.generic(Point)"),
        ("integers", "Eq.generic(Integer)"),
        ("bare", "Eq.generic ;"),
        ("reflIntegers", "Eq.generic.refl(Integer)"),
    ] {
        let refusal = refusal_of(&module, SurfaceName::from(name));
        let LoweringRefusal::GenericMisplaced { span } = refusal
        else {
            panic!("`{name}` is refused misplaced: {refusal:?}");
        };
        // The source follows the prelude, whose own docs spell the call.
        let at = text.rfind(written).unwrap();
        assert_eq!(
            usize::from(span.start()),
            at,
            "`{name}` is refused at the form"
        );
    }
}

#[test]
fn an_uncovered_declaration_is_refused_at_its_name_2302()
{
    // A function field has no equality; a declaration with parameters is
    // not yet covered; the naturals' reflexivity is an induction. Each is
    // refused at the name of the type.
    let (text, unit) = laid(SourceText::from(
        "\
def shapes = Eq.generic(Shape) ;
def boxes = Eq.generic(Box) ;
def reflNats = Eq.generic.refl(Nat) ;
",
    ));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    for (name, data, written) in [
        ("shapes", "Shape", "(Shape)"),
        ("boxes", "Box", "(Box)"),
        ("reflNats", "Nat", "(Nat)"),
    ] {
        let refusal = refusal_of(&module, SurfaceName::from(name));
        let LoweringRefusal::GenericUncovered {
            span,
            data: named,
            fault,
        } = refusal
        else {
            panic!("`{name}` is refused uncovered: {refusal:?}");
        };
        assert_eq!(named, SurfaceName::from(data));
        assert_eq!(
            usize::from(span.start()),
            text.rfind(written).unwrap().saturating_add(1),
            "`{name}` is refused at `{data}`"
        );
        match name {
            "shapes" => assert!(matches!(fault, Uncovered::Field(..)), "{fault:?}"),
            "boxes" => assert!(matches!(fault, Uncovered::Applied(_)), "{fault:?}"),
            _ => assert!(matches!(fault, Uncovered::Inductive(..)), "{fault:?}"),
        }
    }
}
