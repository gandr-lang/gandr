//! The model signature a theory's presentation derives, read back component by
//! component.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::ConstructorTag;
use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::Payload;
use gandr_theory_levitation::TheoryFault;
use gandr_theory_levitation::TheoryValue;
use quenchant_shape::shape::Maybe;

use super::Binder;
use super::ModelFault;
use super::ModelForm;
use super::ModelSignature;
use super::Presentation;
use super::PresentationFault;
use super::SortTerm;
use super::derive;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::unit::Unit;

/// The theory the flagship model signature is derived from.
const CAT_SHAPE: &str = r"theory CatShape {
  sort Ob : Type;
  sort Hom(dom: Ob, cod: Ob) : Type;

  oper id : (a : Ob) --> Hom(a, a);
  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);

  rule unitL : comp(id(a), f) ==> f;
  rule unitR : comp(f, id(b)) ==> f;
  rule assoc : comp(comp(f, g), h) ==> comp(f, comp(g, h));
}";

/// The presentation of the one theory `source` declares.
///
/// # Specification
/// trivial.
fn presented<'source, Text>(source: Text) -> Presentation
where
    Text: Into<SourceText<'source>>,
{
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    let [ref theory] = *report.declarations.as_slice()
    else {
        panic!("one theory declared");
    };
    let Maybe::Present(ref presentation) = theory.presentation
    else {
        panic!("a theory presents its members");
    };
    presentation.clone()
}

/// The model signature of the one theory `source` declares.
///
/// # Specification
/// trivial.
fn derived<'source, Text>(source: Text) -> ModelSignature
where
    Text: Into<SourceText<'source>>,
{
    derive(&presented(source)).unwrap()
}

/// A sort term as the surface spells it.
///
/// # Specification
/// trivial.
fn sort(term: &SortTerm) -> String
{
    if term.indices.is_empty() {
        return format!("{}", term.sort);
    }
    let indices: Vec<String> = term
        .indices
        .iter()
        .map(|index| format!("{index}"))
        .collect();
    format!("{}({})", term.sort, indices.join(", "))
}

/// A telescope as the surface spells it.
///
/// # Specification
/// trivial.
fn telescope(binders: &[Binder]) -> String
{
    let entries: Vec<String> = binders
        .iter()
        .map(|binder| format!("{} : {}", binder.name, sort(&binder.sort)))
        .collect();
    format!("({})", entries.join(", "))
}

/// The component named `name`, spelled as the surface would write its type.
///
/// # Specification
/// trivial.
fn spelled<Named>(
    model: &ModelSignature,
    name: Named,
) -> String
where
    Named: AsRef<str>,
{
    let name = name.as_ref();
    let component = model
        .components
        .iter()
        .find(|component| component.name.as_ref() == name)
        .unwrap_or_else(|| panic!("`{name}` is a component"));
    match component.form {
        Ok(ModelForm::Sort { ref indices }) => {
            format!("type {name} : {} => Type", telescope(indices))
        },
        Ok(ModelForm::Operation {
            telescope: ref binders,
            ref results,
        }) => {
            let results: Vec<String> = results.iter().map(sort).collect();
            format!("{name} : {} => {}", telescope(binders), results.join(" * "))
        },
        Ok(ModelForm::Constant(ref of)) => format!("{name} : {}", sort(of)),
        Ok(ModelForm::Nested(ref theory)) => format!("{name} : Model({theory})"),
        Ok(ModelForm::Law {
            telescope: ref binders,
            ref carrier,
            ref left,
            ref right,
        }) => format!(
            "{name} : {} => Path({}, {left}, {right})",
            telescope(binders),
            sort(carrier)
        ),
        Err(fault) => format!("{name} refused: {fault:?}"),
    }
}

#[test]
fn the_cat_shape_sorts_are_a_type_and_a_family()
{
    let model = derived(CAT_SHAPE);

    let names: Vec<&str> = model
        .components
        .iter()
        .map(|component| component.name.as_ref())
        .collect();
    assert_eq!(
        names,
        ["Ob", "Hom", "id", "comp", "unitL", "unitR", "assoc"],
        "sorts, then operations, then laws, each in written order"
    );
    assert_eq!(
        spelled(&model, "Ob"),
        "type Ob : () => Type",
        "an unindexed sort"
    );
    assert_eq!(
        spelled(&model, "Hom"),
        "type Hom : (dom : Ob, cod : Ob) => Type",
        "an indexed sort is a family over its index telescope"
    );
}

/// A constant, `oper zero : T`, derives a value of its type alone, a sort of
/// the theory or a builtin type; `oper one : () --> T`, an operation of no
/// inputs, derives a function of none; and a constant whose type leaves a
/// variable free binds it as an operation does.
#[test]
fn a_constant_derives_its_type_alone()
{
    let model = derived(
        r"theory Pointed {
  sort Ob : Type;
  sort Hom(dom: Ob, cod: Ob) : Type;
  oper zero : Ob;
  oper one : () --> Ob;
  oper base : Integer;
  oper loop : Hom(a, a);
}",
    );

    assert_eq!(
        [
            spelled(&model, "zero"),
            spelled(&model, "one"),
            spelled(&model, "base"),
            spelled(&model, "loop"),
        ],
        [
            "zero : Ob",
            "one : () => Ob",
            "base : Integer",
            "loop : (a : Ob) => Hom(a, a)",
        ],
    );
}

#[test]
fn the_cat_shape_operations_bind_their_free_sorts_first()
{
    let model = derived(CAT_SHAPE);

    assert_eq!(
        spelled(&model, "id"),
        "id : (a : Ob) => Hom(a, a)",
        "a port the result names is the operation's only binder"
    );
    assert_eq!(
        spelled(&model, "comp"),
        "comp : (a : Ob, b : Ob, c : Ob, f : Hom(a, b), g : Hom(b, c)) => Hom(a, c)",
        "the free sort variables bind first, sorted by the index they stand at"
    );
}

#[test]
fn the_cat_shape_laws_relate_elaborated_terms()
{
    let model = derived(CAT_SHAPE);

    assert_eq!(
        spelled(&model, "unitL"),
        "unitL : (a : Ob, b : Ob, f : Hom(a, b)) => Path(Hom(a, b), comp(a, a, b, id(a), f), f)",
        "an index no term writes takes the first letter the rule leaves free"
    );
    assert_eq!(
        spelled(&model, "unitR"),
        "unitR : (a : Ob, b : Ob, f : Hom(a, b)) => Path(Hom(a, b), comp(a, b, b, f, id(b)), f)",
        "a written index keeps its name and its place in the walk"
    );
    assert_eq!(
        spelled(&model, "assoc"),
        "assoc : (a : Ob, b : Ob, c : Ob, d : Ob, f : Hom(a, b), g : Hom(b, c), h : Hom(c, d)) \
         => Path(Hom(a, d), comp(a, c, d, comp(a, b, c, f, g), h), comp(a, b, d, f, comp(b, c, \
         d, g, h)))",
        "the indices bind in the order the written variables' sorts meet them"
    );
}

#[test]
fn an_underivable_component_keeps_its_fault()
{
    let model = derived(
        r"theory Faulty {
  sort Ob : Type;
  sort Hom(dom: Ob, cod: Ob) : Type;
  sort Tm : Type+;
  oper id : (a : Ob) --> Hom(a, a);
  oper split : (a : Ob) --> (l : Ob, r : Ob);
  oper lam : (t : pi+ (x : Tm) . Tm) --> Tm;
  rule twice : id(id(a)) ==> id(a);
  rule loose : x ==> x;
  rule halves : split(a) ==> split(a);
  rule wired : (data x : Ob) ==> (o : Hom(x, x)) {
    node w : id(x) --> (o);
  };
}",
    );

    assert_eq!(
        spelled(&model, "twice"),
        "twice refused: IllSorted",
        "an argument at a sort its port does not read"
    );
    assert_eq!(
        spelled(&model, "loose"),
        "loose refused: Unsorted",
        "a variable no occurrence sorts"
    );
    assert_eq!(
        spelled(&model, "halves"),
        "halves refused: ManyOut",
        "a term relating a many-out operation's results"
    );
    assert_eq!(
        spelled(&model, "split"),
        "split : (a : Ob) => Ob * Ob",
        "a many-out operation itself returns one sort per output"
    );
    assert_eq!(
        spelled(&model, "wired"),
        "wired refused: Circuit",
        "a circuit rule is kept by name"
    );
    assert_eq!(
        spelled(&model, "lam"),
        "lam refused: Binding",
        "an operation whose port binds a variable"
    );
    assert!(
        model
            .components
            .iter()
            .all(|component| component.form != Err(ModelFault::Inherited)),
        "no component names a refused one"
    );
}

#[test]
fn a_term_at_another_sort_or_inside_its_own_index_is_ill_sorted()
{
    let model = derived(
        r"theory Mixed {
  sort Ob : Type;
  sort Pt : Type;
  sort Hom(dom: Ob, cod: Ob) : Type;
  oper flip : (x : Ob) --> (y : Pt);
  oper succ : (x : Ob) --> (y : Ob);
  oper pred : (x : Ob) --> (y : Ob);
  oper diag : (f : Hom(c, d)) --> Hom(d, d);
  oper down : (x : Ob) --> Hom(x, pred(x));
  oper back : (f : Hom(a, succ(a))) --> (z : Ob);
  rule mixed : flip(flip(x)) ==> flip(x);
  rule cyc : back(diag(h)) ==> back(diag(h));
  rule skew : back(down(o)) ==> o;
}",
    );

    assert_eq!(
        spelled(&model, "mixed"),
        "mixed refused: IllSorted",
        "an argument at another sort of as many indices"
    );
    assert_eq!(
        spelled(&model, "cyc"),
        "cyc refused: IllSorted",
        "an implicit object that would be its own successor"
    );
    assert_eq!(
        spelled(&model, "skew"),
        "skew refused: IllSorted",
        "an index naming another operation of as many arguments"
    );
}

#[test]
fn a_result_sort_indexed_by_an_operation_instantiates_at_each_use()
{
    let model = derived(
        r"theory Stepped {
  sort Ob : Type;
  sort Hom(dom: Ob, cod: Ob) : Type;
  oper next : (a : Ob) --> Ob;
  oper step : (a : Ob) --> Hom(a, next(a));
  rule again : step(a) ==> step(a);
}",
    );
    assert_eq!(
        spelled(&model, "again"),
        "again : (a : Ob) => Path(Hom(a, next(a)), step(a), step(a))",
        "an index the result sort writes as an application instantiates at the call's argument, \
         and the two sides' indices unify application against application"
    );
}

#[test]
fn an_implicit_object_past_the_last_free_letter_is_numbered()
{
    let morphisms: Vec<String> = ('n' ..= 'z').map(String::from).collect();
    let mut left = morphisms.first().cloned().unwrap_or_default();
    for morphism in morphisms.iter().skip(1) {
        left = format!("comp({left}, {morphism})");
    }
    let mut right = morphisms.last().cloned().unwrap_or_default();
    for morphism in morphisms.iter().rev().skip(1) {
        right = format!("comp({morphism}, {right})");
    }
    let model = derived(format!(
        "theory Long {{\n  sort Ob : Type;\n  sort Hom(dom: Ob, cod: Ob) : Type;\n  oper comp : (f : \
         Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  rule chain : {left} ==> {right};\n}}"
    ).as_str());
    let law = spelled(&model, "chain");
    assert!(
        law.starts_with(
            "chain : (a : Ob, b : Ob, c : Ob, d : Ob, e : Ob, f : Ob, g : Ob, h : Ob, i : Ob, j : \
             Ob, k : Ob, l : Ob, m : Ob, x0 : Ob, n : Hom(a, b)"
        ) && law.contains("z : Hom(m, x0)) => Path(Hom(a, x0), "),
        "the thirteen letters the morphisms leave free name the first objects, and the \
         fourteenth takes `x0`: {law}"
    );
}

#[test]
fn a_presentation_reads_its_members_off_its_value()
{
    let presentation = presented(CAT_SHAPE);
    let members = presentation.members().unwrap();
    let [ref id, ref comp] = *members.operations.as_slice()
    else {
        panic!("two operations: {:?}", members.operations);
    };
    let names = |ports: &[super::Port]| -> Vec<String> {
        ports.iter().map(|port| format!("{}", port.name)).collect()
    };
    assert_eq!(
        (names(&id.inputs), names(&id.outputs)),
        (vec![String::from("a")], vec![String::from("_1")]),
        "an unnamed output reads as the placeholder of its position"
    );
    assert_eq!(
        (names(&comp.inputs), names(&comp.outputs)),
        (vec![String::from("f"), String::from("g")], vec![
            String::from("_2")
        ]),
        "positions count the inputs first"
    );
    assert_eq!(
        members
            .laws
            .iter()
            .map(|law| format!("{} : {} ==> {}", law.name, law.left, law.right))
            .collect::<Vec<_>>(),
        [
            "unitL : comp(id(a), f) ==> f",
            "unitR : comp(f, id(b)) ==> f",
            "assoc : comp(comp(f, g), h) ==> comp(f, comp(g, h))"
        ],
        "each face is the value's two terms"
    );

    for (short, kind) in [
        {
            let mut short = presentation.clone();
            let _dropped = short.placement.sorts.pop();
            (short, "sort")
        },
        {
            let mut short = presentation.clone();
            let _dropped = short.placement.operations.pop();
            (short, "operation")
        },
        {
            let mut short = presentation.clone();
            let _dropped = short.placement.laws.pop();
            (short, "law")
        },
    ] {
        assert_eq!(
            short.members(),
            Err(PresentationFault::Unplaced),
            "a {kind} the placement does not place"
        );
    }

    let mut ended = presentation;
    ended.value = TheoryValue::from_value(DescValue::new(
        ConstructorTag::from(1_usize),
        Payload::unit(),
    ));
    assert_eq!(
        ended.members(),
        Err(PresentationFault::Value(TheoryFault::Misplaced(
            ConstructorTag::from(1_usize)
        ))),
        "a value that codes no presentation"
    );
    assert_eq!(
        derive(&ended).map(|model| model.components.len()),
        Err(PresentationFault::Value(TheoryFault::Misplaced(
            ConstructorTag::from(1_usize)
        ))),
        "and derives no model"
    );
}
