//! The rewrites between the explicit and the sugared spellings through the
//! formatter's public surface: each pair both ways, comments kept with the
//! construct they annotate, the declared form over the option, a selection
//! by name, and the corpus formatted into either form — a sample on every
//! pull request, every source under the `sweeps` profile.

use expect_test::expect;
use gandr_surface_format::Beside;
use gandr_surface_format::Form;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::Formatted;
use gandr_surface_format::RewriteName;
use gandr_surface_format::Selection;
use gandr_surface_format::Withdrawn;
use gandr_surface_format::format;
use gandr_surface_format::format_beside;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;

/// Every pair of the table in the explicit spelling, nested and
/// parenthesised where the sugar needs it.
const EXPLICIT: &str = "\
def pair : #{Integer, String} ;
def triple : #{Integer, String, Unit} ;
def choice : +{Integer, #{String, Unit}} ;
def nested : #{+{Integer, String}, Unit} ;
def lazy : +U &{-F Integer, &{-F Integer, -F String}} ;
def mixed : +U &{&{-F Integer, -F Integer}, -F String} ;
def step : +U (Integer -> String -> -F Unit) ;
def dependent : +U ((a : Type) -> a -> -F a) ;
def thunked : +U (-F Integer) ;
def returned : +U (Integer -> -F #{Integer, String}) ;
def tuple = #{1, #{2, \"b\"}} ;
";

/// [`EXPLICIT`] in the sugared spelling, as the presentation printer
/// parenthesises it.
const SUGARED: &str = "\
def pair : Integer * String ;
def triple : Integer * String * Unit ;
def choice : Integer + String * Unit ;
def nested : (Integer + String) * Unit ;
def lazy : +U (-F Integer & -F Integer & -F String) ;
def mixed : +U ((-F Integer & -F Integer) & -F String) ;
def step : (Integer, String) => Unit ;
def dependent : (a : Type, a) => a ;
def thunked : () => Integer ;
def returned : Integer => Integer * String ;
def tuple = (1, (2, \"b\")) ;
";

/// The built-in grammar.
///
/// # Specification
/// trivial.
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// `source` formatted under `form` and `rewrites`.
///
/// # Specification
/// trivial.
fn spelled<'text>(
    grammar: &Pbg,
    source: impl Into<SourceText<'text>>,
    form: Form,
    rewrites: Selection,
) -> String
{
    let parsed = parse(grammar, source.into()).expect("the source parses");
    let options = FormatOptions {
        form,
        rewrites,
        ..FormatOptions::default()
    };
    format(grammar, &parsed, options).map_or_else(
        |error| panic!("the source formats as {form}: {error}"),
        Formatted::into_text,
    )
}

/// Each rewrite moves its pair both ways, and each spelling is the one its
/// form keeps.
#[test]
fn each_rewrite_moves_its_pair_both_ways()
{
    let grammar = grammar();
    for (source, form, expected) in [
        (EXPLICIT, Form::Sugared, SUGARED),
        (SUGARED, Form::Explicit, EXPLICIT),
        (SUGARED, Form::Sugared, SUGARED),
        (EXPLICIT, Form::Explicit, EXPLICIT),
    ] {
        assert_eq!(
            spelled(&grammar, source, form, Selection::Every),
            expected,
            "{form}"
        );
    }
}

/// The circle the path-composite goldens compose its loop in.
const CIRCLE: &str = "\
data Circle : Type {
  Base : Circle;
  loop : Base <-> Base;
}

";

/// The path composite moves both ways, nested: desugared, each composite is
/// the transport whose motive the lowering derived, spelled as the printer
/// spells it; sugared back, the transport is the composite again.
#[test]
fn the_path_composite_moves_both_ways()
{
    let grammar = grammar();
    let sugared = format!(
        "{CIRCLE}def thrice : Path(Path(Circle, Base, Base), loop then (loop then loop), here(Base)) ;\n"
    );
    let explicit = format!(
        "{CIRCLE}def thrice : Path(
  Path(Circle, Base, Base),
  transport(\\a. Path(Circle, Base, a), transport(\\a. Path(Circle, Base, a), loop, loop), loop),
  here(Base)
) ;
"
    );
    let back = format!(
        "{CIRCLE}def thrice : Path(
  Path(Circle, Base, Base),
  loop then (loop then loop),
  here(Base)
) ;
"
    );
    for (source, form, expected) in [
        (&sugared, Form::Explicit, &explicit),
        (&explicit, Form::Sugared, &back),
        (&back, Form::Sugared, &back),
        (&explicit, Form::Explicit, &explicit),
    ] {
        assert_eq!(
            spelled(&grammar, source.as_str(), form, Selection::Every),
            *expected,
            "{form}"
        );
    }
}

/// #778: an inverse and a map's action on a path move both ways as the
/// composite does: desugared, each is the transport whose motive and moved
/// reflexivity the lowering derived, spelled as the printer spells them;
/// sugared back, the transport is the operation again, the map as written.
/// The inverse is taken of a parameter: at the circle's point `here(Base)`
/// reads as the empty word, which no derived inverse moves.
#[test]
fn an_inverse_and_an_action_on_a_path_move_both_ways_778()
{
    let grammar = grammar();
    let sugared = format!(
        "{CIRCLE}def spin(x : Circle) -> -F Circle {{
  x
}}

def undone(x : Circle, p : Path(Circle, x, Base)) -> -F Path(Path(Circle, Base, x), back(p), back(p)) {{
  here(back(p))
}}

def spun : Path(Path(Circle, Base, Base), cong(spin, loop), cong(spin, loop)) ;
"
    );
    let explicit = format!(
        "{CIRCLE}def spin(x : Circle) -> -F Circle {{
  x
}}

def undone(x : Circle, p : Path(Circle, x, Base)) -> -F Path(
  Path(Circle, Base, x),
  transport(\\a. Path(Circle, a, x), p, here(x)),
  transport(\\a. Path(Circle, a, x), p, here(x))
) {{
  here(transport(\\a. Path(Circle, a, x), p, here(x)))
}}

def spun : Path(
  Path(Circle, Base, Base),
  transport(\\a. Path(Circle, spin(Base), spin(a)), loop, here(spin(Base))),
  transport(\\a. Path(Circle, spin(Base), spin(a)), loop, here(spin(Base)))
) ;
"
    );
    let back = format!(
        "{CIRCLE}def spin(x : Circle) -> -F Circle {{
  x
}}

def undone(x : Circle, p : Path(Circle, x, Base)) -> -F Path(
  Path(Circle, Base, x),
  back(p),
  back(p)
) {{
  here(back(p))
}}

def spun : Path(
  Path(Circle, Base, Base),
  cong(spin, loop),
  cong(spin, loop)
) ;
"
    );
    for (source, form, expected) in [
        (&sugared, Form::Explicit, &explicit),
        (&explicit, Form::Sugared, &back),
        (&back, Form::Sugared, &back),
        (&explicit, Form::Explicit, &explicit),
    ] {
        assert_eq!(
            spelled(&grammar, source.as_str(), form, Selection::Every),
            *expected,
            "{form}"
        );
    }
}

/// A transport standing as a computation keeps its spelling sugared, with
/// nothing withdrawn: the printer writes `then` only for the transport the
/// lowering returns at a composite, and spells one a body runs as written.
#[test]
fn a_transport_standing_as_a_computation_keeps_its_spelling()
{
    let grammar = grammar();
    let source = format!(
        "{CIRCLE}def twice(p: Path(Circle, Base, Base)) -> -F Path(Circle, Base, Base) {{
  transport(\\a. Path(Circle, Base, a), p, p)
}}
"
    );
    let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    assert_eq!(formatted.into_text(), source);
}

/// #803: a composite's motive names the binders around it, here the
/// parameter `x`, so the explicit form spells the motive under the names the
/// source writes for them and writes the composite as its transport, in a
/// body and in a type alike, with nothing withdrawn.
#[test]
fn a_composite_under_a_parameter_takes_its_motive_803()
{
    let grammar = grammar();
    let source = format!(
        "{CIRCLE}def onward(x: Circle, q: Path(Circle, x, Base)) -> -F Path(Circle, x, Base) {{
  q then here(Base)
}}

def stated(x: Circle, q: Path(Circle, x, Base)) -> -F Path(Path(Circle, x, Base), q then here(Base), q then here(Base)) {{
  here(q then here(Base))
}}
"
    );
    let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    expect![[r#"
        data Circle : Type {
          Base : Circle;
          loop : Base <-> Base;
        }

        def onward(x: Circle, q: Path(Circle, x, Base)) -> -F Path(Circle, x, Base) {
          transport(\a. Path(Circle, x, a), here(Base), q)
        }

        def stated(x: Circle, q: Path(Circle, x, Base)) -> -F Path(
          Path(Circle, x, Base),
          transport(\a. Path(Circle, x, a), here(Base), q),
          transport(\a. Path(Circle, x, a), here(Base), q)
        ) {
          here(transport(\a. Path(Circle, x, a), here(Base), q))
        }
    "#]]
    .assert_eq(formatted.text().as_ref());
}

/// #803: a composite of types, its carrier `Type`, which the grammar keeps as
/// the path type's own tile, sugars back from its transport as any other.
#[test]
fn a_composite_of_types_sugars_back_803()
{
    let grammar = grammar();
    let source = "def joined(a: Type, b: Type, c: Type, p: Path(Type, a, b), q: Path(Type, b, c)) -> -F \
                  Path(Path(Type, a, c), transport(\\d. Path(Type, a, d), q, p), transport(\\d. \
                  Path(Type, a, d), q, p)) {\n  here(transport(\\d. Path(Type, a, d), q, p))\n}\n";
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    expect![[r#"
        def joined(a: Type, b: Type, c: Type, p: Path(Type, a, b), q: Path(Type, b, c)) -> -F Path(
          Path(Type, a, c),
          p then q,
          p then q
        ) {
          here(p then q)
        }
    "#]]
    .assert_eq(formatted.text().as_ref());
}

/// The value-function alias is written where the printer writes it: a thunk
/// type standing as a call's argument, a transport's family, keeps its
/// thunk sugared with no rewrite tried and none withdrawn, and one that is a
/// static abstraction's body, a type, takes the alias, nullary among them.
#[test]
fn the_value_function_alias_is_written_where_the_printer_writes_it()
{
    let grammar = grammar();
    let argument = "\
data Nat : Type {
  Zero : Nat;
  Succ : (n : Nat) --> Nat;
}

def kept(a: Nat, b: Nat, q: Path(Nat, a, b)) -> -F Path(Nat, b, a) {
  become transport(
    +U ((y : Nat) -> (z : Path(Nat, a, y)) -> -F Path(Nat, y, a)),
    q,
    here(a),
    here(q),
    here(a)
  )
}
";
    let parsed = parse(&grammar, SourceText::from(argument)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    assert_eq!(formatted.into_text(), argument);
    let explicit = "\
def motive : Type -> Type ;
def motive = \\X. +U (X -> -F X) ;
def suspended : Type -> Type ;
def suspended = \\X. +U (-F X) ;
";
    let sugared = "\
def motive : Type -> Type ;
def motive = \\X. X => X ;
def suspended : Type -> Type ;
def suspended = \\X. () => X ;
";
    for (source, form, expected) in [
        (explicit, Form::Sugared, sugared),
        (sugared, Form::Explicit, explicit),
    ] {
        assert_eq!(
            spelled(&grammar, source, form, Selection::Every),
            expected,
            "{form}"
        );
    }
}

/// #838: a thunk type a body returns takes the value-function alias over
/// one bare domain, as the printer writes it, while one standing as a call's
/// argument, a transport's family, keeps its thunk.
#[test]
fn a_thunk_type_a_body_returns_takes_the_alias_838()
{
    let grammar = grammar();
    let explicit = "\
data Nat : Type {
  Zero : Nat;
  Succ : (n : Nat) --> Nat;
}

def onType(t: Type) -> -F Type {
  return (+U (t -> -F t))
}

def flat(a: Nat, b: Nat, q: Path(Nat, a, b), v: Nat) -> -F Nat {
  become transport(+U (Nat -> -F Nat), q, v, v, v)
}
";
    expect![[r#"
        data Nat : Type {
          Zero : Nat;
          Succ : (n : Nat) --> Nat;
        }

        def onType(t: Type) -> -F Type {
          return (t => t)
        }

        def flat(a: Nat, b: Nat, q: Path(Nat, a, b), v: Nat) -> -F Nat {
          become transport(+U (Nat -> -F Nat), q, v, v, v)
        }
    "#]]
    .assert_eq(&spelled(
        &grammar,
        explicit,
        Form::Sugared,
        Selection::Every,
    ));
}

/// An explicit source with comments inside its declarations, sugared: each
/// comment stays in its role before or after the construct it annotated.
#[test]
fn a_sugared_source_keeps_every_comment_with_its_construct()
{
    let grammar = grammar();
    let source = "\
/// A choice, the second arm a pair.
def choice : +{Integer, /* a pair */ #{String, Unit}} ;

def both : +U &{
  -F Integer, // eager first
  -F String
} ;

def pair = #{1, /* second */ \"a\"} ;
";
    let sugared = "\
/// A choice, the second arm a pair.
def choice : Integer + /* a pair */ String * Unit ;

def both : +U (
  -F Integer & // eager first
  -F String
) ;

def pair = (1, /* second */ \"a\") ;
";
    assert_eq!(
        spelled(&grammar, source, Form::Sugared, Selection::Every),
        sugared
    );
    assert_eq!(
        spelled(&grammar, sugared, Form::Explicit, Selection::Every),
        source,
        "desugared, the source returns"
    );
}

/// A source's declared form wins over the option, either way.
#[test]
fn a_declared_form_wins_over_the_option()
{
    let grammar = grammar();
    for (declared, asked, written, expected) in [
        (
            "explicit",
            Form::Sugared,
            "Integer * String",
            "#{Integer, String}",
        ),
        (
            "sugared",
            Form::Explicit,
            "#{Integer, String}",
            "Integer * String",
        ),
    ] {
        let source = format!("@[ form({declared}) ]\ndef pair : {written} ;\n");
        assert_eq!(
            spelled(&grammar, source.as_str(), asked, Selection::Every),
            format!("@[ form({declared}) ]\ndef pair : {expected} ;\n"),
            "declared {declared}, asked {asked}"
        );
    }
}

/// #791: a declaration whose sum pattern reads its parameter's stated
/// `+{…}` is sugared like the declaration beside it, and nothing is
/// withdrawn: the lowering reads `A + B` as it reads `+{A, B}`. Before the
/// fix, the sugared match was refused and the declaration kept its spelling.
#[test]
fn a_match_over_a_stated_sum_is_sugared_791()
{
    let grammar = grammar();
    let matched = |stated: &str| {
        format!(
            "def pick(t : {stated}) -> -F Integer {{\n  case t {{\n    +{{.1 = x}} => return x,\n    _ => return 0\n  }}\n}}"
        )
    };
    let source = format!(
        "{}\n\ndef pair : #{{Integer, String}} ;\n",
        matched("+{Integer, Integer}")
    );
    let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(
        (formatted.text().as_ref(), formatted.withdrawn()),
        (
            format!(
                "{}\n\ndef pair : Integer * String ;\n",
                matched("Integer + Integer")
            )
            .as_str(),
            [].as_slice()
        )
    );
}

/// #893: a source holding a body hole beside a declaration the sugared
/// rewrite respells formats, the hole kept: a hole is named by its place
/// among the source's holes, so respelling the declaration beside it no
/// longer renames it. Before the fix, the formatting was refused as a change
/// of meaning.
#[test]
fn a_body_hole_keeps_its_meaning_beside_a_rewrite_893()
{
    let grammar = grammar();
    let source = "data Color : Type {\n  Red : Color;\n  Green : Color;\n}\n\ndef sketch(c : \
                  Color) -> -F Integer {\n  case c {\n    Red => return 0,\n    Green => ?\n  \
                  }\n}\n\ndef pair : #{Integer, String} ;\n";
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(
        (formatted.text().as_ref(), formatted.withdrawn()),
        (
            source
                .replace("#{Integer, String}", "Integer * String")
                .as_str(),
            [].as_slice()
        )
    );
}

/// A source that imports a sibling is lowered beside it: the rewrite whose
/// meaning reads the sibling's declarations applies, where alone the
/// declaration's lowering is refused and it keeps its spelling, reported.
#[test]
fn an_importing_source_is_rewritten_beside_its_imports()
{
    let grammar = grammar();
    let source = "import \"./circle.gandr\" ;\n\ndef twice : Path(Path(Circle, Base, Base), loop then loop, here(Base)) ;\n";
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let unit = Unit::new(Vec::from([
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(
            ByteOffset::from(CIRCLE.len()),
            Vec::from([ImportTarget::Source(SourceIndex::from(0_usize))]),
        ),
    ]))
    .expect("the unit is well formed");
    let beside = Beside::Imports {
        before: SourceText::from(CIRCLE),
        unit: &unit,
    };
    let formatted = format_beside(&grammar, &parsed, options, beside)
        .unwrap_or_else(|error| panic!("the source formats beside its import: {error}"));
    assert_eq!(formatted.withdrawn(), []);
    assert_eq!(
        formatted.into_text(),
        "import \"./circle.gandr\" ;\n\ndef twice : Path(
  Path(Circle, Base, Base),
  transport(\\a. Path(Circle, Base, a), loop, loop),
  here(Base)
) ;
"
    );
    let alone = format_beside(&grammar, &parsed, options, Beside::Alone)
        .unwrap_or_else(|error| panic!("the source formats alone: {error}"));
    let kept: Vec<(&str, bool)> = alone
        .withdrawn()
        .iter()
        .map(|withdrawal| {
            (
                withdrawal.declaration.as_str(),
                matches!(withdrawal.reason, Withdrawn::Unchecked(_)),
            )
        })
        .collect();
    assert_eq!(kept, [("twice", true)]);
    assert_eq!(alone.into_text(), source);
}

/// #812: desugaring `stay`'s dependent alias once changed how `stayUp`'s
/// call lowered, since the call read the alias and not the explicit thunk,
/// so `stay` was withdrawn for its reader. The call now reads either
/// spelling, so `stay` is rewritten and no reader withdraws it.
#[test]
fn a_rewrite_of_a_dependent_alias_keeps_its_readers_812()
{
    let grammar = grammar();
    let source = "\
data Nat : Type {
  Zero : Nat;
  Succ : (n : Nat) --> Nat;
}

def next(n : Nat) -> -F Nat {
  Succ(n)
}

def stay : (a : Nat) => Path(Nat, a, a) ;

def stayUp(a : Nat) -> -F Path(Nat, Succ(a), Succ(a)) {
  cong(next, stay(a)) then here(Succ(a))
}
";
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options)
        .unwrap_or_else(|error| panic!("the source formats: {error}"));
    let kept: Vec<(&str, &Withdrawn)> = formatted
        .withdrawn()
        .iter()
        .map(|withdrawal| (withdrawal.declaration.as_str(), &withdrawal.reason))
        .collect();
    assert!(kept.iter().all(|&(name, _)| name != "stay"), "{kept:?}");
    assert!(
        formatted
            .text()
            .as_ref()
            .contains("def stay : +U ((a : Nat) -> -F Path(Nat, a, a)) ;"),
        "{}",
        formatted.text()
    );
}

/// A selection runs the rewrites it names and no other.
#[test]
fn a_selection_runs_only_the_rewrites_it_names()
{
    let grammar = grammar();
    let source = "def pair : Integer * String ;\ndef tuple = (1, 2) ;\n";
    assert_eq!(
        spelled(
            &grammar,
            source,
            Form::Explicit,
            Selection::Only(&[RewriteName::Tuple])
        ),
        "def pair : Integer * String ;\ndef tuple = #{1, 2} ;\n"
    );
}

/// The rewrites' sweep: every corpus source formats into either form, the
/// formatter checking its meaning, and formats once in it.
mod sweeps
{
    use gandr_surface_format::Form;
    use gandr_surface_format::Selection;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::grammar;
    use super::spelled;

    /// The sample: sixty-four sources, ranked by their BLAKE3 digest under
    /// this name, at least one of each corpus class, and every source the
    /// change adds or modifies (`gandr-workflow-sweep`). The `sweeps`
    /// profile formats every source.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_source_formats_into_either_form_and_keeps_its_meaning"),
        size: SampleSize(64),
    };

    #[test]
    fn every_source_formats_into_either_form_and_keeps_its_meaning()
    {
        let grammar = grammar();
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let sources = sweep.visit(SAMPLE, &corpus::sources().expect("the corpus reads"));
        assert!(
            sources.len() >= SAMPLE.size.0,
            "the sample is drawn: {}",
            sources.len()
        );
        let mut refused = Vec::new();
        for source in sources {
            let text_of =
                std::fs::read_to_string(&source.path).expect("a corpus source is readable");
            for form in [Form::Explicit, Form::Sugared] {
                let Ok(parsed) = gandr_surface_parser::parse(
                    &grammar,
                    gandr_surface_syntax::SourceText::from(text_of.as_str()),
                )
                else {
                    continue;
                };
                let options = gandr_surface_format::FormatOptions {
                    form,
                    ..gandr_surface_format::FormatOptions::default()
                };
                match gandr_surface_format::format(&grammar, &parsed, options) {
                    Ok(formatted) => {
                        let once = formatted.into_text();
                        assert_eq!(
                            spelled(&grammar, once.as_str(), form, Selection::Every),
                            once,
                            "{} formats once as {form}",
                            source.name
                        );
                    },
                    Err(error) => refused.push(format!("{} as {form}: {error}", source.name)),
                }
            }
        }
        assert!(
            refused.is_empty(),
            "every source formats:\n{}",
            refused.join("\n")
        );
    }
}
