//! The rewrites between the explicit and the sugared spellings through the
//! formatter's public surface: each pair both ways, comments kept with the
//! construct they annotate, the declared form over the option, a selection
//! by name, and the corpus formatted into either form — a sample on every
//! pull request, every source under the `sweeps` profile.

use gandr_surface_format::Form;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::Formatted;
use gandr_surface_format::RewriteName;
use gandr_surface_format::Selection;
use gandr_surface_format::format;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
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
