//! The rewrites between the explicit and the sugared spellings through the
//! formatter's public surface: each pair both ways, comments kept with the
//! construct they annotate, the declared form over the option, a selection
//! by name, and the corpus formatted into either form — a sample on every
//! pull request, every source under the `sweeps` profile.

use alloc::collections::BTreeMap;
use core::cell::Cell;

use expect_test::expect;
use gandr_core_term::CoreArena;
use gandr_surface_format::Beside;
use gandr_surface_format::Elaborate;
use gandr_surface_format::Elaboration;
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
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;

/// Every pair of the table in the explicit spelling, nested and
/// parenthesised where the sugar needs it.
const EXPLICIT: &str = include_str!("rewrite/unformatted/explicit.gandr");

/// [`EXPLICIT`] in the sugared spelling, as the presentation printer
/// parenthesises it.
const SUGARED: &str = include_str!("rewrite/unformatted/sugared.gandr");

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

/// `source` formatted under `form` beside a stand-in for every module its
/// path imports name, each resolving to it: a source naming a host interface
/// imports its module (#4523).
///
/// # Specification
/// trivial.
fn hosted_spelled<Source>(
    grammar: &Pbg,
    source: &Source,
    form: Form,
) -> String
where
    Source: AsRef<str> + ?Sized,
{
    let parsed = parse(grammar, SourceText::from(source.as_ref())).expect("the source parses");
    let imports = source
        .as_ref()
        .lines()
        .filter(|line| line.starts_with("import "))
        .count();
    let unit = Unit::new(Vec::from([
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(ByteOffset::from(1_usize), vec![
            ImportTarget::Source(
                SourceIndex::from(0_usize)
            );
            imports
        ]),
    ]))
    .expect("the unit is well formed");
    let beside = Beside::Imports {
        before: SourceText::from("\n"),
        unit: &unit,
    };
    let options = FormatOptions {
        form,
        rewrites: Selection::Every,
        ..FormatOptions::default()
    };
    format_beside(grammar, &parsed, options, (beside, None)).map_or_else(
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

/// #1327: the default grade of a thunk type, `ω` or `inf` in ASCII, is
/// unwritten in either form, as the printer writes neither, and a value
/// function written with it is sugared as one written without; a comment
/// within the grade, or any other grade, keeps it written. In a theory's
/// judgment only the alias over one bare domain is written: a parenthesised
/// list there opens the judgment's port group (#1329).
#[test]
fn the_default_grade_is_unwritten_in_either_form_1327()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/the-default-grade-is-unwritten-in-either-form-1327.gandr"
    );
    for (form, expected) in [
        (
            Form::Sugared,
            "\
def step : Integer -> Integer;
def lazy : +U (-F Integer & -F Integer);
def noted : +U[/* every use */ ω] (-F Integer);
def once : +U[1] (Integer -> -F Integer);
theory Counting where {
  sort T : Type;
  oper next : T -> T;
  oper add : +U (T -> T -> -F T);
}
",
        ),
        (
            Form::Explicit,
            "\
def step : +U (Integer -> -F Integer);
def lazy : +U &{-F Integer, -F Integer};
def noted : +U[/* every use */ ω] (-F Integer);
def once : +U[1] (Integer -> -F Integer);
theory Counting where {
  sort T : Type;
  oper next : +U (T -> -F T);
  oper add : +U (T -> T -> -F T);
}
",
        ),
    ] {
        assert_eq!(
            spelled(&grammar, source, form, Selection::Every),
            expected,
            "{form}"
        );
    }
}

/// #2384: a law's statement is kept as written in either form, the
/// value-function alias over its named telescope, which is the only spelling
/// a theory reads there, while an operation's judgment beside it is respelled.
#[test]
fn a_law_keeps_its_statement_in_either_form_2384()
{
    let grammar = grammar();
    let explicit = include_str!(
        "rewrite/unformatted/a-law-keeps-its-statement-in-either-form-2384-explicit.gandr"
    );
    let sugared = include_str!(
        "rewrite/unformatted/a-law-keeps-its-statement-in-either-form-2384-sugared.gandr"
    );
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

/// #1327: the sugared form leaves out a tail's `return` of a value, in a
/// body, a match arm, a block and a nested function, as the lowering would
/// infer it; an early `return`, one of a computation, one written as a
/// statement, one under `explicit_exits` and one with a comment after its
/// keyword keep it, and the explicit form writes the source as it was given.
#[test]
fn a_tail_return_is_left_out_where_the_lowering_would_infer_it_1327()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-tail-return-is-left-out-where-the-lowering-would-infer-it-1327.gandr"
    );
    let sugared = "\
data Nat : Type where { | Zero : Nat | Succ : (n : Nat) --> Nat }

def succeeded(n : Nat) -> Nat {
  Succ n
}

def early(k : Nat) -> Nat {
  match k {
    | Zero => k
    | Succ(j) => {
      let q = match j {
        | Zero => return j
        | Succ(r) => pure r
      };
      pure q
    }
  }
}

def computed(n : Nat) -> Nat {
  return succeeded n
}

def stated(n : Nat) -> Nat {
  return n;
}

def nested(n : Nat) -> Nat -> Nat {
  thunk { fun (x) { Succ x } }
}

def blocked(n : Nat) -> Nat {
  match n {
    | Zero => { let y = succeeded n; y }
    | Succ(p) => p
  }
}

def noted(n : Nat) -> Nat {
  return /* the argument */ n
}

@[ explicit_exits ]
def asked(n : Nat) -> Nat {
  return n
}
";
    assert_eq!(
        spelled(&grammar, source, Form::Sugared, Selection::Every),
        sugared,
        "sugared"
    );
    assert_eq!(
        spelled(&grammar, source, Form::Explicit, Selection::Every),
        source,
        "explicit"
    );
}

/// #2325: a result at a world or a region keeps its returner, `-> -F (A at
/// r)`, as the printer writes it: the lowering inserts no returner over a
/// value at a region, so leaving it out would lower to other core and the
/// whole declaration would keep its spelling. The parameter's thunk type
/// still takes its alias.
#[test]
fn a_result_at_a_region_keeps_its_returner_2325()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/a-result-at-a-region-keeps-its-returner-2325.gandr");
    let sugared = "\
def pass[r : Region](k : (() -> Integer) at r) -> -F ((() -> Integer) at r) {
  pure k
}
";
    assert_eq!(
        spelled(&grammar, source, Form::Sugared, Selection::Every),
        sugared,
        "sugared"
    );
}

/// #2255: the sugared form writes a result row of several interfaces before
/// its type, `[Partial, std.process.Exit.Eff] B`, a row open through a tail as
/// written, `[Partial | r] B` and `[r] B`, and a type looser than an
/// application parenthesised after it; a row under `+U` in a parameter's type
/// is no result and keeps its returner.
#[test]
fn a_result_row_is_written_before_its_type_2255()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/a-result-row-is-written-before-its-type-2255.gandr");
    let sugared = "\
import std.process;

def both() -> [Partial, std.process.Exit.Eff] Integer {
  pure 1
}

def pair() -> [Partial] (Integer * Integer) {
  pure *{1, 2}
}

def apply(k : +U (Unit -> -F [Partial] Unit)) -> [Partial] Unit {
  k *{}
}

def tailed[r : Row]() -> [Partial | r] Unit {
  pure *{}
}

def open[r : Row]() -> [r] Unit {
  pure *{}
}
";
    assert_eq!(
        hosted_spelled(&grammar, source, Form::Sugared),
        sugared,
        "sugared"
    );
}

/// #2271: the sugared form writes a result row naming an instance by its
/// label before its type as the row reads, each label before its interface:
/// alone, `[out : std.io.Console.Eff] B`, after an interface and before a tail;
/// the explicit form keeps either spelling.
#[test]
fn a_labelled_result_row_is_written_before_its_type_2271()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-labelled-result-row-is-written-before-its-type-2271.gandr"
    );
    let sugared = include_str!(
        "rewrite/unformatted/a-labelled-result-row-is-written-before-its-type-2271-sugared.gandr"
    );
    assert_eq!(
        hosted_spelled(&grammar, source, Form::Sugared),
        sugared,
        "sugared"
    );
    for written in [source, sugared] {
        assert_eq!(
            hosted_spelled(&grammar, written, Form::Explicit),
            written,
            "explicit"
        );
    }
}

/// #1327: the sugared form writes a value-function alias at its shortest:
/// one domain unparenthesised however deeply written, nested aliases among
/// them, and a binder nothing later reads left out; a list of domains, a
/// binder a later domain or the result reads, and a domain with a comment
/// keep their spelling.
#[test]
fn a_value_function_alias_is_written_at_its_shortest_1327()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-value-function-alias-is-written-at-its-shortest-1327.gandr"
    );
    let sugared = include_str!(
        "rewrite/unformatted/a-value-function-alias-is-written-at-its-shortest-1327-sugared.gandr"
    );
    assert_eq!(
        spelled(&grammar, source, Form::Sugared, Selection::Every),
        sugared
    );
    assert_eq!(
        spelled(&grammar, sugared, Form::Sugared, Selection::Every),
        sugared,
        "the shortest spelling is kept"
    );
}

/// The circle the path-composite goldens compose its loop in.
const CIRCLE: &str = include_str!("rewrite/unformatted/circle.gandr");

/// #5206: both forms write a derived path operation as the operation, as the
/// printer does. A written composite, inverse or action keeps its spelling in
/// the explicit form, and both forms fold a written transport into the
/// operation it derives, nested. #1003: the inverse is taken at the circle's
/// point, where the reflexivity it moves is the empty word a written
/// `Path.here Base` reads as.
#[test]
fn the_path_operations_fold_in_both_forms_5206()
{
    let grammar = grammar();
    let unfolded = format!(
        include_str!(
            "rewrite/unformatted/the-path-operations-fold-in-both-forms-5206-unfolded.gandr"
        ),
        CIRCLE = CIRCLE
    );
    let folded = |returner: &str| {
        format!(
            "{CIRCLE}def spin(x : Circle) -> {returner} {{
  x
}}

def thrice : Path[.A = Path[.A = Circle](Base, Base)](
  Path.step loop (Path.step loop loop),
  Path.here Base
);

def undone : Path[.A = Path[.A = Circle](Base, Base)](
  Path.back loop,
  Path.back loop
);

def spun : Path[.A = Path[.A = Circle](Base, Base)](
  Path.ap spin loop,
  Path.ap spin loop
);
"
        )
    };
    let (explicit, back) = (folded("-F Circle"), folded("Circle"));
    for (source, form, expected) in [
        (&unfolded, Form::Explicit, &explicit),
        (&unfolded, Form::Sugared, &back),
        (&explicit, Form::Explicit, &explicit),
        (&explicit, Form::Sugared, &back),
        (&back, Form::Sugared, &back),
    ] {
        assert_eq!(
            spelled(&grammar, source.as_str(), form, Selection::Every),
            *expected,
            "{form}"
        );
    }
}

/// #4645: a map's action on a path between paths, whose transport quotes its
/// motive, `fun (b) { type(Path(…)) }`, since no expression reads a path over
/// a path. Both forms keep the action as written and fold the quoted
/// transport into the action.
#[test]
fn an_action_under_a_quoted_motive_folds_in_both_forms_4645()
{
    let grammar = grammar();
    let declaration = |action: &str| {
        format!(
            "def congInAType(
  A : Type,
  x : A,
  y : A,
  w : A,
  f1 : Path[.A = A](x, y),
  f2 : Path[.A = A](x, y),
  a : Path[.A = Path[.A = A](x, y)](f1, f2),
  F : Path[.A = A](x, y) -> Path[.A = A](x, w)
) -> Path[.A = Path[.A = Path[.A = A](x, w)](F f1, F f2)]({action}, {action}) {{
  Path.here ({action})
}}
"
        )
    };
    let written = declaration("Path.ap F a");
    let unfolded = declaration(
        "Path.walk (fun (b) { type(Path[.A = Path[.A = A](x, w)](F f1, F b)) }) a (Path.here (F f1))",
    );
    for source in [&written, &unfolded] {
        for form in [Form::Explicit, Form::Sugared] {
            let out = spelled(&grammar, source.as_str(), form, Selection::Every);
            assert_eq!(
                (
                    out.matches("Path.ap F a").count(),
                    out.contains("Path.walk")
                ),
                (3_usize, false),
                "{form}: the action stays an action: {out}"
            );
        }
    }
}

/// #985: a composite read as a value, alone or under `back`, folds in both
/// forms: a written transport read as a value lowers to the value it
/// returns, so both forms write it as the composite.
#[test]
fn a_composite_read_as_a_value_folds_in_both_forms_985()
{
    let grammar = grammar();
    let sugared = format!(
        include_str!(
            "rewrite/unformatted/a-composite-read-as-a-value-folds-in-both-forms-985-sugared.gandr"
        ),
        CIRCLE = CIRCLE
    );
    let unfolded = format!(
        include_str!(
            "rewrite/unformatted/a-composite-read-as-a-value-folds-in-both-forms-985-unfolded.gandr"
        ),
        CIRCLE = CIRCLE
    );
    let explicit = format!(
        include_str!(
            "rewrite/unformatted/a-composite-read-as-a-value-folds-in-both-forms-985-explicit.gandr"
        ),
        CIRCLE = CIRCLE
    );
    for (source, form, expected) in [
        (&sugared, Form::Explicit, &explicit),
        (&unfolded, Form::Explicit, &explicit),
        (&unfolded, Form::Sugared, &sugared),
        (&explicit, Form::Sugared, &sugared),
        (&explicit, Form::Explicit, &explicit),
    ] {
        assert_eq!(
            spelled(&grammar, source.as_str(), form, Selection::Every),
            *expected,
            "{form}"
        );
    }
}

/// A transport standing as a computation keeps its spelling in both forms,
/// with nothing withdrawn: the printer writes an operation only for the
/// transport the lowering returns, and spells one a body runs as written.
#[test]
fn a_transport_standing_as_a_computation_keeps_its_spelling()
{
    let grammar = grammar();
    let source = format!(
        include_str!(
            "rewrite/unformatted/a-transport-standing-as-a-computation-keeps-its-spelling.gandr"
        ),
        CIRCLE = CIRCLE
    );
    let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
    for form in [Form::Sugared, Form::Explicit] {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(formatted.withdrawn(), &[], "{form}");
        assert_eq!(formatted.into_text(), source, "{form}");
    }
}

/// A composite or an inverse standing as the operand of a transport a body
/// runs keeps its transport too, nested to any depth, in both forms: the
/// printer writes a derived operation there as the transport it derives,
/// nothing there stating its type.
#[test]
fn a_derived_operand_of_a_kept_transport_keeps_its_transport()
{
    let grammar = grammar();
    for body in [
        "Path.walk (fun (a) { type(Path[.A = Circle](Base, a)) }) (Path.walk (fun (a) { type(Path[.A = Circle](Base, a)) }) p p) p",
        "Path.walk (fun (a) { type(Path[.A = Circle](Base, a)) }) p (Path.walk (fun (a) { type(Path[.A = Circle](a, Base)) }) \
         (Path.walk (fun (a) { type(Path[.A = Circle](Base, a)) }) p p) (Path.here Base))",
    ] {
        let source = format!(
            include_str!(
                "rewrite/unformatted/a-derived-operand-of-a-kept-transport-keeps-its-transport.gandr"
            ),
            CIRCLE = CIRCLE,
            body = body
        );
        let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
        let laid_out = format(&grammar, &parsed, FormatOptions::default())
            .expect("the source lays out")
            .into_text();
        for form in [Form::Sugared, Form::Explicit] {
            let options = FormatOptions {
                form,
                ..FormatOptions::default()
            };
            let formatted = format(&grammar, &parsed, options).expect("the source formats");
            assert_eq!(formatted.withdrawn(), &[], "{form}: {body}");
            assert_eq!(
                formatted.into_text(),
                laid_out,
                "{form}: {body}: only the layout moves"
            );
        }
    }
}

/// The sugared form strips a bare top-level `@[ checks ]` wherever its
/// declaration stands, on the block's own line or below it, so one pass gives
/// what two give (#3049).
#[test]
fn a_bare_checks_block_before_its_declaration_s_line_is_stripped_once_3049()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-bare-checks-block-before-its-declaration-s-line-is-stripped-once-3049.gandr"
    );
    let sugared = |text: &str| {
        let parsed = parse(&grammar, SourceText::from(text)).expect("the source parses");
        let options = FormatOptions {
            form: Form::Sugared,
            ..FormatOptions::default()
        };
        format(&grammar, &parsed, options)
            .expect("the source formats")
            .into_text()
    };
    let once = sugared(source);
    assert_eq!(
        once,
        "/// One.\ndef one(x : Unit) -> Unit { x }\n\n/// Two.\ndef two(x : Unit) -> Unit { x }\n",
        "both blocks go in one pass"
    );
    assert_eq!(sugared(&once), once, "a second pass changes nothing");
}

/// A parenthesised list after a rule's `<=>` is the rule's outputs, not a
/// tuple: the explicit form keeps it, and a record read as a value beside it
/// stays `*{…}`.
#[test]
fn a_rule_s_outputs_are_not_a_tuple()
{
    let grammar = grammar();
    let rules = include_str!("rewrite/unformatted/a-rule-s-outputs-are-not-a-tuple-rules.gandr");
    assert_eq!(
        spelled(
            &grammar,
            format!("{rules}def pair = *{{1, 2}} ;\n").as_str(),
            Form::Explicit,
            Selection::Every
        ),
        format!("{rules}def pair = *{{1, 2}};\n")
    );
}

/// A parenthesised list after an unbiased composite's shape is its cells, not
/// a tuple: the explicit form keeps it, and withdraws nothing, while a record
/// read as a value beside it stays `*{…}` (#3957).
#[test]
fn a_composite_s_cells_are_not_a_tuple_3957()
{
    let grammar = grammar();
    let source = include_str!("rewrite/unformatted/a-composite-s-cells-are-not-a-tuple-3957.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(
        formatted.withdrawn(),
        &[],
        "no declaration keeps its spelling"
    );
    let text = formatted.into_text();
    assert!(
        text.contains("compose[5, 7] (chain 3) (p, q, r)"),
        "the cells stay a list: {text}"
    );
    assert!(
        text.contains("def pair = *{1, 2};"),
        "a tuple is braced: {text}"
    );
}

/// An arrow written under a thunk inside a type quote is the computation
/// arrow, and so is its codomain arrow. The explicit form keeps both as
/// written and braces the product of the two thunks, as the printer does. The
/// sugared form writes the product back (#5207). Each application is written
/// juxtaposed, `T A` (#5708).
#[test]
fn a_product_of_thunks_in_a_type_quote_is_braced_5207()
{
    let grammar = grammar();
    let quoted = "type(*{+U (A -> T A), +U (+U (T A) -> +U (A -> T B) -> T B)})";
    let source = "def raw : (Type -> Type[-]) -> Type -> Type -> Type = fun (T) { fun (A) { fun (B) { \
                  type(+U (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B))) } } };\n";
    let form = |source: &str, form: Form| {
        let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(
            formatted.withdrawn(),
            &[],
            "no declaration keeps its spelling"
        );
        formatted.into_text()
    };
    let explicit = form(source, Form::Explicit);
    assert!(
        explicit.contains(quoted),
        "each arrow under a thunk stays as written: {explicit}"
    );
    let sugared = form(&explicit, Form::Sugared);
    assert!(
        sugared.contains("type(+U (A -> T A) * +U (+U (T A) -> +U (A -> T B) -> T B))"),
        "the product of the thunks sugars back: {sugared}"
    );
}

/// A parenthesised list after a fill's generator is its cells, not a tuple:
/// the explicit form keeps it and withdraws nothing (#4075).
#[test]
fn a_fill_s_cells_are_not_a_tuple_4075()
{
    let grammar = grammar();
    let source = include_str!("rewrite/unformatted/a-fill-s-cells-are-not-a-tuple-4075.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(
        formatted.withdrawn(),
        &[],
        "no declaration keeps its spelling"
    );
    let text = formatted.into_text();
    assert!(
        text.contains("fill[5, 7] (chain 2) (selfComposite a x y z) (fa, g)"),
        "the cells stay a list: {text}"
    );
}

/// A parenthesised list inside a level-two shape, `chain(m, (a₁, …, aₘ))`,
/// is its column heights, not a tuple: the explicit form keeps the
/// whisker's shape and withdraws nothing, while a record read as a value
/// beside it stays `*{…}` (#4475).
#[test]
fn a_level_two_shape_s_heights_are_not_a_tuple_4475()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/a-level-two-shape-s-heights-are-not-a-tuple-4475.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(
        formatted.withdrawn(),
        &[],
        "no declaration keeps its spelling"
    );
    let text = formatted.into_text();
    assert!(
        text.contains("compose[5, 11] (chain 2 (1, 0)) (fa, g)"),
        "the heights stay a list: {text}"
    );
    assert!(
        text.contains("def pair = *{1, 0};"),
        "a tuple is braced: {text}"
    );
}

/// A composite of two flows is no path composite: it has no transport to
/// write, so the explicit form keeps its `then`.
#[test]
fn a_composite_of_flows_keeps_its_then()
{
    let grammar = grammar();
    let source = include_str!("rewrite/unformatted/a-composite-of-flows-keeps-its-then.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid_out = format(&grammar, &parsed, FormatOptions::default())
        .expect("the source lays out")
        .into_text();
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    assert_eq!(formatted.into_text(), laid_out);
}

/// A transport whose motive is no path type, or no abstraction at all, or a
/// path type whose endpoints, or a call whose arguments, fit none of the
/// derived operations, derives no path operation: the sugared form keeps it
/// as written.
#[test]
fn a_transport_along_no_path_motive_keeps_its_spelling()
{
    let grammar = grammar();
    for value in [
        "Path.walk (fun (a) { Integer }) loop 5",
        "Path.walk (+U (Circle -> -F Integer)) loop 5",
        "Path.walk (fun (a) { type(Path[.A = Circle](a, a)) }) loop (Path.here Base)",
        "Path.walk (fun (a) { type(Path[.A = Circle](Base, Base)) }) loop (Path.here Base)",
        "Path.walk (fun (a) { type(Path[.A = Circle](a, Base)) }) loop loop",
        "Path.walk (fun (a) { type(Path[.A = Circle](Base, a)) }) loop",
    ] {
        let source = format!("{CIRCLE}def m : Integer = {value};\n");
        assert_eq!(
            spelled(&grammar, source.as_str(), Form::Sugared, Selection::Every),
            source
        );
    }
}

/// #803: a composite of types, its carrier `Type`, which the grammar keeps as
/// the path type's own tile, sugars back from its transport as any other.
#[test]
fn a_composite_of_types_sugars_back_803()
{
    let grammar = grammar();
    let source = include_str!("rewrite/unformatted/a-composite-of-types-sugars-back-803.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    expect![[r#"
        def joined(
          a : Type,
          b : Type,
          c : Type,
          p : Path[.A = Type](a, b),
          q : Path[.A = Type](b, c)
        ) -> Path[.A = Path[.A = Type](a, c)](Path.step p q, Path.step p q) {
          Path.here (Path.step p q)
        }
    "#]]
    .assert_eq(formatted.text().as_ref());
}

/// The value-function alias is written where the printer writes it: a thunk
/// type standing as a call's argument, a transport's family, takes the alias
/// over its domain list, the binder a later domain reads named and the one
/// nothing reads left out (#2255). A static lambda's body is read as an
/// expression, so it takes the alias over a domain and the thunk over none,
/// `+U (-F X)`, as a quoted thunk type is (#4508).
#[test]
fn the_value_function_alias_is_written_where_the_printer_writes_it()
{
    let grammar = grammar();
    let argument = include_str!(
        "rewrite/unformatted/the-value-function-alias-is-written-where-the-printer-writes-it-argument.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(argument)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    expect![[r#"
        data Nat : Type where {
          | Zero : Nat
          | Succ : (n : Nat) --> Nat
        }

        def kept(a : Nat, b : Nat, q : Path[.A = Nat](a, b)) -> Path[.A = Nat](b, a) {
          become Path.walk
            ((y : Nat, Path[.A = Nat](a, y)) -> Path[.A = Nat](y, a))
            q
            (Path.here a)
            (Path.here q)
            (Path.here a)
        }
    "#]]
    .assert_eq(formatted.text().as_ref());
    let explicit = include_str!(
        "rewrite/unformatted/the-value-function-alias-is-written-where-the-printer-writes-it-explicit.gandr"
    );
    let sugared = include_str!(
        "rewrite/unformatted/the-value-function-alias-is-written-where-the-printer-writes-it-sugared.gandr"
    );
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

/// #2246: a manifest sort's carrier binds no looser than a sum, as the printer
/// writes it: a thunk type fixed there takes the alias parenthesised, and the
/// alias fixed there takes the thunk with the parenthesis it needed gone.
#[test]
fn a_manifest_carrier_is_parenthesised_as_the_printer_writes_it_2246()
{
    let grammar = grammar();
    let theory = include_str!(
        "rewrite/unformatted/a-manifest-carrier-is-parenthesised-as-the-printer-writes-it-2246-theory.gandr"
    );
    let explicit =
        format!("{theory}def endo : Model Pointed with sort M = +U (Integer -> -F Integer);\n");
    let sugared = format!("{theory}def endo : Model Pointed with sort M = (Integer -> Integer);\n");
    for (source, form, expected) in [
        (&explicit, Form::Sugared, &sugared),
        (&sugared, Form::Explicit, &explicit),
    ] {
        assert_eq!(
            spelled(&grammar, source.as_str(), form, Selection::Every),
            *expected,
            "{form}"
        );
    }
}

/// #838: a thunk type a body returns takes the value-function alias over
/// one bare domain, as the printer writes it, and so does one standing as a
/// call's argument, a transport's family (#2255).
#[test]
fn a_thunk_type_a_body_returns_takes_the_alias_838()
{
    let grammar = grammar();
    let explicit = include_str!(
        "rewrite/unformatted/a-thunk-type-a-body-returns-takes-the-alias-838-explicit.gandr"
    );
    expect![[r#"
        data Nat : Type where {
          | Zero : Nat
          | Succ : (n : Nat) --> Nat
        }

        def onType(t : Type) -> Type {
          return (t -> t)
        }

        def flat(a : Nat, b : Nat, q : Path[.A = Nat](a, b), v : Nat) -> Nat {
          become Path.walk (Nat -> Nat) q v v v
        }
    "#]]
    .assert_eq(&spelled(
        &grammar,
        explicit,
        Form::Sugared,
        Selection::Every,
    ));
}

/// #5528: before the fix, the value-function sugar wrote a thunk over a kind
/// arrow, `+U (Type -> -F Type)`, as the static arrow `Type -> Type`. That
/// lowers otherwise, so the formatter withdrew every rewrite of the
/// declaration, and the value function beside it kept its thunk. Now the thunk
/// over a kind arrow keeps its spelling, and the value function is sugared.
#[test]
fn a_thunk_over_a_kind_arrow_keeps_its_spelling_beside_a_value_function_5528()
{
    let grammar = grammar();
    let source = "def kinded(e : *{c : +U ((x : Integer) -> -F Integer), b : +U (Type -> -F Type)}) -> Integer { 0 }\n";
    assert_eq!(
        spelled(&grammar, source, Form::Sugared, Selection::Every),
        "def kinded(e : *{c : Integer -> Integer, b : +U (Type -> -F Type)}) -> Integer { 0 }\n",
        "the thunk over the kind arrow keeps its spelling, and the value function is sugared"
    );
}

/// An explicit source with comments inside its declarations, sugared: each
/// comment stays in its role before or after the construct it annotated.
#[test]
fn a_sugared_source_keeps_every_comment_with_its_construct()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-sugared-source-keeps-every-comment-with-its-construct.gandr"
    );
    let sugared = include_str!(
        "rewrite/unformatted/a-sugared-source-keeps-every-comment-with-its-construct-sugared.gandr"
    );
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
            "*{Integer, String}",
        ),
        (
            "sugared",
            Form::Explicit,
            "*{Integer, String}",
            "Integer * String",
        ),
    ] {
        let source = format!(
            include_str!("rewrite/unformatted/a-declared-form-wins-over-the-option.gandr"),
            declared = declared,
            written = written
        );
        assert_eq!(
            spelled(&grammar, source.as_str(), asked, Selection::Every),
            format!("@[ form({declared}) ]\ndef pair : {expected};\n"),
            "declared {declared}, asked {asked}"
        );
    }
}

/// #791: a declaration whose sum pattern reads its parameter's stated
/// `+{…}` is sugared like the declaration beside it, and nothing is
/// withdrawn: the lowering reads `A + B` as it reads `+{A, B}`. Before the
/// fix, the sugared match was refused and the declaration kept its spelling.
/// Its arms' tail `return`s are left out (#1327).
#[test]
fn a_match_over_a_stated_sum_is_sugared_791()
{
    let grammar = grammar();
    let matched = |stated: &str, exit: &str, result: &str| {
        format!(
            "def pick(t : {stated}) -> {result} {{\n  match t {{\n    | +{{.1 = x}} => {exit}x\n    | _ => {exit}0\n  }}\n}}"
        )
    };
    let source = format!(
        include_str!("rewrite/unformatted/a-match-over-a-stated-sum-is-sugared-791.gandr"),
        matched("+{Integer, Integer}", "return ", "-F Integer")
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
                "{}\n\ndef pair : Integer * String;\n",
                matched("Integer + Integer", "", "Integer")
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
/// of meaning. The arm's tail `return` is left out (#1327).
#[test]
fn a_body_hole_keeps_its_meaning_beside_a_rewrite_893()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-body-hole-keeps-its-meaning-beside-a-rewrite-893.gandr"
    );
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
                .replace("*{Integer, String}", "Integer * String")
                .replace("-> -F Integer", "-> Integer")
                .replace("return 0", "0")
                .as_str(),
            [].as_slice()
        )
    );
}

/// A source that imports a sibling is lowered beside it: the rewrite whose
/// meaning reads the sibling's declarations applies, where alone the
/// declaration's lowering is refused and it keeps its spelling, reported.
/// Here the explicit form folds a transport into the composite it derives.
#[test]
fn an_importing_source_is_rewritten_beside_its_imports()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/an-importing-source-is-rewritten-beside-its-imports.gandr"
    );
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
    let formatted = format_beside(&grammar, &parsed, options, (beside, None))
        .unwrap_or_else(|error| panic!("the source formats beside its import: {error}"));
    assert_eq!(formatted.withdrawn(), []);
    assert_eq!(
        formatted.into_text(),
        "import \"./circle.gandr\";\n\ndef twice : Path[.A = Path[.A = Circle](Base, Base)](
  Path.step loop loop,
  Path.here Base
);
"
    );
    let alone = format_beside(&grammar, &parsed, options, (Beside::Alone, None))
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
    let source = include_str!(
        "rewrite/unformatted/a-rewrite-of-a-dependent-alias-keeps-its-readers-812.gandr"
    );
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
            .contains("def stay : +U ((a : Nat) -> -F Path[.A = Nat](a, a));"),
        "{}",
        formatted.text()
    );
}

/// A selection runs the rewrites it names and no other.
#[test]
fn a_selection_runs_only_the_rewrites_it_names()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/a-selection-runs-only-the-rewrites-it-names.gandr");
    assert_eq!(
        spelled(
            &grammar,
            source,
            Form::Explicit,
            Selection::Only(&[RewriteName::Sum])
        ),
        "def pair : Integer * String;\ndef choice : +{Integer, String};\n"
    );
}

/// A stray is named by the text it opens with, which the layout respaces; it
/// binds no name, so a rewrite beside it is checked by its role and position
/// and kept.
#[test]
fn a_respaced_root_expression_keeps_the_rewrite_beside_it()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-respaced-root-expression-keeps-the-rewrite-beside-it.gandr"
    );
    assert_eq!(
        spelled(&grammar, source, Form::Explicit, Selection::Every),
        "def pair : *{Integer, String};\ndef s = *{b = 1};\n*{s | b = 2}\n"
    );
}

/// What a test's checker answers for every declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Answer
{
    /// One body, for the source and the rewritten text alike.
    Alike,
    /// A body for the source and none for the rewritten text.
    Apart,
    /// None for the source: it refuses it as written.
    Refused,
}

/// A checker whose elaborations the test decides, counting the modules it is
/// asked about: the source's first, then the rewritten text's.
struct Oracle
{
    /// What it answers.
    answer: Answer,
    /// The modules it was asked about so far.
    asked: Cell<usize>,
}

impl Elaborate for Oracle
{
    /// Every declaration's body as [`Answer`] says, for the source asked
    /// first and the rewritten text after it, and no crossing.
    ///
    /// # Specification
    /// trivial.
    fn elaborate(
        &self,
        arena: &mut CoreArena,
        module: &LoweredModule<'_>,
    ) -> Elaboration
    {
        let asked = self.asked.get();
        self.asked.set(asked.saturating_add(1));
        Elaboration {
            definitions: module
                .declarations()
                .iter()
                .map(|_| match (self.answer, asked) {
                    (Answer::Alike, _) | (Answer::Apart, 0) => Some(arena.value_unit()),
                    (Answer::Apart | Answer::Refused, _) => None,
                })
                .collect(),
            crossings: BTreeMap::new(),
        }
    }
}

/// A `let` statement the lowering lists as linear follows the checker: it is
/// written at its read where the checker elaborates both spellings to one
/// body, withdrawn and reported where it elaborates them otherwise, and kept
/// with nothing reported where it refuses the source as written. The
/// checker's own verdict on a real source is the dispatcher's to witness.
#[test]
fn a_linear_run_follows_the_checker_s_elaborations()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/a-linear-run-follows-the-checker-s-elaborations.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let format = |answer: Answer| {
        let oracle = Oracle {
            answer,
            asked: Cell::new(0),
        };
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, Some(&oracle)))
            .expect("the source formats");
        let withdrawn: Vec<(String, Withdrawn)> = formatted
            .withdrawn()
            .iter()
            .map(|withdrawal| (withdrawal.declaration.clone(), withdrawal.reason.clone()))
            .collect();
        (formatted.into_text(), withdrawn)
    };
    let written = source.replace("\n  let m = twice n;\n  Succ m\n", "\n  Succ (twice n)\n");
    assert_eq!(
        format(Answer::Alike),
        (written, Vec::new()),
        "elaborated alike, the run is written at its read"
    );
    assert_eq!(
        format(Answer::Apart),
        (
            String::from(source),
            Vec::from([(String::from("field"), Withdrawn::Lowered)])
        ),
        "elaborated otherwise, the declaration keeps its spelling, reported"
    );
    assert_eq!(
        format(Answer::Refused),
        (String::from(source), Vec::new()),
        "refused as written, no run is written away and nothing is withdrawn"
    );
}

/// #2255: a tail's `return` of a call follows the checker as a linear run
/// does: written away where the checker elaborates both spellings to one
/// body, withdrawn and reported where it elaborates them otherwise, and kept
/// with nothing reported where it refuses the source as written or no checker
/// is beside the formatter.
#[test]
fn a_tail_return_of_a_call_follows_the_checker_s_elaborations_2255()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-tail-return-of-a-call-follows-the-checker-s-elaborations-2255.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let format = |answer: Option<Answer>| {
        let oracle = answer.map(|answer| Oracle {
            answer,
            asked: Cell::new(0),
        });
        let checker: Option<&dyn Elaborate> = oracle.as_ref().map(|oracle| {
            let checker: &dyn Elaborate = oracle;
            checker
        });
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, checker))
            .expect("the source formats");
        let withdrawn: Vec<(String, Withdrawn)> = formatted
            .withdrawn()
            .iter()
            .map(|withdrawal| (withdrawal.declaration.clone(), withdrawal.reason.clone()))
            .collect();
        (formatted.into_text(), withdrawn)
    };
    assert_eq!(
        format(Some(Answer::Alike)),
        (source.replace("return twice n", "twice n"), Vec::new()),
        "elaborated alike, the tail is the call"
    );
    assert_eq!(
        format(Some(Answer::Apart)),
        (
            String::from(source),
            Vec::from([(String::from("again"), Withdrawn::Lowered)])
        ),
        "elaborated otherwise, the declaration keeps its spelling, reported"
    );
    assert_eq!(
        format(Some(Answer::Refused)),
        (String::from(source), Vec::new()),
        "refused as written, the return stays and nothing is withdrawn"
    );
    assert_eq!(
        format(None),
        (String::from(source), Vec::new()),
        "with no checker, the return stays and nothing is withdrawn"
    );
}

/// The runs ending a block are written away together, last first, each at
/// its read, a comment between two of them kept; a run whose binder is read
/// twice stops them, and the runs before it stay.
#[test]
fn the_runs_ending_a_block_are_written_away_together()
{
    let grammar = grammar();
    let head = include_str!(
        "rewrite/unformatted/the-runs-ending-a-block-are-written-away-together-head.gandr"
    );
    for (body, written) in [
        (
            include_str!(
                "rewrite/unformatted/the-runs-ending-a-block-are-written-away-together-1.gandr"
            ),
            "  both (twice n) (twice n)\n",
        ),
        (
            include_str!(
                "rewrite/unformatted/the-runs-ending-a-block-are-written-away-together-2.gandr"
            ),
            "  // between\n  both (twice n) (twice n)\n",
        ),
        (
            include_str!(
                "rewrite/unformatted/the-runs-ending-a-block-are-written-away-together-3.gandr"
            ),
            "  let m = twice n;\n  both (twice m) m\n",
        ),
    ] {
        let source = format!("{head}{body}}}\n");
        let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
        let oracle = Oracle {
            answer: Answer::Alike,
            asked: Cell::new(0),
        };
        let options = FormatOptions {
            form: Form::Sugared,
            ..FormatOptions::default()
        };
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, Some(&oracle)))
            .expect("the source formats");
        assert_eq!(
            formatted.into_text(),
            format!("{head}{written}}}\n"),
            "{body}"
        );
    }
}

/// A match's branch writes its runs away as a block does, and a branch's
/// block left with its one computation is written as that computation; a
/// block keeping a statement keeps its braces (#1935).
#[test]
fn a_branch_s_runs_are_written_away_and_its_block_with_them_1935()
{
    let grammar = grammar();
    let head = include_str!(
        "rewrite/unformatted/a-branch-s-runs-are-written-away-and-its-block-with-them-1935-head.gandr"
    );
    for (body, written) in [
        (
            "def armed(a : Nat) -> Nat { match a { | Zero => Zero | Succ(b) => { let d = twice b ; Succ d } } }\n",
            "def armed(a : Nat) -> Nat { match a { | Zero => Zero | Succ(b) => Succ (twice b) } }\n",
        ),
        (
            "def paired(a : Nat) -> Nat { match a { | Zero => Zero | Succ(b) => { let e = twice b ; let f = twice Zero ; both e f } } }\n",
            "def paired(a : Nat) -> Nat { match a { | Zero => Zero | Succ(b) => both (twice b) (twice Zero) } }\n",
        ),
        (
            "def reread(a : Nat) -> Nat { match a { | Zero => Zero | Succ(b) => { let g = twice b ; let h = twice g ; both h g } } }\n",
            "def reread(a : Nat) -> Nat {\n  match a { | Zero => Zero | Succ(b) => { let g = twice b; both (twice g) g } }\n}\n",
        ),
    ] {
        let source = format!("{head}{body}");
        let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
        let oracle = Oracle {
            answer: Answer::Alike,
            asked: Cell::new(0),
        };
        let options = FormatOptions {
            form: Form::Sugared,
            ..FormatOptions::default()
        };
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, Some(&oracle)))
            .expect("the source formats");
        assert_eq!(formatted.into_text(), format!("{head}{written}"), "{body}");
    }
}

/// Every refusal, every reason a declaration keeps its spelling and every
/// rewrite's name renders apart from the others of its kind, carrying what
/// it names.
#[test]
fn every_refusal_withdrawal_and_rewrite_renders_apart()
{
    use gandr_surface_format::Change;
    use gandr_surface_format::FormatError;
    use gandr_surface_format::REWRITES;
    use gandr_surface_layout::RenderError;
    use gandr_surface_layout::error::BuildError;
    use gandr_surface_parser::MeldError;
    use gandr_surface_syntax::SyntaxError;

    /// Each text distinct from every other.
    ///
    /// # Specification
    /// trivial.
    fn apart(texts: &[String])
    {
        for (index, text) in texts.iter().enumerate() {
            assert!(
                texts
                    .get(index.saturating_add(1) ..)
                    .unwrap_or_default()
                    .iter()
                    .all(|other| other != text),
                "`{text}` renders like a later one"
            );
        }
    }
    let refusals = [
        FormatError::Unbalanced,
        FormatError::from(BuildError::ArenaKeyExhausted),
        FormatError::from(RenderError::UnknownDoc),
        FormatError::Reparse(MeldError::Build(SyntaxError::BuilderIdExhausted)),
        FormatError::Changed(Change::Meaning),
        FormatError::Changed(Change::Material),
        FormatError::Changed(Change::Attachment),
    ]
    .map(|refusal| refusal.to_string());
    apart(&refusals);
    let withdrawals = [
        Withdrawn::Refused(String::from("the refusal")),
        Withdrawn::Lowered,
        Withdrawn::Unchecked(String::from("the refusal")),
        Withdrawn::Read(String::from("reader")),
    ]
    .map(|reason| reason.to_string());
    apart(&withdrawals);
    for (index, carried) in [(0, "the refusal"), (2, "the refusal"), (3, "`reader`")] {
        assert!(
            withdrawals[index].contains(carried),
            "`{}` names {carried}",
            withdrawals[index]
        );
    }
    let mut names: Vec<String> = REWRITES
        .iter()
        .map(|rewrite| rewrite.name.to_string())
        .collect();
    names.dedup();
    assert_eq!(
        names,
        [
            "product",
            "sum",
            "lazy-product",
            "value-function",
            "default-grade",
            "path-composite",
            "path-inverse",
            "path-action",
            "tail-return",
            "inserted-returner",
            "short-alias",
            "linear-run",
            "inserted-thunk",
            "inserted-reduct",
            "inserted-forget",
            "function-form",
            "joined-definition",
            "type-application",
        ],
        "each rewrite is named as a caller selects it, in the table's order"
    );
}

/// A rewrite in one declaration is checked against every other kind of
/// declaration beside it — codata, a world, a sealed module's components and
/// a declaration the lowering refuses — and each agrees with its
/// rewritten self, so the rewrite stands and nothing is withdrawn.
#[test]
fn a_rewrite_is_checked_beside_every_kind_of_declaration()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-rewrite-is-checked-beside-every-kind-of-declaration.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    assert_eq!(
        formatted.into_text(),
        source.replace("*{Integer, String}", "Integer * String")
    );
}

/// A `thunk { e }` passed where a thunk is expected follows the checker: it
/// is written `e` where the checker elaborates both spellings to one body,
/// and kept, with nothing reported, where it elaborates them otherwise:
/// there the checker inserts none. Without a checker it is kept.
#[test]
fn an_inserted_thunk_follows_the_checker_s_elaborations()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/an-inserted-thunk-follows-the-checker-s-elaborations-1.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let format = |answer: Option<Answer>| {
        let oracle = answer.map(|answer| Oracle {
            answer,
            asked: Cell::new(0),
        });
        let checker: Option<&dyn Elaborate> = oracle.as_ref().map(|oracle| {
            let checker: &dyn Elaborate = oracle;
            checker
        });
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, checker))
            .expect("the source formats");
        let withdrawn: Vec<(String, Withdrawn)> = formatted
            .withdrawn()
            .iter()
            .map(|withdrawal| (withdrawal.declaration.clone(), withdrawal.reason.clone()))
            .collect();
        (formatted.into_text(), withdrawn)
    };
    let aliased = source.replace("+U (-F Nat)", "() -> Nat");
    assert_eq!(
        format(Some(Answer::Alike)),
        (
            aliased.replace("call (thunk { twice n })", "call (twice n)"),
            Vec::new()
        ),
        "elaborated alike, the thunk is left for the checker to insert"
    );
    assert_eq!(
        format(Some(Answer::Apart)),
        (aliased.clone(), Vec::new()),
        "elaborated otherwise, the thunk is kept and nothing is reported"
    );
    assert_eq!(
        format(None),
        (aliased.clone(), Vec::new()),
        "with no checker to insert it, the thunk is kept"
    );
    // No sugar spells a `become`, a statement or a comment the thunk itself
    // owns, so each keeps its thunk; a comment its body owns goes with the
    // body.
    for (body, written) in [
        (
            "thunk { become twice n }",
            "call (thunk { become twice n })",
        ),
        (
            include_str!(
                "rewrite/unformatted/an-inserted-thunk-follows-the-checker-s-elaborations-2.gandr"
            ),
            "call (\n  thunk // owned\n  { twice n }\n)",
        ),
        (
            "thunk { let m = twice n ; return m }",
            "call (thunk { let m = twice n; m })",
        ),
        (
            include_str!(
                "rewrite/unformatted/an-inserted-thunk-follows-the-checker-s-elaborations-3.gandr"
            ),
            "call (\n  // keeper\n  twice n\n)",
        ),
    ] {
        let source = source.replace("thunk { twice n }", body);
        let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
        let oracle = Oracle {
            answer: Answer::Alike,
            asked: Cell::new(0),
        };
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, Some(&oracle)))
            .expect("the source formats");
        assert_eq!(
            formatted.into_text(),
            aliased.replace("call (thunk { twice n })", written),
            "{body}"
        );
    }
}

/// A signature at a suspended returner and the thunk defining it after it
/// are written as the function form that declares them, in either form: a
/// `become`, a statement block and a computation alike. A thunk holding a
/// comment, a graded one and a definition of a value keep their function
/// halves; the graded one, which the checker refuses, keeps both halves, its
/// join withdrawn (#1449).
#[test]
fn a_signed_thunk_merges_into_its_function_form_1449()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/a-signed-thunk-merges-into-its-function-form-1449.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid = |form: Form| {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        let withdrawn: Vec<&str> = formatted
            .withdrawn()
            .iter()
            .map(|withdrawal| withdrawal.declaration.as_str())
            .collect();
        let expected: &[&str] = match form {
            Form::Sugared => &["graded"],
            Form::Explicit | Form::Source => &[],
        };
        assert_eq!(
            withdrawn, expected,
            "only the refused join is withdrawn in {form:?}"
        );
        formatted.into_text()
    };
    expect![[r#"
        def twice(n : Integer) -> Integer { return (n + n) }

        /// Becomes a call.
        @[ runs("2") ]
        def becomes() -> Integer { become twice 1 }

        def block() -> Integer { let m = twice 1; m }

        def pair() -> Integer * Integer { *{1, 2} }

        def commented : () -> Integer = thunk {
          // keeper
          become twice 2
        };

        def graded : +U[1] (-F Integer);
        def graded = thunk[1] { become twice 3 };

        def value : Integer = 3;
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def twice(n : Integer) -> -F Integer { return (n + n) }

        /// Becomes a call.
        @[ runs("2") ]
        def becomes() -> -F Integer { become twice 1 }

        def block() -> -F Integer { let m = twice 1; return m }

        def pair() -> -F *{Integer, Integer} { return *{1, 2} }

        def commented : +U (-F Integer);
        def commented = thunk {
          // keeper
          become twice 2
        };

        def graded : +U[1] (-F Integer);
        def graded = thunk[1] { become twice 3 };

        def value : Integer;
        def value = 3;
    "#]]
    .assert_eq(&laid(Form::Explicit));
}

/// A signature at a suspended function and the thunk holding a lambda after
/// it are written as the function form, each binder a parameter at its
/// domain, in either form: one binder and two, and a dependent domain naming
/// its binder. A lambda short of the arrows and an annotated binder, at its
/// domain or another type, keep their halves; so does a binder other than
/// the one a dependent domain names, where the domain stays dependent: the
/// sugared form writes an unread dependence as a plain domain (#1899).
#[test]
fn a_signed_lambda_merges_into_its_function_form_1899()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-signed-lambda-merges-into-its-function-form-1899.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid = |form: Form| {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(
            formatted.withdrawn(),
            &[],
            "nothing is withdrawn in {form:?}"
        );
        formatted.into_text()
    };
    expect![[r#"
        def identity(n : Integer) -> Integer { n }

        def add(a : Integer, b : Integer) -> Integer { return (a + b) }

        def named(x : Integer) -> Integer { x }

        def stated : Integer -> Integer = thunk { fun (x : Integer) { x } };

        def short : (Integer, Integer) -> Integer = thunk { fun (a) { become add a } };

        def renamed(y : Integer) -> Integer { y }

        def mistyped : Integer -> Integer = thunk { fun (x : String) { 1 } };
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def identity(n : Integer) -> -F Integer { return n }

        def add(a : Integer, b : Integer) -> -F Integer { return (a + b) }

        def named(x : Integer) -> -F Integer { return x }

        def stated : +U (Integer -> -F Integer);
        def stated = thunk { fun (x : Integer) { return x } };

        def short : +U (Integer -> Integer -> -F Integer);
        def short = thunk { fun (a) { become add a } };

        def renamed : +U ((x : Integer) -> -F Integer);
        def renamed = thunk { fun (y) { return y } };

        def mistyped : +U (Integer -> -F Integer);
        def mistyped = thunk { fun (x : String) { return 1 } };
    "#]]
    .assert_eq(&laid(Form::Explicit));
}

/// The sugared form joins a signature and the definition directly after it
/// into one form, a comment inside the value kept; a comment, the
/// definition's own documentation or another declaration between them, a
/// commented signature and a definition before its signature keep the two
/// forms; the explicit form writes every joined definition apart (#2228).
#[test]
fn an_adjacent_pair_joins_into_one_definition_2228()
{
    let grammar = grammar();
    let source =
        include_str!("rewrite/unformatted/an-adjacent-pair-joins-into-one-definition-2228.gandr");
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid = |form: Form| {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(
            formatted.withdrawn(),
            &[],
            "nothing is withdrawn in {form:?}"
        );
        formatted.into_text()
    };
    expect![[r#"
        def three : Integer = 3;

        def four : Integer = 4;

        def five : Integer;
        // parts them
        def five = 5;

        def six : Integer;
        /// Documents the definition.
        def six = 6;

        def seven : Integer;
        def between : Integer = 0;
        def seven = 7;

        def eight : Integer; // on the signature
        def eight = 8;

        def nine : Integer = (
          // inside the value
          9
        );

        def ten = 10;
        def ten : Integer;
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def three : Integer;
        def three = 3;

        def four : Integer;
        def four = 4;

        def five : Integer;
        // parts them
        def five = 5;

        def six : Integer;
        /// Documents the definition.
        def six = 6;

        def seven : Integer;
        def between : Integer;
        def between = 0;
        def seven = 7;

        def eight : Integer; // on the signature
        def eight = 8;

        def nine : Integer;
        def nine = (
          // inside the value
          9
        );

        def ten = 10;
        def ten : Integer;
    "#]]
    .assert_eq(&laid(Form::Explicit));
}

/// A module member's signature and the definition directly after it are
/// written as one form as a top-level pair is, in a nested module too, a
/// thunk's into its function form; a comment between them keeps the two; the
/// explicit form writes each joined member apart (#2255).
#[test]
fn a_module_member_pair_joins_as_a_top_level_one_2255()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-module-member-pair-joins-as-a-top-level-one-2255.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid = |form: Form| {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(
            formatted.withdrawn(),
            &[],
            "nothing is withdrawn in {form:?}"
        );
        formatted.into_text()
    };
    expect![[r#"
        module Outer where {
          /// The one.
          def one : Integer = 1;

          def two : Integer = 2;

          def three : Integer;
          // parts them
          def three = 3;

          def four() -> Integer { 4 }

          module Inner where {
            def five : Integer = 5;
          }
        }
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        module Outer where {
          /// The one.
          def one : Integer;
          def one = 1;

          def two : Integer;
          def two = 2;

          def three : Integer;
          // parts them
          def three = 3;

          def four() -> -F Integer { 4 }

          module Inner where {
            def five : Integer;
            def five = 5;
          }
        }
    "#]]
    .assert_eq(&laid(Form::Explicit));
}

/// A definition's result written `-F B` is written `B` in the sugared form,
/// the returner the lowering inserts, a module member's and a merged function
/// form's among them, and one with an effect row `[E] B`, its row before the
/// type; the explicit form keeps them, and one in a parameter's type stays a
/// type's (#2255).
#[test]
fn a_definition_s_result_leaves_its_returner_unwritten_2255()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-definition-s-result-leaves-its-returner-unwritten-2255.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid = |form: Form| {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(
            formatted.withdrawn(),
            &[],
            "nothing is withdrawn in {form:?}"
        );
        formatted.into_text()
    };
    expect![[r#"
        def inc(x : Integer) -> Integer { x + 1 }

        def pair() -> Integer * Integer { *{1, 2} }

        def spin(x : Integer) -> [Partial] Integer { x }

        def call(f : () -> Integer) -> Integer { force f }

        def four() -> Integer { 4 }

        module Kept where {
          def five() -> Integer { 5 }
        }
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def inc(x : Integer) -> -F Integer { x + 1 }

        def pair() -> -F *{Integer, Integer} { *{1, 2} }

        def spin(x : Integer) -> -F [Partial] Integer { x }

        def call(f : +U (-F Integer)) -> -F Integer { force f }

        def four() -> -F Integer { 4 }

        module Kept where {
          def five() -> -F Integer { 5 }
        }
    "#]]
    .assert_eq(&laid(Form::Explicit));
}

/// A lambda the checker thunks, written bare after its signature, merges
/// into the function form as the thunk holding it does, beside a checker
/// that elaborates both alike; without one the two lower apart and the pair
/// is kept (#2228).
#[test]
fn a_lambda_the_checker_thunks_merges_into_its_function_form_2228()
{
    let grammar = grammar();
    let source = include_str!(
        "rewrite/unformatted/a-lambda-the-checker-thunks-merges-into-its-function-form-2228.gandr"
    );
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let laid = |form: Form, answer: Option<Answer>| {
        let options = FormatOptions {
            form,
            ..FormatOptions::default()
        };
        let oracle = answer.map(|answer| Oracle {
            answer,
            asked: Cell::new(0),
        });
        let checker: Option<&dyn Elaborate> = oracle.as_ref().map(|oracle| {
            let checker: &dyn Elaborate = oracle;
            checker
        });
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, checker))
            .expect("the source formats");
        assert_eq!(
            formatted.withdrawn(),
            &[],
            "nothing is withdrawn in {form:?}"
        );
        formatted.into_text()
    };
    expect![[r#"
        def identity(x : Integer) -> Integer { x }

        def add(a : Integer, b : Integer) -> Integer { a + b }
    "#]]
    .assert_eq(&laid(Form::Sugared, Some(Answer::Alike)));
    expect![[r#"
        def identity(x : Integer) -> -F Integer { x }

        def add(a : Integer, b : Integer) -> -F Integer { a + b }
    "#]]
    .assert_eq(&laid(Form::Explicit, Some(Answer::Alike)));
    expect![[r#"
        def identity : Integer -> Integer = fun (x) { x };

        def add : (Integer, Integer) -> Integer = fun (a) { fun (b) { a + b } };
    "#]]
    .assert_eq(&laid(Form::Sugared, None));
}

/// The formatter writes a type application juxtaposed in either form, as the
/// printer does: `Parcel(Integer)` is `Parcel Integer`. A product argument
/// keeps its parentheses under the sugar, `Parcel (Integer * Integer)`, and
/// its stars under the explicit form, `Parcel *{Integer, Integer}`. A call
/// whose argument in parentheses follows a type variable keeps its call form,
/// `Pair(a, Parcel Integer)`, since the type grammar reads `a (Parcel
/// Integer)` as the call `a(Parcel Integer)`; after a type's name the
/// argument is juxtaposed, `Pair Integer (Parcel Integer)`. A returner
/// encloses a juxtaposition whose first argument takes parentheses, `-F (Pair
/// (Parcel Integer) Integer)`, since the type grammar reads `-F Pair (Parcel
/// Integer) Integer` as the call `Pair(Parcel Integer)` applied on (#5708).
#[test]
fn a_type_application_is_written_juxtaposed_5708()
{
    let grammar = grammar();
    for (parameter, form, expected) in [
        ("Parcel(Integer)", Form::Sugared, "Parcel Integer"),
        ("Parcel(Integer)", Form::Explicit, "Parcel Integer"),
        (
            "Parcel(Integer * Integer)",
            Form::Sugared,
            "Parcel (Integer * Integer)",
        ),
        (
            "Parcel(Integer * Integer)",
            Form::Explicit,
            "Parcel *{Integer, Integer}",
        ),
        (
            "Parcel *{Integer, Integer}",
            Form::Sugared,
            "Parcel (Integer * Integer)",
        ),
        (
            "Parcel (Integer * Integer)",
            Form::Explicit,
            "Parcel *{Integer, Integer}",
        ),
        (
            "Pair(Integer, Parcel(Integer))",
            Form::Sugared,
            "Pair Integer (Parcel Integer)",
        ),
        (
            "Pair(a, Parcel(Integer))",
            Form::Sugared,
            "Pair(a, Parcel Integer)",
        ),
        (
            "Pair(Parcel(Integer), Integer)",
            Form::Sugared,
            "Pair (Parcel Integer) Integer",
        ),
        (
            "+U (Integer -> -F Pair(Parcel(Integer), Integer))",
            Form::Explicit,
            "+U (Integer -> -F (Pair (Parcel Integer) Integer))",
        ),
    ] {
        let source = format!(
            include_str!("rewrite/unformatted/a-type-application-is-written-juxtaposed-5708.gandr"),
            parameter = parameter
        );
        assert_eq!(
            spelled(&grammar, source.as_str(), form, Selection::Every),
            format!(
                include_str!(
                    "rewrite/unformatted/a-type-application-is-written-juxtaposed-5708.gandr"
                ),
                parameter = expected
            ),
            "{parameter} as {form}"
        );
    }
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
    /// this name, at least one of each corpus class, and, in the companion,
    /// the sources the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The `sweeps` profile formats every source.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_source_formats_into_either_form_and_keeps_its_meaning"),
        size: SampleSize(64),
    };

    #[test]
    fn every_source_formats_into_either_form_and_keeps_its_meaning()
    {
        formats_either(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn every_source_formats_into_either_form_and_keeps_its_meaning_changed()
    {
        formats_either(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits formats into either form and once in it.
    ///
    /// # Specification
    /// trivial.
    fn formats_either(sweep: &Sweep)
    {
        let grammar = grammar();
        let sources = sweep.visit(SAMPLE, &corpus::sources().expect("the corpus reads"));
        assert!(
            sources.len() >= sweep.drawn(SAMPLE).0,
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
