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
const EXPLICIT: &str = "\
def pair : #{Integer, String} ;
def triple : #{Integer, String, Unit} ;
def choice : +{Integer, #{String, Unit}} ;
def nested : #{+{Integer, String}, Unit} ;
def lazy : +U &{-F Integer, -F Integer, -F String} ;
def right : +U &{-F Integer, &{-F Integer, -F String}} ;
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
def right : +U (-F Integer & (-F Integer & -F String)) ;
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
    let source = "\
def step : +U[ω] (Integer -> -F Integer) ;
def lazy : +U[inf] &{-F Integer, -F Integer} ;
def noted : +U[/* every use */ ω] (-F Integer) ;
def once : +U[1] (Integer -> -F Integer) ;
theory Counting {
  sort T : Type;
  oper next : +U[ω] (T -> -F T);
  oper add : +U[ω] (T -> T -> -F T);
}
";
    for (form, expected) in [
        (
            Form::Sugared,
            "\
def step : Integer => Integer ;
def lazy : +U (-F Integer & -F Integer) ;
def noted : +U[/* every use */ ω] (-F Integer) ;
def once : +U[1] (Integer -> -F Integer) ;
theory Counting {
  sort T : Type;
  oper next : T => T;
  oper add : +U (T -> T -> -F T);
}
",
        ),
        (
            Form::Explicit,
            "\
def step : +U (Integer -> -F Integer) ;
def lazy : +U &{-F Integer, -F Integer} ;
def noted : +U[/* every use */ ω] (-F Integer) ;
def once : +U[1] (Integer -> -F Integer) ;
theory Counting {
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

/// #1327: the sugared form leaves out a tail's `return` of a value, in a
/// body, a match arm, a block and a nested function, as the lowering would
/// infer it; an early `return`, one of a computation, one written as a
/// statement, one under `explicit_exits` and one with a comment after its
/// keyword keep it, and the explicit form writes the source as it was given.
#[test]
fn a_tail_return_is_left_out_where_the_lowering_would_infer_it_1327()
{
    let grammar = grammar();
    let source = "\
data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }

def succeeded(n : Nat) -> -F Nat {
  return Succ(n)
}

def early(k : Nat) -> -F Nat {
  case k {
    Zero => return k,
    Succ(j) => {
      run q <- case j {
        Zero => return j,
        Succ(r) => pure r,
      } ;
      pure q
    },
  }
}

def computed(n : Nat) -> -F Nat {
  return succeeded(n)
}

def stated(n : Nat) -> -F Nat {
  return n ;
}

def nested(n : Nat) -> -F (+U (Nat -> -F Nat)) {
  return thunk { fn (x) { return Succ(x) } }
}

def blocked(n : Nat) -> -F Nat {
  case n {
    Zero => { run y <- succeeded(n) ; return y },
    Succ(p) => p,
  }
}

def noted(n : Nat) -> -F Nat {
  return /* the argument */ n
}

@[ explicit_exits ]
def asked(n : Nat) -> -F Nat {
  return n
}
";
    let sugared = "\
data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }

def succeeded(n : Nat) -> Nat {
  Succ(n)
}

def early(k : Nat) -> Nat {
  case k {
    Zero => k,
    Succ(j) => {
      run q <- case j {
        Zero => return j,
        Succ(r) => pure r,
      } ;
      pure q
    },
  }
}

def computed(n : Nat) -> Nat {
  return succeeded(n)
}

def stated(n : Nat) -> Nat {
  return n ;
}

def nested(n : Nat) -> Nat => Nat {
  thunk { fn (x) { Succ(x) } }
}

def blocked(n : Nat) -> Nat {
  case n {
    Zero => { run y <- succeeded(n) ; y },
    Succ(p) => p,
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

/// #1327: the sugared form writes a value-function alias at its shortest:
/// one domain unparenthesised however deeply written, nested aliases among
/// them, and a binder nothing later reads left out; a list of domains, a
/// binder a later domain or the result reads, and a domain with a comment
/// keep their spelling.
#[test]
fn a_value_function_alias_is_written_at_its_shortest_1327()
{
    let grammar = grammar();
    let source = "\
def step : (Integer) => Integer ;
def named : (x : Integer) => Integer ;
def nested : ((Integer)) => Integer ;
def twice : (Integer) => (Integer) => Integer ;
def unread : (a : Type, b : Integer) => a ;
def pair : (Integer, String) => Unit ;
def dependent : (a : Type, a) => a ;
def noted : (/* the count */ Integer) => Integer ;
";
    let sugared = "\
def step : Integer => Integer ;
def named : Integer => Integer ;
def nested : Integer => Integer ;
def twice : Integer => Integer => Integer ;
def unread : (a : Type, Integer) => a ;
def pair : (Integer, String) => Unit ;
def dependent : (a : Type, a) => a ;
def noted : (/* the count */ Integer) => Integer ;
";
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
/// #1003: the inverse is taken at the circle's point, where the reflexivity
/// it moves is the empty word a written `here(Base)` reads as.
#[test]
fn an_inverse_and_an_action_on_a_path_move_both_ways_778()
{
    let grammar = grammar();
    let sugared = format!(
        "{CIRCLE}def spin(x : Circle) -> -F Circle {{
  x
}}

def undone : Path(Path(Circle, Base, Base), back(loop), back(loop)) ;

def spun : Path(Path(Circle, Base, Base), cong(spin, loop), cong(spin, loop)) ;
"
    );
    let explicit = format!(
        "{CIRCLE}def spin(x : Circle) -> -F Circle {{
  x
}}

def undone : Path(
  Path(Circle, Base, Base),
  transport(\\a. Path(Circle, a, Base), loop, here(Base)),
  transport(\\a. Path(Circle, a, Base), loop, here(Base))
) ;

def spun : Path(
  Path(Circle, Base, Base),
  transport(\\a. Path(Circle, spin(Base), spin(a)), loop, here(spin(Base))),
  transport(\\a. Path(Circle, spin(Base), spin(a)), loop, here(spin(Base)))
) ;
"
    );
    let back = format!(
        "{CIRCLE}def spin(x : Circle) -> Circle {{
  x
}}

def undone : Path(
  Path(Circle, Base, Base),
  back(loop),
  back(loop)
) ;

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

/// #985: a composite read as a value, alone or under `back`, moves both
/// ways: desugared, each composite is its transport, written where a value
/// is read, and sugared back it is the composite again, since a written
/// transport read as a value lowers to the value it returns.
#[test]
fn a_composite_read_as_a_value_moves_both_ways_985()
{
    let grammar = grammar();
    let sugared = format!(
        "{CIRCLE}def two : Path(Circle, Base, Base) = loop then loop ;

def undone : Path(Circle, Base, Base) = back(loop then loop) ;
"
    );
    let explicit = format!(
        "{CIRCLE}def two : Path(Circle, Base, Base) ;
def two = transport(\\a. Path(Circle, Base, a), loop, loop) ;

def undone : Path(Circle, Base, Base) ;
def undone = transport(
  \\a. Path(Circle, a, Base),
  transport(\\a. Path(Circle, Base, a), loop, loop),
  here(Base)
) ;
"
    );
    for (source, form, expected) in [
        (&sugared, Form::Explicit, &explicit),
        (&explicit, Form::Sugared, &sugared),
        (&sugared, Form::Sugared, &sugared),
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
        "{CIRCLE}def twice(p: Path(Circle, Base, Base)) -> Path(Circle, Base, Base) {{
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

/// A composite or an inverse standing as the operand of a transport a body
/// runs keeps its transport too, nested to any depth: the printer writes a
/// derived operation there as the transport it derives, nothing there
/// stating its type.
#[test]
fn a_derived_operand_of_a_kept_transport_keeps_its_transport()
{
    let grammar = grammar();
    for body in [
        "transport(\\a. Path(Circle, Base, a), transport(\\a. Path(Circle, Base, a), p, p), p)",
        "transport(\\a. Path(Circle, Base, a), p, transport(\\a. Path(Circle, a, Base), \
         transport(\\a. Path(Circle, Base, a), p, p), here(Base)))",
    ] {
        let source = format!(
            "{CIRCLE}def twice(p: Path(Circle, Base, Base)) -> Path(Circle, Base, Base) \
             {{\n  {body}\n}}\n"
        );
        let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
        let laid_out = format(&grammar, &parsed, FormatOptions::default())
            .expect("the source lays out")
            .into_text();
        let options = FormatOptions {
            form: Form::Sugared,
            ..FormatOptions::default()
        };
        let formatted = format(&grammar, &parsed, options).expect("the source formats");
        assert_eq!(formatted.withdrawn(), &[], "{body}");
        assert_eq!(
            formatted.into_text(),
            laid_out,
            "{body}: only the layout moves"
        );
    }
}

/// A parenthesised list after a rule's `<=>` is the rule's outputs, not a
/// tuple: the explicit form keeps it, while a tuple read as a value beside it
/// is written `#{…}`.
#[test]
fn a_rule_s_outputs_are_not_a_tuple()
{
    let grammar = grammar();
    let rules = "data NatDiv : Type {\n  Zero : NatDiv;\n  Succ : (n : NatDiv) --> NatDiv;\n  \
                 oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);\n  rule \
                 divmod(m, Zero) <=> (Zero, m);\n}\n\n";
    assert_eq!(
        spelled(
            &grammar,
            format!("{rules}def pair = (1, 2) ;\n").as_str(),
            Form::Explicit,
            Selection::Every
        ),
        format!("{rules}def pair = #{{1, 2}} ;\n")
    );
}

/// A composite of two flows is no path composite: it has no transport to
/// write, so the explicit form keeps its `then`.
#[test]
fn a_composite_of_flows_keeps_its_then()
{
    let grammar = grammar();
    let source = "module Evolution {\n  type Old = +{ report : !String. end };\n  type New = +{ \
                  report : !String. end, pause : end };\n  def sub : Flow(Type, Old, New);\n  \
                  def sub = sim(Old, New);\n  def kept : Flow(Type, Old, Old);\n  def kept = \
                  stay(Old);\n  def widened() -> -F Flow(Type, Old, New) {\n    become kept then \
                  sub\n  }\n}\n";
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
        "transport(\\a. Integer, loop, 5)",
        "transport(+U (Circle -> -F Integer), loop, 5)",
        "transport(\\a. Path(Circle, a, a), loop, here(Base))",
        "transport(\\a. Path(Circle, Base, Base), loop, here(Base))",
        "transport(\\a. Path(Circle, a, Base), loop, loop)",
        "transport(\\a. Path(Circle, Base, a), loop)",
    ] {
        let source = format!("{CIRCLE}def moved : Integer = {value} ;\n");
        assert_eq!(
            spelled(&grammar, source.as_str(), Form::Sugared, Selection::Every),
            source
        );
    }
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

/// #2166: a functor's instantiation copies its members, so a copy's composite
/// stands at the functor body's span; its motive, spelled under the argument,
/// is never the functor's own, and the explicit form keeps `back` where the
/// functor cannot spell one.
#[test]
fn a_functor_s_composite_takes_no_motive_from_its_instantiation_2166()
{
    let grammar = grammar();
    let source = "theory Semi {
  sort M : Type;
  oper mul : (x : M, y : M) --> M;
  rule assoc : mul(mul(x, y), z) ==> mul(x, mul(y, z));
}

module Reassociating(S : Model(Semi)) {
  def reassoc(x : S.M, y : S.M, z : S.M) -> -F Path(
    S.M,
    S.mul(x, S.mul(y, z)),
    S.mul(S.mul(x, y), z)
  ) {
    back(S.assoc(x, y, z))
  }
}

module OnePoint : Model(Semi) {
  type M = Unit;

  def mul(a : Unit, b : Unit) -> -F Unit { unit }

  def assoc(x : Unit, y : Unit, z : Unit) -> -F Path(
    Unit,
    mul(mul(x, y), z),
    mul(x, mul(y, z))
  ) {
    here(unit)
  }
}

module OnePointReassociated = Reassociating(OnePoint) ;
";
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Explicit,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    assert_eq!(<&str>::from(formatted.text()), source);
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
        def joined(a: Type, b: Type, c: Type, p: Path(Type, a, b), q: Path(Type, b, c)) -> Path(
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

def kept(a: Nat, b: Nat, q: Path(Nat, a, b)) -> Path(Nat, b, a) {
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
def motive : Type -> Type = \\X. X => X ;
def suspended : Type -> Type = \\X. () => X ;
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

/// #2246: a manifest sort's carrier binds no looser than a sum, as the printer
/// writes it: a thunk type fixed there takes the alias parenthesised, and the
/// alias fixed there takes the thunk with the parenthesis it needed gone.
#[test]
fn a_manifest_carrier_is_parenthesised_as_the_printer_writes_it_2246()
{
    let grammar = grammar();
    let theory = "theory Pointed {\n  sort M : Type;\n  oper one : M;\n}\n\n";
    let explicit =
        format!("{theory}def endo : Model(Pointed) with sort M = +U (Integer -> -F Integer) ;\n");
    let sugared =
        format!("{theory}def endo : Model(Pointed) with sort M = (Integer => Integer) ;\n");
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

        def onType(t: Type) -> Type {
          return (t => t)
        }

        def flat(a: Nat, b: Nat, q: Path(Nat, a, b), v: Nat) -> Nat {
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
/// Its arms' tail `return`s are left out (#1327).
#[test]
fn a_match_over_a_stated_sum_is_sugared_791()
{
    let grammar = grammar();
    let matched = |stated: &str, exit: &str, result: &str| {
        format!(
            "def pick(t : {stated}) -> {result} {{\n  case t {{\n    +{{.1 = x}} => {exit}x,\n    _ => {exit}0\n  }}\n}}"
        )
    };
    let source = format!(
        "{}\n\ndef pair : #{{Integer, String}} ;\n",
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
                "{}\n\ndef pair : Integer * String ;\n",
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
    let formatted = format_beside(&grammar, &parsed, options, (beside, None))
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

/// A `run` statement the lowering lists as linear follows the checker: it is
/// written at its read where the checker elaborates both spellings to one
/// body, withdrawn and reported where it elaborates them otherwise, and kept
/// with nothing reported where it refuses the source as written. The
/// checker's own verdict on a real source is the dispatcher's to witness.
#[test]
fn a_linear_run_follows_the_checker_s_elaborations()
{
    let grammar = grammar();
    let source = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                  \n\
                  def twice(n : Nat) -> Nat { Succ(Succ(n)) }\n\
                  \n\
                  def field(n : Nat) -> Nat {\n  run m <- twice(n) ;\n  Succ(m)\n}\n";
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
    let written = source.replace(
        "\n  run m <- twice(n) ;\n  Succ(m)\n",
        "\n  Succ(twice(n))\n",
    );
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
    let source = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                  \n\
                  def twice(n : Nat) -> Nat { Succ(Succ(n)) }\n\
                  \n\
                  def again(n : Nat) -> Nat { return twice(n) }\n";
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
        (source.replace("return twice(n)", "twice(n)"), Vec::new()),
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
    let head = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                \n\
                def twice(n : Nat) -> Nat { Succ(Succ(n)) }\n\
                \n\
                def both(m : Nat, k : Nat) -> Nat { Succ(m) }\n\
                \n\
                def field(n : Nat) -> Nat {\n";
    for (body, written) in [
        (
            "  run m <- twice(n) ;\n  run k <- twice(n) ;\n  both(m, k)\n",
            "  both(twice(n), twice(n))\n",
        ),
        (
            "  run m <- twice(n) ;\n  // between\n  run k <- twice(n) ;\n  both(m, k)\n",
            "  // between\n  both(twice(n), twice(n))\n",
        ),
        (
            "  run m <- twice(n) ;\n  run k <- twice(m) ;\n  both(k, m)\n",
            "  run m <- twice(n) ;\n  both(twice(m), m)\n",
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
    let head = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                \n\
                def twice(n : Nat) -> Nat { Succ(Succ(n)) }\n\
                \n\
                def both(m : Nat, k : Nat) -> Nat { Succ(m) }\n\
                \n";
    for (body, written) in [
        (
            "def armed(a : Nat) -> Nat { case a { Zero => Zero, Succ(b) => { run d <- twice(b) ; Succ(d) } } }\n",
            "def armed(a : Nat) -> Nat { case a { Zero => Zero, Succ(b) => Succ(twice(b)) } }\n",
        ),
        (
            "def paired(a : Nat) -> Nat { case a { Zero => Zero, Succ(b) => { run e <- twice(b) ; run f <- twice(Zero) ; both(e, f) } } }\n",
            "def paired(a : Nat) -> Nat { case a { Zero => Zero, Succ(b) => both(twice(b), twice(Zero)) } }\n",
        ),
        (
            "def reread(a : Nat) -> Nat { case a { Zero => Zero, Succ(b) => { run g <- twice(b) ; run h <- twice(g) ; both(h, g) } } }\n",
            "def reread(a : Nat) -> Nat {\n  case a { Zero => Zero, Succ(b) => { run g <- twice(b) ; both(twice(g), g) } }\n}\n",
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
        Withdrawn::Unspelled,
        Withdrawn::Read(String::from("reader")),
    ]
    .map(|reason| reason.to_string());
    apart(&withdrawals);
    for (index, carried) in [(0, "the refusal"), (2, "the refusal"), (4, "`reader`")] {
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
            "tuple",
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
    let source = "codata Stream(a : Type) : Type[-] {\n  head : a;\n  tail : Stream(a);\n}\n\
                  \n\
                  world seat;\n\
                  \n\
                  module Pair :> #{ type Kept, one : Kept } {\n  type Kept = Integer;\n  def \
                  one = 1;\n}\n\
                  \n\
                  def lost() -> Integer { migrate [nowhere] { pure 1 } }\n\
                  \n\
                  def pair : #{Integer, String} ;\n";
    let parsed = parse(&grammar, SourceText::from(source)).expect("the source parses");
    let options = FormatOptions {
        form: Form::Sugared,
        ..FormatOptions::default()
    };
    let formatted = format(&grammar, &parsed, options).expect("the source formats");
    assert_eq!(formatted.withdrawn(), &[]);
    assert_eq!(
        formatted.into_text(),
        source.replace("#{Integer, String}", "Integer * String")
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
    let source = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                  \n\
                  def twice(n : Nat) -> Nat { Succ(Succ(n)) }\n\
                  \n\
                  def call(f : +U (-F Nat)) -> Nat { force f }\n\
                  \n\
                  def field(n : Nat) -> Nat { call(thunk { twice(n) }) }\n";
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
    let aliased = source.replace("+U (-F Nat)", "() => Nat");
    assert_eq!(
        format(Some(Answer::Alike)),
        (
            aliased.replace("call(thunk { twice(n) })", "call(twice(n))"),
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
            "thunk { become twice(n) }",
            "call(thunk { become twice(n) })",
        ),
        (
            "thunk // owned\n  { twice(n) }",
            "call(\n  thunk // owned\n  { twice(n) }\n)",
        ),
        (
            "thunk { run m <- twice(n) ; return m }",
            "call(thunk { run m <- twice(n) ; m })",
        ),
        (
            "thunk {\n    // kept\n    twice(n)\n  }",
            "call(\n  // kept\n  twice(n)\n)",
        ),
    ] {
        let source = source.replace("thunk { twice(n) }", body);
        let parsed = parse(&grammar, SourceText::from(source.as_str())).expect("the source parses");
        let oracle = Oracle {
            answer: Answer::Alike,
            asked: Cell::new(0),
        };
        let formatted = format_beside(&grammar, &parsed, options, (Beside::Alone, Some(&oracle)))
            .expect("the source formats");
        assert_eq!(
            formatted.into_text(),
            aliased.replace("call(thunk { twice(n) })", written),
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
    let source = "def twice(n : Integer) -> -F Integer { return (n + n) }\n\
                  \n\
                  /// Becomes a call.\n\
                  @[ runs(\"2\") ]\n\
                  def becomes : +U (-F Integer) ;\n\
                  def becomes = thunk { become twice(1) } ;\n\
                  \n\
                  def block : () => Integer ;\n\
                  def block = thunk { run m <- twice(1) ; return m } ;\n\
                  \n\
                  def pair : () => Integer * Integer ;\n\
                  def pair = thunk { return (1, 2) } ;\n\
                  \n\
                  def commented : () => Integer ;\n\
                  def commented = thunk {\n  // kept\n  become twice(2)\n} ;\n\
                  \n\
                  def graded : +U[1] (-F Integer) ;\n\
                  def graded = thunk[1] { become twice(3) } ;\n\
                  \n\
                  def value : Integer ;\n\
                  def value = 3 ;\n";
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
        def becomes() -> Integer { become twice(1) }

        def block() -> Integer { run m <- twice(1) ; m }

        def pair() -> Integer * Integer { (1, 2) }

        def commented : () => Integer = thunk {
          // kept
          become twice(2)
        } ;

        def graded : +U[1] (-F Integer) ;
        def graded = thunk[1] { become twice(3) } ;

        def value : Integer = 3 ;
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def twice(n : Integer) -> -F Integer { return (n + n) }

        /// Becomes a call.
        @[ runs("2") ]
        def becomes() -> -F Integer { become twice(1) }

        def block() -> -F Integer { run m <- twice(1) ; return m }

        def pair() -> -F #{Integer, Integer} { return #{1, 2} }

        def commented : +U (-F Integer) ;
        def commented = thunk {
          // kept
          become twice(2)
        } ;

        def graded : +U[1] (-F Integer) ;
        def graded = thunk[1] { become twice(3) } ;

        def value : Integer ;
        def value = 3 ;
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
    let source = "def identity : +U (Integer -> -F Integer) ;\n\
                  def identity = thunk { fn (n) { return n } } ;\n\
                  \n\
                  def add : (Integer, Integer) => Integer ;\n\
                  def add = thunk { fn (a) { fn (b) { return (a + b) } } } ;\n\
                  \n\
                  def named : +U ((x : Integer) -> -F Integer) ;\n\
                  def named = thunk { fn (x) { return x } } ;\n\
                  \n\
                  def stated : Integer => Integer ;\n\
                  def stated = thunk { fn (x : Integer) { return x } } ;\n\
                  \n\
                  def short : +U (Integer -> Integer -> -F Integer) ;\n\
                  def short = thunk { fn (a) { become add(a) } } ;\n\
                  \n\
                  def renamed : +U ((x : Integer) -> -F Integer) ;\n\
                  def renamed = thunk { fn (y) { return y } } ;\n\
                  \n\
                  def mistyped : Integer => Integer ;\n\
                  def mistyped = thunk { fn (x : String) { return 1 } } ;\n";
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

        def stated : Integer => Integer = thunk { fn (x : Integer) { x } } ;

        def short : (Integer, Integer) => Integer = thunk { fn (a) { become add(a) } } ;

        def renamed(y : Integer) -> Integer { y }

        def mistyped : Integer => Integer = thunk { fn (x : String) { 1 } } ;
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def identity(n : Integer) -> -F Integer { return n }

        def add(a : Integer, b : Integer) -> -F Integer { return (a + b) }

        def named(x : Integer) -> -F Integer { return x }

        def stated : +U (Integer -> -F Integer) ;
        def stated = thunk { fn (x : Integer) { return x } } ;

        def short : +U (Integer -> Integer -> -F Integer) ;
        def short = thunk { fn (a) { become add(a) } } ;

        def renamed : +U ((x : Integer) -> -F Integer) ;
        def renamed = thunk { fn (y) { return y } } ;

        def mistyped : +U (Integer -> -F Integer) ;
        def mistyped = thunk { fn (x : String) { return 1 } } ;
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
    let source = "def three : Integer ;\n\
                  def three = 3 ;\n\
                  \n\
                  def four : Integer = 4 ;\n\
                  \n\
                  def five : Integer ;\n\
                  // parts them\n\
                  def five = 5 ;\n\
                  \n\
                  def six : Integer ;\n\
                  /// Documents the definition.\n\
                  def six = 6 ;\n\
                  \n\
                  def seven : Integer ;\n\
                  def between : Integer = 0 ;\n\
                  def seven = 7 ;\n\
                  \n\
                  def eight : Integer ; // on the signature\n\
                  def eight = 8 ;\n\
                  \n\
                  def nine : Integer ;\n\
                  def nine = (\n  // inside the value\n  9\n) ;\n\
                  \n\
                  def ten = 10 ;\n\
                  def ten : Integer ;\n";
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
        def three : Integer = 3 ;

        def four : Integer = 4 ;

        def five : Integer ;
        // parts them
        def five = 5 ;

        def six : Integer ;
        /// Documents the definition.
        def six = 6 ;

        def seven : Integer ;
        def between : Integer = 0 ;
        def seven = 7 ;

        def eight : Integer ; // on the signature
        def eight = 8 ;

        def nine : Integer = (
          // inside the value
          9
        ) ;

        def ten = 10 ;
        def ten : Integer ;
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def three : Integer ;
        def three = 3 ;

        def four : Integer ;
        def four = 4 ;

        def five : Integer ;
        // parts them
        def five = 5 ;

        def six : Integer ;
        /// Documents the definition.
        def six = 6 ;

        def seven : Integer ;
        def between : Integer ;
        def between = 0 ;
        def seven = 7 ;

        def eight : Integer ; // on the signature
        def eight = 8 ;

        def nine : Integer ;
        def nine = (
          // inside the value
          9
        ) ;

        def ten = 10 ;
        def ten : Integer ;
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
    let source = "module Outer {\n\
                  \x20 /// The one.\n\
                  \x20 def one : Integer ;\n\
                  \x20 def one = 1 ;\n\
                  \n\
                  \x20 def two : Integer = 2 ;\n\
                  \n\
                  \x20 def three : Integer ;\n\
                  \x20 // parts them\n\
                  \x20 def three = 3 ;\n\
                  \n\
                  \x20 def four : () => Integer ;\n\
                  \x20 def four = thunk { 4 } ;\n\
                  \n\
                  \x20 module Inner {\n\
                  \x20   def five : Integer ;\n\
                  \x20   def five = 5 ;\n\
                  \x20 }\n\
                  }\n";
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
        module Outer {
          /// The one.
          def one : Integer = 1 ;

          def two : Integer = 2 ;

          def three : Integer ;
          // parts them
          def three = 3 ;

          def four() -> Integer { 4 }

          module Inner {
            def five : Integer = 5 ;
          }
        }
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        module Outer {
          /// The one.
          def one : Integer ;
          def one = 1 ;

          def two : Integer ;
          def two = 2 ;

          def three : Integer ;
          // parts them
          def three = 3 ;

          def four() -> -F Integer { 4 }

          module Inner {
            def five : Integer ;
            def five = 5 ;
          }
        }
    "#]]
    .assert_eq(&laid(Form::Explicit));
}

/// A definition's result written `-F B` is written `B` in the sugared form,
/// the returner the lowering inserts, a module member's and a merged function
/// form's among them; a returner with an effect row and the explicit form keep
/// theirs, and one in a parameter's type stays a type's (#2255).
#[test]
fn a_definition_s_result_leaves_its_returner_unwritten_2255()
{
    let grammar = grammar();
    let source = "def inc(x : Integer) -> -F Integer { x + 1 }\n\
                  \n\
                  def pair() -> -F (Integer * Integer) { (1, 2) }\n\
                  \n\
                  def spin(x : Integer) -> -F [Div] Integer { x }\n\
                  \n\
                  def call(f : +U (-F Integer)) -> -F Integer { force f }\n\
                  \n\
                  def four : () => Integer ;\n\
                  def four = thunk { 4 } ;\n\
                  \n\
                  module Kept {\n\
                  \x20 def five() -> -F Integer { 5 }\n\
                  }\n";
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

        def pair() -> Integer * Integer { (1, 2) }

        def spin(x : Integer) -> -F [Div] Integer { x }

        def call(f : () => Integer) -> Integer { force f }

        def four() -> Integer { 4 }

        module Kept {
          def five() -> Integer { 5 }
        }
    "#]]
    .assert_eq(&laid(Form::Sugared));
    expect![[r#"
        def inc(x : Integer) -> -F Integer { x + 1 }

        def pair() -> -F #{Integer, Integer} { #{1, 2} }

        def spin(x : Integer) -> -F [Div] Integer { x }

        def call(f : +U (-F Integer)) -> -F Integer { force f }

        def four() -> -F Integer { 4 }

        module Kept {
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
    let source = "def identity : Integer => Integer ;\n\
                  def identity = fn (x) { x } ;\n\
                  \n\
                  def add : (Integer, Integer) => Integer ;\n\
                  def add = fn (a) { fn (b) { a + b } } ;\n";
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
        def identity : Integer => Integer = fn (x) { x } ;

        def add : (Integer, Integer) => Integer = fn (a) { fn (b) { a + b } } ;
    "#]]
    .assert_eq(&laid(Form::Sugared, None));
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
