//! The binders in scope at an offset, and what each written name resolved to:
//! what a name written there would resolve to, and what one written there
//! did, kept for a declaration the lowering refused.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::Resolution;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

/// `source`'s module, lowered on its own.
///
/// # Specification
/// trivial.
fn lowered(source: SourceText<'_>) -> LoweredModule<'_>
{
    let grammar = built_in().expect("the built-in grammar builds");
    let parsed = parse(&grammar, source).expect("the source parses");
    let mut arena = CoreArena::new();
    lower_module(
        &grammar,
        parsed.tree(),
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .expect("the module lowers")
}

/// The names of the binders in scope at the first byte of the first
/// occurrence of `needle` in `source`, innermost first.
///
/// # Specification
/// trivial.
fn in_scope(
    source: SourceText<'_>,
    needle: SourceText<'_>,
) -> Vec<String>
{
    let text = <&str>::from(source);
    let at = text.find(<&str>::from(needle)).expect("the needle occurs");
    lowered(source)
        .in_scope()
        .binders_at(ByteOffset::from(at))
        .filter_map(|site| text.get(usize::from(site.start()) .. usize::from(site.end())))
        .map(String::from)
        .collect()
}

/// Each name `source` writes after the first occurrence of `from` that the
/// lowering resolved, beside the name tile of the binder, declaration or
/// constructor it names, in written order.
///
/// # Specification
/// trivial.
fn resolved(
    source: SourceText<'_>,
    from: SourceText<'_>,
) -> Vec<(String, String)>
{
    let text = <&str>::from(source);
    let start = text.find(<&str>::from(from)).expect("the start occurs");
    let module = lowered(source);
    let spelled = |span: ByteSpan| {
        String::from(
            text.get(usize::from(span.start()) .. usize::from(span.end()))
                .unwrap_or_default(),
        )
    };
    let declared: BTreeMap<_, _> = module
        .declarations()
        .iter()
        .map(|declaration| (declaration.constant(), declaration.named()))
        .collect();
    module
        .resolutions()
        .iter()
        .filter(|&&(span, _)| usize::from(span.start()) >= start)
        .map(|&(span, resolution)| {
            let site = match resolution {
                Resolution::Binder(named) | Resolution::Constructor { named, .. } => named,
                Resolution::Declaration(constant) => {
                    declared.get(&constant).copied().unwrap_or(span)
                },
            };
            (spelled(span), spelled(site))
        })
        .collect()
}

/// A family, and a recursive function matching on it: each arm sees the
/// parameters, the recursion and its own pattern's binder alone.
const WRITTEN: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec \
                       plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    \
                       Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef k : +U (Nat -> -F Nat) ;\ndef k \
                       = thunk { fn (x) { return Succ(x) } } ;\n";

/// [`WRITTEN`] with the recursive call not yet written in full: `pl` resolves
/// to nothing, and the lowering refuses `plus`.
const TYPING: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec \
                      plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    \
                      Succ(p) => Succ(pl)\n  }\n}\n";

#[test]
fn the_binders_in_scope_are_the_innermost_reading_s_chain()
{
    let at = |needle: &'static str| in_scope(SourceText::from(WRITTEN), SourceText::from(needle));
    assert_eq!(
        at("p))"),
        ["p", "m", "plus", "n"],
        "an arm's body: its binder, then the function's"
    );
    assert_eq!(
        at("n,\n"),
        ["m", "plus", "n"],
        "a sibling arm: the function's, never `p`"
    );
    assert_eq!(at("x) }"), ["x"], "a lambda's body: its binder alone");
    assert_eq!(
        at("+U (Nat"),
        Vec::<String>::new(),
        "a signature reads under no binder"
    );
}

/// #831: the declaration being typed is refused, and its binders stay in
/// scope where the name not yet written in full stands.
#[test]
fn the_binders_in_scope_are_kept_for_a_refused_declaration_831()
{
    assert_eq!(
        in_scope(SourceText::from(TYPING), SourceText::from("pl)")),
        ["p", "m", "plus", "n"],
        "the arm's binder, then the function's, though `plus` is refused"
    );
}

#[test]
fn each_written_name_keeps_what_it_resolved_to()
{
    let pair = |name: &str, site: &str| (String::from(name), String::from(site));
    assert_eq!(
        resolved(SourceText::from(WRITTEN), SourceText::from("def k =")),
        [pair("Succ", "Succ"), pair("x", "x")],
        "a constructor head names its tile in the family, a parameter its binder"
    );
}

#[test]
fn a_name_in_a_type_keeps_what_it_resolved_to()
{
    let pair = |name: &str, site: &str| (String::from(name), String::from(site));
    assert_eq!(
        resolved(SourceText::from(WRITTEN), SourceText::from("def k :")),
        [
            pair("Nat", "Nat"),
            pair("Nat", "Nat"),
            pair("Succ", "Succ"),
            pair("x", "x")
        ],
        "a family named in a claim names its declaration"
    );
    let fields = "def r : #{ con : Type, tm : +U (con -> -F Type), t : tm(con) } ;\n";
    assert_eq!(
        resolved(SourceText::from(fields), SourceText::from("def r")),
        [pair("con", "con"), pair("tm", "tm"), pair("con", "con")],
        "a field named in a later field's type names its binder, applied or not"
    );
}

/// #836: a constructor applied to no field yet is refused, and its name keeps
/// what it names.
#[test]
fn a_refused_declaration_keeps_the_names_it_resolved_836()
{
    let typing = WRITTEN.replace("Succ(x)", "Succ()");
    assert_eq!(
        resolved(
            SourceText::from(typing.as_str()),
            SourceText::from("def k =")
        ),
        [(String::from("Succ"), String::from("Succ"))],
        "the constructor's tile in its family, though `k` is refused"
    );
}

/// A rose tree's node and forest, one block, measured by two functions that
/// call each other through their descent marker.
const MUTUAL: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\nrec {\n  \
                      data Rose : Type { Node : (kids : Forest) --> Rose; }\n  data Forest : \
                      Type { Empty : Forest; More : (head : Rose, tail : Forest) --> Forest; \
                      }\n  def rec size(t : Rose) -> -F Nat { case t { Node(kids) => { run s \
                      <- sizes[<](kids); return Succ(s) } } }\n  def rec sizes(ts : Forest) \
                      -> -F Nat { case ts { Empty => return Zero, More(t, rest) => { run a <- \
                      size[<](t); sizes[<](rest) } } }\n}\n";

/// #827: a call head written with its descent marker keeps what its name
/// names at the name alone, the marker aside: the function's own fixpoint
/// binder, or a sibling member's declaration.
#[test]
fn a_marked_call_head_keeps_its_name_s_referent_827()
{
    let pair = |name: &str, site: &str| (String::from(name), String::from(site));
    assert_eq!(
        resolved(SourceText::from(WRITTEN), SourceText::from("plus[<]")),
        [
            pair("plus", "plus"),
            pair("n", "n"),
            pair("p", "p"),
            pair("Nat", "Nat"),
            pair("Nat", "Nat"),
            pair("Succ", "Succ"),
            pair("x", "x")
        ],
        "the function's own call names its binder from its name"
    );
    assert_eq!(
        resolved(SourceText::from(MUTUAL), SourceText::from("sizes[<](kids)")),
        [
            pair("sizes", "sizes"),
            pair("kids", "kids"),
            pair("Succ", "Succ"),
            pair("s", "s"),
            pair("Forest", "Forest"),
            pair("Nat", "Nat"),
            pair("ts", "ts"),
            pair("Zero", "Zero"),
            pair("size", "size"),
            pair("t", "t"),
            pair("sizes", "sizes"),
            pair("rest", "rest")
        ],
        "a sibling's call names its declaration from its name"
    );
}

/// #843: a call typed up to its next argument without its `)` is refused,
/// and its head keeps what it names.
#[test]
fn an_unclosed_call_keeps_its_head_s_referent_843()
{
    let typing = alloc::format!("{WRITTEN}def f : +U (-F Nat) ;\ndef f = thunk {{ plus(Zero, ");
    assert_eq!(
        resolved(
            SourceText::from(typing.as_str()),
            SourceText::from("plus(Zero")
        ),
        [(String::from("plus"), String::from("plus"))],
        "the head names its declaration, though the call and `f` are refused"
    );
}

/// #1265: a declaration the lowering refuses keeps what each name written
/// inside the refused form names: a parameter inside a `drop` of no endpoint,
/// a forked endpoint inside a reserved `dup`, and a parameter inside a `case`
/// whose block is refused for its joins, each its own binder.
#[test]
fn a_use_inside_a_refused_form_keeps_its_referent_1265()
{
    let parameter = "def dropped(seat : Integer) -> -F Unit {\n  drop(seat)\n}\n";
    assert_eq!(
        resolved(SourceText::from(parameter), SourceText::from("drop(")),
        [(String::from("seat"), String::from("seat"))],
        "the parameter used inside the refused `drop` names its binder"
    );
    let endpoint = "def forked() -> -F Unit {\n  fork (seat : end) { close(seat) } as desk;\n  \
                    dup(desk)\n}\n";
    assert_eq!(
        resolved(SourceText::from(endpoint), SourceText::from("dup(")),
        [(String::from("desk"), String::from("desk"))],
        "the endpoint a `fork` binds, used inside the refused `dup`, names its binder"
    );
    let joined = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef joined(n : \
                  Nat) -> -F Nat {\n  run m <- case n -> -F Nat {\n    Zero => return n,\n    \
                  Succ(p) => pure p,\n  } ;\n  return m\n}\n";
    assert!(
        resolved(SourceText::from(joined), SourceText::from("case n"))
            .contains(&(String::from("n"), String::from("n"))),
        "the parameter the refused block's scrutinee names keeps its binder"
    );
}
