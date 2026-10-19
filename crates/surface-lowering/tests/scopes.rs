//! The binders in scope at an offset: what a name written there would resolve
//! to, kept for a declaration the lowering refused.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;

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
    let grammar = built_in().expect("the built-in grammar builds");
    let parsed = parse(&grammar, source).expect("the source parses");
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        parsed.tree(),
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .expect("the module lowers");
    let at = text.find(<&str>::from(needle)).expect("the needle occurs");
    module
        .in_scope()
        .binders_at(ByteOffset::from(at))
        .filter_map(|site| text.get(usize::from(site.start()) .. usize::from(site.end())))
        .map(String::from)
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
