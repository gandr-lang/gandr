use gandr_core_term::CoreArena;
use gandr_kernel_term::BaseType;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::Arguments;
use super::entry_shape;
use crate::error::LoweringRefusal;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;

/// An entry returns the exit code, `U (F Integer)`, or returns it after the
/// argument list, `U (List(String) → F Integer)`; a returner of a string, a
/// function of an integer and an integer are no entry's type (#1881).
#[test]
fn an_entry_returns_an_integer_after_its_arguments_1881()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let strings = arena.value_type_list(string);
    let code = arena.comp_type_returner(integer);
    let reads = arena.comp_type_arrow(strings, code);
    let reads_dependent = arena.comp_type_pi(strings, code);
    let text = arena.comp_type_returner(string);
    let of_integer = arena.comp_type_arrow(integer, code);
    let shapes = [
        (
            arena.value_type_thunk(code),
            Maybe::Present(Arguments::Unread),
        ),
        (
            arena.value_type_thunk(reads),
            Maybe::Present(Arguments::Read),
        ),
        (
            arena.value_type_thunk(reads_dependent),
            Maybe::Present(Arguments::Read),
        ),
        (
            arena.value_type_thunk(text),
            Maybe::Absent(super::entry_shape::Absent::Misshapen),
        ),
        (
            arena.value_type_thunk(of_integer),
            Maybe::Absent(super::entry_shape::Absent::Misshapen),
        ),
        (
            integer,
            Maybe::Absent(super::entry_shape::Absent::Misshapen),
        ),
    ];
    for (declared, wanted) in shapes {
        assert_eq!(
            entry_shape(&arena, declared),
            wanted,
            "{:?}",
            arena.value_type(declared)
        );
    }
}

/// A `main` of either entry type is lowered as written; one returning a
/// string, one taking an integer and one with no signature are refused by
/// name at their names; a module's member named `main` is no entry (#1881).
#[test]
fn a_main_of_another_type_is_refused_by_name_1881()
{
    for source in [
        "def main() -> -F Integer { return 0 }\n",
        "def main(args : List(String)) -> -F Integer { return 0 }\n",
        "module Tool { def main() -> -F String { return \"x\" } }\n",
    ] {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        assert!(
            module.declarations().iter().all(|declaration| matches!(
                declaration.outcome(),
                DeclarationOutcome::Completed { .. }
            )),
            "{source}"
        );
    }
    for (source, name) in [
        (
            "def main() -> -F String { return \"x\" }\n",
            4_usize .. 8_usize,
        ),
        (
            "def main(n : Integer) -> -F Integer { return n }\n",
            4_usize .. 8_usize,
        ),
        ("def main = 0 ;\n", 4_usize .. 8_usize),
    ] {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        let LoweringRefusal::EntryType { span } = refusal_of(&module, SurfaceName::from("main"))
        else {
            panic!("`main` is refused as an entry: {source}");
        };
        assert_eq!(
            (usize::from(span.start()), usize::from(span.end())),
            (name.start, name.end),
            "the refusal marks the name: {source}"
        );
    }
}
