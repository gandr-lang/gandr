use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::outcome_of;
use crate::lower::native::tests::preluded;
use crate::lower::native::tests::refusal_of;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;
use crate::unit::Unit;

/// The span of the `n`-th `export` mark of `text`: the name of the mark.
///
/// # Specification
/// trivial.
fn mark(
    text: &str,
    n: usize,
) -> ByteSpan
{
    let start = text
        .match_indices("export")
        .nth(n)
        .map_or(0_usize, |(at, _)| at);
    ByteSpan::new(
        ByteOffset::from(start),
        ByteOffset::from(start.saturating_add("export".len())),
    )
    .expect("a mark's span")
}

/// An export of fixed-width integers lowers to its definition, and the export
/// table has each export in the order of its declaration, each with its
/// position as its key. A definition with no mark is no export.
#[test]
fn an_export_of_fixed_width_integers_lowers()
{
    let text = include_str!("tests/unformatted/an-export-of-fixed-width-integers-lowers.gandr");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &Unit::single(), &mut arena);
    for name in ["add", "hidden", "answer"] {
        let outcome = outcome_of(&module, SurfaceName::from(name));
        assert!(
            matches!(outcome, DeclarationOutcome::Completed { .. }),
            "`{name}` lowers to its definition: {outcome:?}"
        );
    }
    let exports = module.exports();
    let table: Vec<(&str, usize)> = exports
        .iter()
        .map(|export| (export.name.as_ref(), usize::from(export.key)))
        .collect();
    assert_eq!(
        table,
        [("add", 0_usize), ("answer", 1_usize)],
        "the table has each export in order, keyed by its position"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// Each export outside the fragment is refused by name at its mark: a
/// parameter that is no fixed-width integer, a definition that states no
/// type, a row that names an interface, and a row that a binder leaves open.
#[test]
fn each_export_outside_the_fragment_is_refused_by_name()
{
    let text =
        include_str!("tests/unformatted/each-export-outside-the-fragment-is-refused-by-name.gandr");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &Unit::single(), &mut arena);
    for (name, n, boundary) in [
        ("whole", 0_usize, FragmentBoundary::Export),
        ("unstated", 1_usize, FragmentBoundary::Export),
        ("partial", 2_usize, FragmentBoundary::ExportRow),
        ("open", 3_usize, FragmentBoundary::ExportRow),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::OutOfFragment {
                span: mark(text, n),
                form: FormName::ATTRIBUTE,
                sort: FragmentSort::Declaration,
                boundary,
            },
            "`{name}` is refused by its boundary"
        );
    }
    assert!(module.exports().is_empty(), "a refused export has no key");
}
