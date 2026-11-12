//! The attribute carriers, filled by the production lowering route of
//! `gandr-surface-lowering`.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::parsed;
use gandr_surface_lowering_base::namespace::Recognition;
use gandr_surface_syntax::SourceText;

/// A use of a deprecated declaration carries the bytes of the use, the
/// declaration's name and the texts its attribute states; a use of an
/// unmarked declaration is no deprecated use.
#[test]
fn a_deprecated_use_carries_its_bytes_its_name_and_its_texts()
{
    let text = "@[deprecated(*{since = \"0.2\"})]\ndef square = 1;\ndef cube = 3;\ndef a = \
                square;\ndef b = cube;";
    let grammar = grammar();
    let tree = parsed(&grammar, SourceText::from(text));
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let uses: Vec<(&str, String, Option<String>, Option<String>)> = module
        .deprecated_uses(&arena)
        .into_iter()
        .map(|used| {
            (
                text.get(usize::from(used.span.start()) .. usize::from(used.span.end()))
                    .unwrap_or_default(),
                alloc::format!("{}", used.name),
                used.deprecation.since,
                used.deprecation.note,
            )
        })
        .collect();
    assert_eq!(
        uses,
        [(
            "square",
            String::from("square"),
            Some(String::from("0.2")),
            None
        )],
        "the one use of `square` carries what its attribute states"
    );
}
