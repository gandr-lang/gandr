//! The text a call to a block's normal form is written as, and the term it
//! reads as over the block's own description. The cases that lower a block
//! and decide its rules are in this crate's integration target,
//! `tests::coincide`.

use alloc::string::String;

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_computads::ElaborateError;

use super::CallText;
use super::Decisions;
use super::NormalFormFault;
use super::normal_form;
use crate::desc_cells::elaborate_desc_cells;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::unit::Unit;

/// The spelling of the normal form each call reaches under the one block
/// `source` describes, or why the call reads no normal form.
///
/// # Specification
/// trivial.
fn reached<const N: usize>(
    source: &str,
    calls: [&str; N],
) -> [Result<String, NormalFormFault>; N]
{
    let grammar = grammar();
    let tree = parse(&grammar, SourceText::from(source))
        .unwrap()
        .into_tree();
    let described = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    let cells = elaborate_desc_cells(&described.declarations, &mut Decisions::none());
    let (&[ref block], &[ref cells]) = (
        described.declarations.as_slice(),
        cells.declarations.as_slice(),
    )
    else {
        panic!("one described block")
    };
    calls.map(|call| {
        normal_form(&block.description, cells, CallText::from(call)).map(|normal| normal.spelling())
    })
}

#[test]
fn a_call_lends_the_text_it_was_written_as()
{
    assert_eq!(
        CallText::from("add(Succ(Zero), Zero)").as_ref(),
        "add(Succ(Zero), Zero)"
    );
}

/// A nested call of many arguments reads as the term it spells, space
/// between its tokens read past; a call that is no whole term, names no
/// declared symbol or applies a constructor is refused for its own reason;
/// an atom a restriction abstracts is its occurrence inside the abstraction
/// and unknown beside it.
#[test]
fn a_call_reads_as_the_term_it_spells_or_says_why_not()
{
    let normal = |spelling: &str| Ok(String::from(spelling));
    assert_eq!(
        reached(
            include_str!("tests/unformatted/a-call-reads-its-normal-form-or-says-why-not.gandr"),
            [
                "divmod(Succ(Succ(Succ(Succ(Succ(Zero))))), Succ(Succ(Zero)))",
                " divmod ( Zero , Zero ) ",
                "divmod(Zero",
                "divmod(Zero, Zero) Zero",
                "divmod(Zero,)",
                "plus(Zero, Zero)",
                "Succ(Zero)",
            ],
        ),
        [
            normal("(Succ(Succ(Zero)), Succ(Zero))"),
            normal("(Zero, Zero)"),
            Err(NormalFormFault::Unread),
            Err(NormalFormFault::Unread),
            Err(NormalFormFault::Unread),
            Err(NormalFormFault::UnknownSymbol),
            Err(NormalFormFault::NotACall(ElaborateError::LhsNotOperation)),
        ]
    );
    assert_eq!(
        reached(
            include_str!(
                "tests/unformatted/a-call-reads-its-normal-form-or-says-why-not-restriction.gandr"
            ),
            [
                "nu(bind b . out(b, nil))",
                "nu(bind a . nu(bind b . out(a, nil)))",
                "nu(bind b . out(c, nil))",
                "out(b, nu(bind b . nil))",
                "nu(bind b . out(b, nil)",
            ],
        ),
        [
            normal("nil"),
            normal("nu(bind a0 . nu(bind a1 . out(a0, nil)))"),
            Err(NormalFormFault::UnknownSymbol),
            Err(NormalFormFault::UnknownSymbol),
            Err(NormalFormFault::Unread),
        ]
    );
}
