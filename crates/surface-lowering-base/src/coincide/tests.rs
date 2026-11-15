//! The text a call to a block's normal form is written as. The cases that
//! lower a block and decide its rules are in this crate's integration target,
//! `tests::coincide`.

use super::CallText;

#[test]
fn a_call_lends_the_text_it_was_written_as()
{
    assert_eq!(
        CallText::from("add(Succ(Zero), Zero)").as_ref(),
        "add(Succ(Zero), Zero)"
    );
}
