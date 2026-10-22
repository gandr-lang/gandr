//! Kept decisions answer as deciding does, wherever the block now stands.

use alloc::format;

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use super::*;
use crate::desc_cells::CellReport;
use crate::desc_cells::elaborate_desc_cells;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::unit::Unit;

/// Two rules rewriting `add(Zero, Zero)` apart: the block is refused at the
/// later rule, naming the earlier.
const APART: &str = r#"data NatApart : Type {
    Zero : NatApart;
    Succ : (n : NatApart) --> NatApart;
    oper add(m : NatApart, n : NatApart) -> NatApart;
    rule add(Zero, n) ==> n;
    rule add(m, Zero) ==> Succ(m);
    rule add(Succ(m), n) ==> Succ(add(m, n));
}"#;

/// A group's laws with the left inverse, which completion joins by deriving
/// rules into the block's store.
const GROUP: &str = r#"theory Group {
    sort G : Type;
    oper e : G;
    oper a : G;
    oper b : G;
    oper inv : (x : G) --> G;
    oper mul : (x : G, y : G) --> G;
    rule unitL : mul(e(), x) <=> x;
    rule assoc : mul(mul(x, y), z) <=> mul(x, mul(y, z));
    rule invL : mul(inv(x), x) <=> e();
}"#;

/// The cell report of `source`, its blocks decided through `decisions`.
///
/// # Specification
/// trivial.
fn elaborated<'source>(
    source: impl Into<SourceText<'source>>,
    decisions: &mut Decisions,
) -> CellReport
{
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    let described = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    elaborate_desc_cells(&described.declarations, decisions)
}

#[test]
fn a_block_an_edit_moves_is_answered_as_decided_where_it_stands_1547()
{
    for (block, refused) in [(APART, true), (GROUP, false)] {
        let mut decisions = Decisions::held();
        let first = elaborated(block, &mut decisions);
        let moved = format!("// An edit above the block.\n{block}");
        let kept = elaborated(moved.as_str(), &mut decisions);
        assert_eq!(
            decisions.kept.len(),
            1,
            "the moved block is found, not decided again"
        );
        assert_eq!(
            kept,
            elaborated(moved.as_str(), &mut Decisions::none()),
            "the kept answer, cells and spans are deciding's where the block stands"
        );
        assert_ne!(first, kept, "the block moved");
        assert_eq!(
            !kept.diagnostics.is_empty(),
            refused,
            "{:?}",
            kept.diagnostics
        );
    }
}

#[test]
fn a_block_whose_rule_changed_is_decided_again_1547()
{
    let mut decisions = Decisions::held();
    let apart = elaborated(APART, &mut decisions);
    assert!(!apart.diagnostics.is_empty(), "the written rules part");
    let changed = APART.replace("rule add(m, Zero) ==> Succ(m);", "rule add(m, Zero) ==> m;");
    let decided = elaborated(changed.as_str(), &mut decisions);
    assert_eq!(
        decisions.kept.len(),
        2,
        "the changed block is decided and kept beside the first"
    );
    assert_eq!(
        decided,
        elaborated(changed.as_str(), &mut Decisions::none())
    );
    assert!(
        decided.diagnostics.is_empty(),
        "the changed rules join: {:?}",
        decided.diagnostics
    );
}
