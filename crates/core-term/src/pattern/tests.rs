use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::Side;

use super::BranchStatus;
use super::Pattern;
use super::PatternId;
use super::Patterns;
use crate::hole::HoleId;

#[test]
fn a_conjunction_refutes_first_and_doubts_second()
{
    use BranchStatus::Possibly;
    use BranchStatus::Refuted;
    use BranchStatus::Satisfied;
    let table = [
        (Satisfied, Satisfied, Satisfied),
        (Satisfied, Possibly, Possibly),
        (Satisfied, Refuted, Refuted),
        (Possibly, Satisfied, Possibly),
        (Possibly, Possibly, Possibly),
        (Possibly, Refuted, Refuted),
        (Refuted, Satisfied, Refuted),
        (Refuted, Possibly, Refuted),
        (Refuted, Refuted, Refuted),
    ];
    for (left, right, expected) in table {
        assert_eq!(left.and(right), expected, "{left:?} and {right:?}");
    }
}

#[test]
fn a_pattern_names_its_parts_in_order()
{
    let mut patterns = Patterns::new();
    let first = patterns.mint(Pattern::Binder);
    let second = patterns.mint(Pattern::Hole(HoleId::from(3_u32)));
    assert_ne!(first, second, "two mints are two patterns");
    let pair = patterns.mint(Pattern::Pair(first, second));
    let injected = patterns.mint(Pattern::Injection(Side::Right, pair));
    let constructed = patterns.mint(Pattern::Constructor {
        tag: ConstructorTag::from(1_usize),
        fields: vec![second, first],
    });
    let read = |id: PatternId| patterns.pattern(id).expect("minted").parts();
    assert_eq!(read(pair), vec![first, second]);
    assert_eq!(read(injected), vec![pair]);
    assert_eq!(
        read(constructed),
        vec![second, first],
        "fields keep their order"
    );
    assert_eq!(read(second), Vec::<PatternId>::new(), "a hole has no parts");
    assert_eq!(
        patterns.pattern(second),
        Some(&Pattern::Hole(HoleId::from(3_u32))),
        "an id reads back what was minted under it"
    );
    assert_eq!(
        Patterns::new().pattern(first),
        None,
        "an empty table resolves nothing"
    );
}

#[test]
fn a_table_names_its_holes()
{
    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let later = patterns.mint(Pattern::Hole(HoleId::from(9_u32)));
    let earlier = patterns.mint(Pattern::Hole(HoleId::from(2_u32)));
    patterns.mint(Pattern::Constructor {
        tag: ConstructorTag::from(0_usize),
        fields: vec![earlier, wildcard, later],
    });
    assert_eq!(
        patterns.holes(),
        vec![HoleId::from(9_u32), HoleId::from(2_u32)],
        "the holes in mint order, not by id, and nothing else"
    );
    assert_eq!(Patterns::new().holes(), Vec::<HoleId>::new());
}
