use super::*;

#[test]
fn a_label_twice_is_refused_and_order_is_no_part_of_a_row()
{
    let forward = Row::from_entries([("a", 1_u32), ("b", 2_u32)]);
    let backward = Row::from_entries([("b", 2_u32), ("a", 1_u32)]);
    assert_eq!(
        forward, backward,
        "a row is its entries, in no order of their own"
    );
    assert_eq!(
        Err(LabelTwice("a")),
        Row::from_entries([("a", 1_u32), ("b", 2_u32), ("a", 1_u32)]),
        "a label written twice is refused, even at one entry"
    );
    assert_eq!(
        Ok(Row::EMPTY),
        Row::<&str, u32>::from_entries([]),
        "no entries make the allocation-free empty row"
    );
    let agree = |ours: &u32, theirs: &u32| {
        if ours == theirs {
            RowInclusion::Included
        }
        else {
            RowInclusion::Excluded
        }
    };
    let one = Row::singleton("a", 1_u32);
    assert_eq!(
        Err(LabelTwice("a")),
        one.union(&Row::singleton("a", 2_u32), &agree),
        "two rows defining one label apart do not join"
    );
    assert_eq!(
        Ok(one.clone()),
        one.union(&one, &agree),
        "an agreeing label joins once"
    );
}
