use super::*;

/// Entries agree exactly when they are equal.
///
/// # Specification
/// trivial.
fn agree<Entry>(
    ours: &Entry,
    theirs: &Entry,
) -> RowInclusion
where
    Entry: PartialEq,
{
    if ours == theirs {
        RowInclusion::Included
    }
    else {
        RowInclusion::Excluded
    }
}

#[test]
fn a_label_twice_is_refused_and_order_is_no_part_of_a_row()
{
    let forward = Row::<_, _, char>::from_entries([("a", 1_u32), ("b", 2_u32)]);
    let backward = Row::from_entries([("b", 2_u32), ("a", 1_u32)]);
    assert_eq!(
        forward, backward,
        "a row is its entries, in no order of their own"
    );
    assert_eq!(
        Err(LabelTwice("a")),
        Row::<_, _, char>::from_entries([("a", 1_u32), ("b", 2_u32), ("a", 1_u32)]),
        "a label written twice is refused, even at one entry"
    );
    assert_eq!(
        Ok(Row::EMPTY),
        Row::<&str, u32, char>::from_entries([]),
        "no entries make the allocation-free empty row"
    );
    let one = Row::<_, _, char>::singleton("a", 1_u32);
    assert_eq!(
        Err(RowsApart::Label("a")),
        one.union(&Row::singleton("a", 2_u32), &agree),
        "two rows defining one label apart do not join"
    );
    assert_eq!(
        Ok(one.clone()),
        one.union(&one, &agree),
        "an agreeing label joins once"
    );
}

#[test]
fn a_row_has_one_tail_and_inclusion_keeps_it()
{
    let console = Row::<_, _, char>::singleton("console", 1_u32);
    let div = Row::singleton("div", 2_u32);
    let open = console.with_tail(Some('r'));
    let other = div.with_tail(Some('s'));
    assert_eq!(
        Ok(Row::from_entries([("console", 1_u32), ("div", 2_u32)])
            .expect("apart")
            .with_tail(Some('r'))),
        open.union(&div, &agree),
        "a join keeps the one tail either row is open through"
    );
    assert_eq!(
        Ok(open.union(&div, &agree).expect("one tail")),
        open.union(&div.with_tail(Some('r')), &agree),
        "two rows on one tail join on it"
    );
    assert_eq!(
        Err(RowsApart::Tails('r', 's')),
        open.union(&other, &agree),
        "two different tails do not make one row"
    );
    assert_eq!(
        RowInclusion::Included,
        console.is_subset(&open, &agree),
        "a closed row is included in a row writing its labels, open or not"
    );
    assert_eq!(
        RowInclusion::Excluded,
        open.is_subset(&console, &agree),
        "an open row is not included in a closed one: its tail is unknown"
    );
    assert_eq!(
        RowInclusion::Excluded,
        open.is_subset(&console.with_tail(Some('s')), &agree),
        "nor in a row open through another tail"
    );
    assert_eq!(
        RowInclusion::Included,
        open.is_subset(&open.union(&div, &agree).expect("one tail"), &agree),
        "an open row is included in a wider row on its own tail"
    );
    assert_eq!(
        Row::EMPTY.with_tail(Some('r')),
        open.without(&"console"),
        "removing a label keeps the tail"
    );
    let both = open.union(&div, &agree).expect("one tail");
    assert_eq!(
        div.with_tail(Some('r')),
        both.difference(&console),
        "a difference keeps the labels the other row does not write, on this row's tail"
    );
    assert_eq!(
        div,
        Row::from_entries([("console", 1_u32), ("div", 2_u32)])
            .expect("apart")
            .difference(&open),
        "and never takes the other row's tail"
    );
}
