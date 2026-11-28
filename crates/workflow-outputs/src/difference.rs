//! The difference of the values of one kind between two trees.

use alloc::collections::BTreeMap;

use anodized::spec;

use crate::tree::Source;

/// How the value of one source differs between the base and the head.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Change
{
    /// The head has the source, and the base does not.
    Added
    {
        /// The name of the source.
        name: String,
        /// The value of the head.
        head: Vec<u8>,
    },
    /// The base has the source, and the head does not.
    Removed
    {
        /// The name of the source.
        name: String,
        /// The value of the base.
        base: Vec<u8>,
    },
    /// Both have the source, with two values.
    Changed
    {
        /// The name of the source.
        name: String,
        /// The value of the base.
        base: Vec<u8>,
        /// The value of the head.
        head: Vec<u8>,
    },
}

/// What the line of a change shows for a value that has no line at the place
/// of the difference.
const ABSENT: &str = "no line";

/// A whole value on one line: a value of one line as it is, and a value of
/// more lines as their count and the first of them.
///
/// # Specification
/// trivial.
fn whole(value: &[u8]) -> String
{
    let text = String::from_utf8_lossy(value);
    let mut lines = text.lines();
    let first = lines.next().unwrap_or_default().trim_end();
    match lines.count() {
        0 => first.to_owned(),
        more => format!("{} lines, the first: {first}", more.saturating_add(1)),
    }
}

/// The first line at which two values differ: its number from 1, then the
/// line of the base and the line of the head. A value that ends before that
/// line gives [`ABSENT`].
///
/// # Specification
/// trivial.
fn first_difference<'text>(
    base: &'text str,
    head: &'text str,
) -> (usize, &'text str, &'text str)
{
    let mut left = base.lines();
    let mut right = head.lines();
    let mut number = 1_usize;
    loop {
        match (left.next(), right.next()) {
            (Some(was), Some(is)) if was == is => number = number.saturating_add(1),
            (was, is) => return (number, was.unwrap_or(ABSENT), is.unwrap_or(ABSENT)),
        }
    }
}

impl Change
{
    /// The change as one line: the name, then `added`, `removed`, or the
    /// value of the base and the value of the head, each without its newline.
    ///
    /// A value of more lines does not go on the line whole. An added or a
    /// removed value gives the count of its lines and the first of them. A
    /// changed value gives the first line that differs, with its number.
    ///
    /// # Specification
    /// - ensures: the line has no newline.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an added, a removed and a changed source give three
    ///   lines that name them, and a value of more lines gives one line of it.
    /// - witness: `difference::tests::two_trees_differ_by_source`
    /// - witness: `difference::tests::a_value_of_more_lines_shows_one_line`
    #[spec(ensures: |ret| !ret.contains('\n'))]
    #[inline]
    #[must_use]
    pub fn line(&self) -> String
    {
        match *self {
            Self::Added { ref name, ref head } => format!("{name}: added: {}", whole(head)),
            Self::Removed { ref name, ref base } => format!("{name}: removed: {}", whole(base)),
            Self::Changed {
                ref name,
                ref base,
                ref head,
            } => {
                let before = String::from_utf8_lossy(base);
                let after = String::from_utf8_lossy(head);
                if before.lines().nth(1).is_none() && after.lines().nth(1).is_none() {
                    format!("{name}: {} → {}", before.trim_end(), after.trim_end())
                }
                else {
                    let (number, was, is) = first_difference(&before, &after);
                    format!(
                        "{name}: line {number}: {} → {}",
                        was.trim_end(),
                        is.trim_end()
                    )
                }
            },
        }
    }
}

/// The changes from the values `base` to the values `head`, each in name
/// order, in name order.
///
/// # Specification
/// - requires: each list is in name order, each name one time.
/// - ensures: the changes are in name order, and a source with one value in
///   both trees gives no change.
///
/// # Adequacy
/// - hypothesis: L3 — an added, a removed, a changed and an equal source give
///   three changes.
/// - witness: `difference::tests::two_trees_differ_by_source`
#[spec(ensures: |ret| ret.len() <= base.len().saturating_add(head.len()))]
#[inline]
#[must_use]
pub fn changes(
    base: &[(Source, Vec<u8>)],
    head: &[(Source, Vec<u8>)],
) -> Vec<Change>
{
    let mut changes = Vec::new();
    let mut left = base.iter().peekable();
    let mut right = head.iter().peekable();
    loop {
        match (left.peek(), right.peek()) {
            (None, None) => break,
            (Some(&&(ref source, ref value)), None) => {
                changes.push(Change::Removed {
                    name: source.name.clone(),
                    base: value.clone(),
                });
                let _next = left.next();
            },
            (None, Some(&&(ref source, ref value))) => {
                changes.push(Change::Added {
                    name: source.name.clone(),
                    head: value.clone(),
                });
                let _next = right.next();
            },
            (Some(&&(ref was, ref before)), Some(&&(ref is, ref after))) => {
                match was.name.cmp(&is.name) {
                    core::cmp::Ordering::Less => {
                        changes.push(Change::Removed {
                            name: was.name.clone(),
                            base: before.clone(),
                        });
                        let _next = left.next();
                    },
                    core::cmp::Ordering::Greater => {
                        changes.push(Change::Added {
                            name: is.name.clone(),
                            head: after.clone(),
                        });
                        let _next = right.next();
                    },
                    core::cmp::Ordering::Equal => {
                        if before != after {
                            changes.push(Change::Changed {
                                name: is.name.clone(),
                                base: before.clone(),
                                head: after.clone(),
                            });
                        }
                        let _next = left.next();
                        let _next = right.next();
                    },
                }
            },
        }
    }
    changes
}

/// The members of the values `head` that the values `base` do not have, each
/// as `<name>: <member>`, in name order.
///
/// A member is one line of a value. The name of its source is not a part of
/// it, so a member that moves to another source is no change. Two equal
/// members are two members: the head adds one when it has more of them than
/// the base has.
///
/// # Specification
/// - ensures: a member of each line is counted against the members of all the
///   values of the base; a member that the base has as often is not in the
///   result.
///
/// # Adequacy
/// - hypothesis: L3 — a moved member, a removed member, a member that the head
///   has twice and the base once, and a new member give two added members.
/// - witness: `difference::tests::a_ratchet_refuses_only_the_members_that_the_head_adds`
#[spec(ensures: |ret| ret.len() <= head.iter().map(|value| value.1.split(|&byte| byte == b'\n').count()).sum())]
#[inline]
#[must_use]
pub fn added(
    base: &[(Source, Vec<u8>)],
    head: &[(Source, Vec<u8>)],
) -> Vec<String>
{
    let mut held: BTreeMap<&[u8], usize> = BTreeMap::new();
    for &(_, ref value) in base {
        for member in members(value) {
            let count = held.entry(member).or_default();
            *count = count.saturating_add(1);
        }
    }
    let mut added = Vec::new();
    for &(ref source, ref value) in head {
        for member in members(value) {
            match held.get_mut(member) {
                Some(count) if *count > 0 => *count = count.saturating_sub(1),
                _ => added.push(format!(
                    "{}: {}",
                    source.name,
                    String::from_utf8_lossy(member)
                )),
            }
        }
    }
    added
}

/// The members of `value`: its lines that hold a byte, with no line break.
///
/// # Specification
/// trivial.
fn members(value: &[u8]) -> impl Iterator<Item = &[u8]>
{
    value
        .split(|&byte| byte == b'\n')
        .filter(|line| !line.is_empty())
}

#[cfg(test)]
mod tests
{
    use super::Change;
    use super::added;
    use super::changes;
    use crate::tree::Source;

    /// A value of a source named `name`.
    fn value(
        name: &str,
        text: &str,
    ) -> (Source, Vec<u8>)
    {
        (
            Source {
                name: name.to_owned(),
                object: String::new(),
            },
            text.as_bytes().to_vec(),
        )
    }

    /// An added, a removed, a changed and an equal source give three changes
    /// in name order, each on one line.
    #[test]
    fn two_trees_differ_by_source()
    {
        let base = [
            value("fixture/a.gandr", "W\t0\n"),
            value("fixture/b.gandr", "W\t1\n"),
            value("strict/c.gandr", "W\t2\n"),
        ];
        let head = [
            value("fixture/b.gandr", "W\t1\n"),
            value("strict/c.gandr", "W\t3\n"),
            value("strict/d.gandr", "W\t4\n"),
        ];
        let found = changes(&base, &head);
        let lines: Vec<String> = found.iter().map(Change::line).collect();
        assert_eq!(lines, [
            "fixture/a.gandr: removed: W\t0",
            "strict/c.gandr: W\t2 → W\t3",
            "strict/d.gandr: added: W\t4",
        ]);
    }

    /// A value of more lines gives one line of it: the first line that
    /// differs with its number, or the count of the lines and the first.
    #[test]
    fn a_value_of_more_lines_shows_one_line()
    {
        let base = [
            value("fixture/a.gandr", "0..1 Other \"a\"\n1..2 Other \";\"\n"),
            value("fixture/c.gandr", "0..1 Other \"c\"\n1..2 Other \";\"\n"),
        ];
        let head = [
            value("fixture/a.gandr", "0..1 Other \"a\"\n1..2 Keyword \";\"\n"),
            value("fixture/b.gandr", "0..1 Other \"b\"\n1..2 Other \";\"\n"),
            value("fixture/c.gandr", "0..1 Other \"c\"\n"),
        ];
        let found = changes(&base, &head);
        let lines: Vec<String> = found.iter().map(Change::line).collect();
        assert_eq!(lines, [
            "fixture/a.gandr: line 2: 1..2 Other \";\" → 1..2 Keyword \";\"",
            "fixture/b.gandr: added: 2 lines, the first: 0..1 Other \"b\"",
            "fixture/c.gandr: line 2: 1..2 Other \";\" → no line",
        ]);
    }

    /// A ratchet refuses only the members that the head adds: a member that
    /// moves to another source, and a member that the head removes, are not
    /// refused; a member that the head has twice and the base once is.
    #[test]
    fn a_ratchet_refuses_only_the_members_that_the_head_adds()
    {
        let base = [
            value(
                "fixture/a.gandr",
                "moved:1 uncommented\nkept:2 uncommented\n",
            ),
            value(
                "fixture/b.gandr",
                "gone:3 uncommented\ntwice:4 uncommented\n",
            ),
        ];
        let head = [
            value("fixture/a.gandr", "kept:2 uncommented\n"),
            value(
                "fixture/b.gandr",
                "twice:4 uncommented\ntwice:4 uncommented\n",
            ),
            value(
                "fixture/c.gandr",
                "moved:1 uncommented\nnew:5 uncommented\n",
            ),
        ];
        assert_eq!(added(&base, &head), [
            "fixture/b.gandr: twice:4 uncommented",
            "fixture/c.gandr: new:5 uncommented",
        ]);
    }
}
