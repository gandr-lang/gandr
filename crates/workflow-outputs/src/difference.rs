//! The difference of the values of one kind between two trees.

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

impl Change
{
    /// The change as one line: the name, then `added`, `removed`, or the
    /// value of the base and the value of the head, each without its newline.
    ///
    /// # Specification
    /// - ensures: the line has no newline.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an added, a removed and a changed source give three
    ///   lines that name them.
    /// - witness: `difference::tests::two_trees_differ_by_source`
    #[spec(ensures: |ret| !ret.contains('\n'))]
    #[inline]
    #[must_use]
    pub fn line(&self) -> String
    {
        let shown = |value: &[u8]| String::from_utf8_lossy(value).trim_end().replace('\n', "⏎");
        match *self {
            Self::Added { ref name, ref head } => format!("{name}: added: {}", shown(head)),
            Self::Removed { ref name, ref base } => format!("{name}: removed: {}", shown(base)),
            Self::Changed {
                ref name,
                ref base,
                ref head,
            } => format!("{name}: {} → {}", shown(base), shown(head)),
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

#[cfg(test)]
mod tests
{
    use super::Change;
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
}
