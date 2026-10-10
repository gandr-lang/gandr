//! The three build-time gates: Operator Form, Unique Tiles and Assumption 3
//! (Moon, Blinn, Porter and Omar 2025, § 3).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::GrammarFingerprint;

use crate::model::PbgError;
use crate::model::RegexShape;
use crate::model::RegexView;
use crate::model::Rule;
use crate::model::RuleName;
use crate::model::Sort;
use crate::model::Sym;
use crate::mold::MoldTable;

/// A subtree's emptiness and the sorts of the holes it can begin and end
/// with.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Summary
{
    /// Whether the subtree derives the empty sequence.
    nullable: bool,
    /// The sorts of the holes that can come first.
    first: BTreeSet<Sort>,
    /// The sorts of the holes that can come last.
    last: BTreeSet<Sort>,
}

/// Checks one rule's form against Operator Form: no concatenation puts two
/// holes side by side.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when no path through the form, empty branches,
///   optionals and repetitions included, puts a hole directly after a hole.
/// - fails: the first exposure in left-to-right, innermost-first order.
/// - panics: none.
///
/// # Errors
/// [`PbgError::AdjacentSorts`] naming the rule and both sorts.
///
/// # Adequacy
/// - hypothesis: For direct adjacency, nullable bridges and mandatory tile
///   separators, L3 exact refusal and acceptance observations catch lost
///   FIRST/LAST exposure and misattributed errors; repetition-backedge
///   adjacency is outside these witnesses.
/// - witness: `tests::pbg::pbg_rejects_direct_adjacent_sorts_in_sequence`
/// - witness: `tests::pbg::pbg_rejects_adjacency_exposed_by_nullable_sequence_paths`
/// - witness: `tests::pbg::pbg_accepts_terminal_separators_between_sort_uses`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| matches!(error, PbgError::AdjacentSorts { rule: name, .. } if *name == rule.name)))]
#[inline]
pub fn validate_operator_form(rule: &Rule) -> Result<(), PbgError>
{
    summarize(rule.name(), rule.regex().view()).map(|_summary| ())
}

/// Checks a rule set against Unique Tiles: no two tile occurrences share a
/// label and a context.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when every tile occurrence interns to a distinct
///   label and context; occurrences at distinct positions never collide.
/// - fails: the first redundant occurrence, rules in input order and each form
///   left to right.
/// - panics: none.
///
/// # Errors
/// [`PbgError::DuplicateTile`] naming both rules, or
/// [`PbgError::MoldOverflow`].
///
/// # Adequacy
/// - hypothesis: For identical branches and same-label occurrences at distinct
///   positions, L3 identity observations catch accidental context collisions
///   and missed duplicate tiles; capacity exhaustion and arbitrary canonical
///   expressions are outside the witnesses.
/// - witness: `tests::pbg::pbg_rejects_duplicate_rctx_tile`
/// - witness: `tests::pbg::pbg_accepts_same_label_at_distinct_contexts`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| match *error {
    PbgError::DuplicateTile { sort, prec, first_rule, second_rule, .. } => rules.iter().any(|rule| rule.name == first_rule) && rules.iter().any(|rule| rule.name == second_rule && rule.sort == sort && rule.prec == prec),
    PbgError::MoldOverflow => true,
    _ => false,
}))]
#[inline]
pub fn validate_unique_tiles(rules: &[Rule]) -> Result<(), PbgError>
{
    MoldTable::build(rules, GrammarFingerprint::from(0_u64)).map(|_table| ())
}

/// Checks a rule set against Assumption 3: no two distinct sorts `r` and `s`
/// with `s ∈ FIRST(G(r, p))` and `r ∈ LAST(G(s, q))` for any precedences `p`
/// and `q`.
///
/// # Specification
/// - requires: every rule passed Operator Form.
/// - ensures: `Ok` exactly when no such pair exists.
/// - fails: the first conflicting pair, by sort order.
/// - panics: none.
/// - intension: FIRST and LAST are aggregated per producing sort over every
///   precedence before pairs are compared.
///
/// # Errors
/// [`PbgError::Assumption3Conflict`] naming the pair, or
/// [`PbgError::AdjacentSorts`] for a rule that skipped Operator Form.
///
/// # Adequacy
/// - hypothesis: For two legal forms with opposing boundary sorts and the
///   nearest non-conflicting forms, L3 exact pair and acceptance observations
///   catch ignored cross-sort edges; arbitrary rule sets and all sort-order
///   ties are not enumerated.
/// - witness: `tests::pbg::assumption_3_contract`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| match *error {
    PbgError::Assumption3Conflict { first_sort, second_sort } => first_sort != second_sort && rules.iter().any(|rule| rule.sort == first_sort) && rules.iter().any(|rule| rule.sort == second_sort),
    PbgError::AdjacentSorts { rule: name, .. } => rules.iter().any(|rule| rule.name == name),
    _ => false,
}))]
#[inline]
pub fn validate_assumption_3(rules: &[Rule]) -> Result<(), PbgError>
{
    let mut first_sorts: BTreeMap<Sort, BTreeSet<Sort>> = BTreeMap::new();
    let mut last_sorts: BTreeMap<Sort, BTreeSet<Sort>> = BTreeMap::new();
    for rule in rules {
        let summary = summarize(rule.name(), rule.regex().view())?;
        first_sorts
            .entry(rule.sort())
            .or_default()
            .extend(summary.first);
        last_sorts
            .entry(rule.sort())
            .or_default()
            .extend(summary.last);
    }
    for (&first_sort, begins) in &first_sorts {
        for &second_sort in begins {
            if second_sort != first_sort
                && last_sorts
                    .get(&second_sort)
                    .is_some_and(|ends| ends.contains(&first_sort))
            {
                return Err(PbgError::Assumption3Conflict {
                    first_sort,
                    second_sort,
                });
            }
        }
    }
    Ok(())
}

/// One pending step of [`summarize`].
#[derive(Clone, Copy)]
enum Frame<'regex>
{
    /// Visit a subtree.
    Enter(RegexView<'regex>),
    /// Fold the last `count` summaries as a sequence.
    FinishSeq(usize),
    /// Fold the last `count` summaries as an alternation.
    FinishAlt(usize),
    /// Make the last summary nullable.
    FinishNullable,
}

/// Summarizes a form, refusing the first place it puts two holes side by
/// side.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success, the form's emptiness and the sorts of its first and
///   last holes.
/// - fails: a concatenation whose prefix can end with a hole while the next
///   item can begin with one.
/// - panics: none.
/// - intension: an explicit frame stack, so nesting depth costs heap rather
///   than call stack; children finish left to right before their parent.
///
/// # Errors
/// [`PbgError::AdjacentSorts`] for the first exposure.
///
/// # Adequacy
/// - hypothesis: For direct adjacency and nullable bridges, L3 exposed-boundary
///   observations catch lost nullability and first/last sorts; the predicate
///   protects refusal provenance, not every accepted summary or repetition
///   backedge.
/// - witness: `tests::pbg::pbg_rejects_direct_adjacent_sorts_in_sequence`
/// - witness: `tests::pbg::pbg_rejects_adjacency_exposed_by_nullable_sequence_paths`
/// - witness: `tests::pbg::pbg_accepts_terminal_separators_between_sort_uses`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| matches!(error, PbgError::AdjacentSorts { rule: name, .. } if *name == rule.0)))]
fn summarize(
    rule: RuleName,
    regex: RegexView<'_>,
) -> Result<Summary, PbgError>
{
    let mut frames = vec![Frame::Enter(regex)];
    let mut summaries: Vec<Summary> = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            | Frame::Enter(node) => match node.shape() {
                | RegexShape::Empty => summaries.push(Summary {
                    nullable: true,
                    ..Summary::default()
                }),
                | RegexShape::Sym(Sym::Tile(_tile)) => summaries.push(Summary::default()),
                | RegexShape::Sym(Sym::Sort(sort)) => summaries.push(Summary {
                    nullable: false,
                    first: BTreeSet::from([sort]),
                    last: BTreeSet::from([sort]),
                }),
                | RegexShape::Seq(items) => {
                    frames.push(Frame::FinishSeq(items.len()));
                    frames.extend(items.into_iter().rev().map(Frame::Enter));
                },
                | RegexShape::Alt(items) => {
                    frames.push(Frame::FinishAlt(items.len()));
                    frames.extend(items.into_iter().rev().map(Frame::Enter));
                },
                | RegexShape::Optional(inner) | RegexShape::Repeat(inner) => {
                    frames.push(Frame::FinishNullable);
                    frames.push(Frame::Enter(inner));
                },
            },
            | Frame::FinishSeq(count) => {
                let start = summaries.len().saturating_sub(count);
                let children = summaries.split_off(start);
                let mut acc = Summary {
                    nullable: true,
                    ..Summary::default()
                };
                for current in children {
                    reject_adjacent(rule, &acc.last, &current.first)?;
                    acc = seq_summary(&acc, &current);
                }
                summaries.push(acc);
            },
            | Frame::FinishAlt(count) => {
                let start = summaries.len().saturating_sub(count);
                let children = summaries.split_off(start);
                let mut acc = Summary::default();
                for current in children {
                    acc.nullable = acc.nullable || current.nullable;
                    acc.first.extend(current.first);
                    acc.last.extend(current.last);
                }
                summaries.push(acc);
            },
            | Frame::FinishNullable => {
                if let Some(summary) = summaries.last_mut() {
                    summary.nullable = true;
                }
            },
        }
    }
    Ok(summaries.pop().unwrap_or_default())
}

/// Refuses a prefix that can end with a hole followed by an item that can
/// begin with one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when `left` or `right` is empty.
/// - fails: both non-empty; the error names the smallest sort of each.
/// - panics: none.
///
/// # Errors
/// [`PbgError::AdjacentSorts`].
///
/// # Adequacy
/// - hypothesis: For empty boundary sets and two multi-sort sets, L3
///   exact-result observations catch inverted acceptance and non-minimal error
///   witnesses; the closed sort domain is sampled rather than every subset pair
///   enumerated.
/// - witness: `check::tests::adjacency_refusal_uses_smallest_boundary_sorts`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::AdjacentSorts { rule: name, left: a, right: b } if *name == rule.0 && left.first() == Some(a) && right.first() == Some(b)), |&()| left.is_empty() || right.is_empty()))]
fn reject_adjacent(
    rule: RuleName,
    left: &BTreeSet<Sort>,
    right: &BTreeSet<Sort>,
) -> Result<(), PbgError>
{
    match (left.first(), right.first()) {
        | (Some(&left_sort), Some(&right_sort)) => Err(PbgError::AdjacentSorts {
            rule: rule.0,
            left: left_sort,
            right: right_sort,
        }),
        | _ => Ok(()),
    }
}

/// The summary of `left` followed by `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the standard FIRST/LAST/nullable composition of a concatenation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For distinct boundary sorts under all four nullability pairs,
///   L2 finite truth-table observations catch swapped FIRST/LAST propagation
///   and incorrect conjunction; larger sets are not exhausted, while the
///   predicate checks their full unions without allocation.
/// - witness: `check::tests::sequence_summary_obeys_all_nullability_pairs`
#[spec(ensures: |ret| ret.nullable == (left.nullable && right.nullable) && (if left.nullable { ret.first.iter().eq(left.first.union(&right.first)) } else { ret.first == left.first }) && (if right.nullable { ret.last.iter().eq(left.last.union(&right.last)) } else { ret.last == right.last }))]
fn seq_summary(
    left: &Summary,
    right: &Summary,
) -> Summary
{
    let mut first = left.first.clone();
    if left.nullable {
        first.extend(right.first.iter().copied());
    }
    let mut last = right.last.clone();
    if right.nullable {
        last.extend(left.last.iter().copied());
    }
    Summary {
        nullable: left.nullable && right.nullable,
        first,
        last,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;

    use super::PbgError;
    use super::RuleName;
    use super::Sort;
    use super::Summary;
    use super::reject_adjacent;
    use super::seq_summary;

    #[test]
    fn adjacency_refusal_uses_smallest_boundary_sorts()
    {
        let empty = BTreeSet::new();
        let left = BTreeSet::from([Sort::Type, Sort::Item, Sort::Expression]);
        let right = BTreeSet::from([Sort::Type, Sort::Pattern]);
        for (a, b) in [(&empty, &empty), (&empty, &right), (&left, &empty)] {
            assert_eq!(Ok(()), reject_adjacent(RuleName("boundary"), a, b));
        }
        assert_eq!(
            Err(PbgError::AdjacentSorts {
                rule: "boundary",
                left: Sort::Item,
                right: Sort::Pattern
            }),
            reject_adjacent(RuleName("boundary"), &left, &right)
        );
    }

    #[test]
    fn sequence_summary_obeys_all_nullability_pairs()
    {
        for (left_nullable, right_nullable, first, last, nullable) in [
            (
                false,
                false,
                BTreeSet::from([Sort::Item]),
                BTreeSet::from([Sort::Type]),
                false,
            ),
            (
                false,
                true,
                BTreeSet::from([Sort::Item]),
                BTreeSet::from([Sort::Pattern, Sort::Type]),
                false,
            ),
            (
                true,
                false,
                BTreeSet::from([Sort::Item, Sort::Expression]),
                BTreeSet::from([Sort::Type]),
                false,
            ),
            (
                true,
                true,
                BTreeSet::from([Sort::Item, Sort::Expression]),
                BTreeSet::from([Sort::Pattern, Sort::Type]),
                true,
            ),
        ] {
            let left = Summary {
                nullable: left_nullable,
                first: BTreeSet::from([Sort::Item]),
                last: BTreeSet::from([Sort::Pattern]),
            };
            let right = Summary {
                nullable: right_nullable,
                first: BTreeSet::from([Sort::Expression]),
                last: BTreeSet::from([Sort::Type]),
            };
            assert_eq!(
                Summary {
                    nullable,
                    first,
                    last
                },
                seq_summary(&left, &right)
            );
        }
    }
}
