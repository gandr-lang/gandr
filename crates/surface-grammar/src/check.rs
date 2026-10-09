//! The three build-time gates: Operator Form, Unique Tiles and Assumption 3
//! (Moon, Blinn, Porter and Omar 2025, § 3).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

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
/// - hypothesis: L3 pointwise — direct adjacency, adjacency exposed through a
///   nullable bridge, and a tile separator between two holes.
/// - witness: `tests::pbg::pbg_rejects_direct_adjacent_sorts_in_sequence`
/// - witness: `tests::pbg::pbg_rejects_adjacency_exposed_by_nullable_sequence_paths`
/// - witness: `tests::pbg::pbg_accepts_terminal_separators_between_sort_uses`
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
/// - hypothesis: L3 pointwise — identical alternation branches collide, the
///   same label at distinct positions does not.
/// - witness: `tests::pbg::pbg_rejects_duplicate_rctx_tile`
/// - witness: `tests::pbg::pbg_accepts_same_label_at_distinct_contexts`
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
/// - hypothesis: L3 pointwise — a form beginning with one sort paired with a
///   form ending with the other is refused, and the built-in surface passes.
/// - witness: `tests::pbg::assumption_3_contract`
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
