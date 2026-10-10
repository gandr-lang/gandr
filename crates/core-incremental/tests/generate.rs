//! Generated programs and edits for the differential.
//!
//! A program holds one to six statements named from `d0`–`d5`, so shadowing
//! and forward references are common; a rename draws from `d0`–`d7`, so it
//! lands on an existing name about three times in four. Bodies change type
//! (integer, string, thunk) and value, and one edit changes a body's value
//! alone; ascriptions include `El 0 name`, the one type position that reads a
//! definition, so value-only edits under type-position reads are reached on
//! purpose. Nothing is renamed apart:
//! shadowing under a type-position read is generated as written.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use proptest::prelude::Just;
use proptest::prelude::Strategy;
use proptest::prelude::any;
use proptest::prop_oneof;
use proptest::sample::Index;
use proptest::sample::select;

use crate::common::Ascription;
use crate::common::Body;
use crate::common::Natural;
use crate::common::Stmt;

/// The cases each property runs.
pub const CASES: u32 = 400;

/// An edit to a statement list. Insertion clamps to the end; integer rank is
/// reduced modulo the integer-body count; other missing indices are no-ops.
/// Thus edits sized to the first program remain total as a sequence changes it.
///
/// # Specification
/// - executable: none — this command declaration is not callable; apply and
///   revalue specify its state transitions.
///
/// # Adequacy
/// - hypothesis: L3 — boundary indices, coordinated rename and modular integer
///   rank have exact resulting statement lists.
/// - witness: `tests::generate::edits_have_total_boundary_semantics`
/// - witness: `tests::generate::coordinated_rename_rewrites_bindings_and_reads`
/// - witness: `tests::generate::revalue_preserves_metadata_and_classifies_exactly`
#[derive(Clone, Debug)]
pub enum Edit
{
    /// Replace the statement at the index.
    Replace(usize, Stmt),
    /// Insert a statement before the index.
    Insert(usize, Stmt),
    /// Delete the statement at the index.
    Delete(usize),
    /// Rename the definition at the index, every definition of the same name
    /// and every reader of it, in one edit.
    Rename(usize, String),
    /// Exchange two statements.
    Swap(usize, usize),
    /// Set or clear the ascription of the statement at the index.
    Ascribe(usize, Option<Ascription>),
    /// Give the integer-bodied statement of this rank, counted modulo how
    /// many there are, this value: a value-only edit, keeping the name, the
    /// ascription and the body's type.
    Revalue(usize, u64),
}

/// How many statements a program holds: the span an edit's indices come from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ProgramLength(pub usize);

/// A name from the rename pool.
///
/// # Specification
/// - ensures: samples names from the rename pool.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — generated edit chains exercise renaming into existing and
///   fresh names. This evidence concerns sampled edits, not exhaustiveness of
///   the distribution.
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
pub fn name() -> impl Strategy<Value = String>
{
    (0_usize .. 8_usize).prop_map(|index| format!("d{index}"))
}

/// A name from the statement pool.
///
/// # Specification
/// - ensures: samples names from the statement pool, allowing repeats.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — generated programs exercise shadowing and unbound
///   references; the fixed shadowing witness supplies a pointwise boundary.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::defects::a_shadowing_program_under_a_type_position_read_checks_and_terminates`
pub fn statement_name() -> impl Strategy<Value = String>
{
    (0_usize .. 6_usize).prop_map(|index| format!("d{index}"))
}

/// An ascription, or none.
///
/// # Specification
/// - ensures: samples absent, ground, returner and code ascriptions.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — the differential samples these forms; a deterministic
///   census requires type-position reads to remain reachable, without pinning
///   weights.
/// - witness: `tests::defects::the_generator_reaches_value_only_edits_under_type_position_reads`
pub fn ascription() -> impl Strategy<Value = Option<Ascription>>
{
    prop_oneof![
        3 => Just(None),
        1 => Just(Some(Ascription::Integer)),
        1 => Just(Some(Ascription::Text)),
        1 => Just(Some(Ascription::ReturnsInteger)),
        3 => statement_name().prop_map(|name| Some(Ascription::CodeOf(name))),
    ]
}

/// A body.
///
/// # Specification
/// - ensures: samples integer, reference, string, thunk and hole bodies.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — sampled edits exercise the body vocabulary; the
///   value-only census prevents loss of the integer-change class. It is not a
///   frequency law for every body.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::defects::the_generator_reaches_value_only_edits_under_type_position_reads`
pub fn body() -> impl Strategy<Value = Body>
{
    prop_oneof![
        3 => (0_u64 .. 20_u64).prop_map(Body::Int),
        3 => statement_name().prop_map(Body::Ref),
        1 => select(["", "a", "hi", "xyz"].as_slice()).prop_map(|content| Body::Str(String::from(content))),
        1 => (0_u64 .. 3_u64).prop_map(Body::Thunk),
        1 => Just(Body::Hole),
    ]
}

/// A statement.
///
/// # Specification
/// - ensures: samples a statement whose name, ascription and body come from
///   their respective domains.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — complete sampled statements pass through the
///   module/incremental differential. The stage golden separately fixes the
///   fixture interpretation.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::common::lowering_handles_numeric_and_binding_boundaries`
pub fn statement() -> impl Strategy<Value = Stmt>
{
    (statement_name(), ascription(), body()).prop_map(|(name, ascription, body)| Stmt {
        name,
        ascription,
        body,
    })
}

/// A program of one to six statements, each `El 0 name` ascription after the
/// first statement naming an earlier definition.
///
/// # Specification
/// - ensures: samples one to six statements; each code ascription after the
///   first names an earlier definition.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — deterministic sampling retains the value-change/type-read
///   class. L3 — retargeting with a short pick list preserves untouched rows
///   and chooses the only preceding name for its covered row.
/// - witness: `tests::defects::the_generator_reaches_value_only_edits_under_type_position_reads`
/// - witness: `tests::generate::retarget_preserves_unselected_rows`
pub fn program() -> impl Strategy<Value = Vec<Stmt>>
{
    (
        proptest::collection::vec(statement(), 1_usize .. 7_usize),
        proptest::collection::vec(any::<Index>(), 6_usize),
    )
        .prop_map(|(statements, picks)| retarget(statements, &picks))
}

/// `statements` with each type-position read after the first statement
/// pointed at the earlier definition `picks` chooses, so a generated reader
/// reads a definition the program has rather than one name in six.
///
/// # Specification
/// - requires: nothing.
/// - ensures: rows and bodies are retained; a code ascription after the first
///   is redirected when its position has a pick, and otherwise retained.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — no picks preserve the whole list; a covered code read
///   chooses its sole predecessor while the first and uncovered reads remain
///   unchanged. The predicate checks length and selected target names without
///   cloning the input.
/// - witness: `tests::generate::retarget_preserves_unselected_rows`
#[spec(
    captures: [length = statements.len()],
    ensures: |ret| {
        ret.len() == length
            && ret.iter().enumerate().skip(1).all(|(at, statement)| {
                match (&statement.ascription, picks.get(at)) {
                    | (&Some(Ascription::CodeOf(ref name)), Some(pick)) => ret
                        .get(pick.index(at))
                        .is_some_and(|earlier| name == &earlier.name),
                    | _ => true,
                }
            })
    },
)]
fn retarget(
    mut statements: Vec<Stmt>,
    picks: &[Index],
) -> Vec<Stmt>
{
    for at in 1_usize .. statements.len() {
        let earlier = picks
            .get(at)
            .and_then(|pick| statements.get(pick.index(at)))
            .map(|statement| statement.name.clone());
        if let (
            Some(earlier),
            Some(&mut Stmt {
                ascription: Some(Ascription::CodeOf(ref mut read)),
                ..
            }),
        ) = (earlier, statements.get_mut(at))
        {
            *read = earlier;
        }
    }
    statements
}

/// One edit sized to a program of `length` statements.
///
/// # Specification
/// - ensures: samples every edit kind using a nonempty index span, including
///   when length is zero; application remains total after length changes.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — generated edit chains reuse the original span. L3 — fixed
///   extreme and empty-list edits establish application boundaries
///   independently of sampling.
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
/// - witness: `tests::generate::edits_have_total_boundary_semantics`
pub fn edit(length: ProgramLength) -> impl Strategy<Value = Edit>
{
    let span = length.0.max(1_usize);
    prop_oneof![
        1 => (0_usize .. span, statement()).prop_map(|(at, statement)| Edit::Replace(at, statement)),
        1 => (0_usize ..= span, statement()).prop_map(|(at, statement)| Edit::Insert(at, statement)),
        1 => (0_usize .. span).prop_map(Edit::Delete),
        1 => (0_usize .. span, name()).prop_map(|(at, to)| Edit::Rename(at, to)),
        1 => (0_usize .. span, 0_usize .. span).prop_map(|(first, second)| Edit::Swap(first, second)),
        1 => (0_usize .. span, ascription()).prop_map(|(at, ascription)| Edit::Ascribe(at, ascription)),
        3 => (0_usize .. span, 0_u64 .. 20_u64).prop_map(|(at, value)| Edit::Revalue(at, value)),
    ]
}

/// A program and one edit sized to it.
///
/// # Specification
/// - ensures: samples a program with an edit sized from that program.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — the single-edit differential and deterministic census
///   observe paired samples through the real strategy runner.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::defects::the_generator_reaches_value_only_edits_under_type_position_reads`
pub fn program_and_edit() -> impl Strategy<Value = (Vec<Stmt>, Edit)>
{
    program().prop_flat_map(|statements| {
        let length = ProgramLength(statements.len());
        (Just(statements), edit(length))
    })
}

/// A program and a chain of one to four edits sized to it.
///
/// # Specification
/// - ensures: samples a program and one to four edits, all sized from the
///   initial program.
/// - executable: none — the predicate expansion rejects opaque strategy
///   returns; generated values are observed through the runner protocol, not at
///   construction.
///
/// # Adequacy
/// - hypothesis: L2 — the edit-chain differential resumes each result into the
///   next and round-trips every checkpoint set. It does not assert statistical
///   independence of samples.
/// - witness: `tests::incremental::edit_sequences_preserve_zero_drift`
pub fn program_and_edits() -> impl Strategy<Value = (Vec<Stmt>, Vec<Edit>)>
{
    program().prop_flat_map(|statements| {
        let length = ProgramLength(statements.len());
        (
            Just(statements),
            proptest::collection::vec(edit(length), 1_usize .. 5_usize),
        )
    })
}

/// `statements` with `edit` applied.
///
/// # Specification
/// - requires: nothing.
/// - ensures: insertion clamps to the end, missing direct indices are no-ops,
///   rename rewrites every matching binding and term/type read, and revalue
///   changes only the integer body selected by modular rank. Other fields
///   retain their source values.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and extreme indices, valid
///   replacements/deletions/swaps/ascriptions, a coordinated shadowing rename
///   and a wrapped integer rank have exact list outcomes. The predicate
///   compares borrowed source rows rather than allocating another edit.
/// - witness: `tests::generate::edits_have_total_boundary_semantics`
/// - witness: `tests::generate::coordinated_rename_rewrites_bindings_and_reads`
/// - witness: `tests::generate::revalue_preserves_metadata_and_classifies_exactly`
#[spec(
    ensures: |ret| match *edit {
        | Edit::Insert(at, ref statement) => {
            let at = at.min(statements.len());
            statements.len().checked_add(1) == Some(ret.len())
                && ret.get(at) == Some(statement)
                && ret.get(.. at) == statements.get(.. at)
                && ret.get(at.saturating_add(1) ..) == statements.get(at ..)
        },
        | Edit::Delete(at) if at < statements.len() => {
            ret.len().checked_add(1) == Some(statements.len())
                && ret.iter().enumerate().all(|(index, row)| {
                    Some(row) == statements.get(index.saturating_add(usize::from(index >= at)))
                })
        },
        | Edit::Replace(at, ref replacement) => {
            ret.len() == statements.len()
                && ret
                    .iter()
                    .zip(statements)
                    .enumerate()
                    .all(|(index, (row, before))| {
                        if index == at {
                            row == replacement
                        }
                        else {
                            row == before
                        }
                    })
        },
        | Edit::Swap(first, second) if first < statements.len() && second < statements.len() => {
            ret.len() == statements.len()
                && ret.iter().enumerate().all(|(index, row)| {
                    Some(row)
                        == statements.get(if index == first {
                            second
                        }
                        else if index == second {
                            first
                        }
                        else {
                            index
                        })
                })
        },
        | Edit::Ascribe(at, ref ascription) => {
            ret.len() == statements.len()
                && ret
                    .iter()
                    .zip(statements)
                    .enumerate()
                    .all(|(index, (row, before))| {
                        if index == at {
                            row.name == before.name
                                && row.body == before.body
                                && &row.ascription == ascription
                        }
                        else {
                            row == before
                        }
                    })
        },
        | Edit::Rename(at, ref to) => ret.len() == statements.len()
            && statements.get(at).map_or_else(
                || ret.as_slice() == statements,
                |old| {
                    ret.iter().zip(statements).all(|(row, before)| {
                        row.name
                            == (if before.name == old.name {
                                to
                            }
                            else {
                                &before.name
                            })
                            .as_str()
                            && match before.body {
                                | Body::Ref(ref name) if name == &old.name => match row.body {
                                    | Body::Ref(ref name) => name == to,
                                    | _ => false,
                                },
                                | _ => row.body == before.body,
                            }
                            && match before.ascription {
                                | Some(Ascription::CodeOf(ref name)) if name == &old.name => {
                                    match row.ascription {
                                        | Some(Ascription::CodeOf(ref name)) => name == to,
                                        | _ => false,
                                    }
                                },
                                | _ => row.ascription == before.ascription,
                            }
                    })
                },
            ),
        | Edit::Revalue(rank, value) => {
            let count = statements
                .iter()
                .filter(|statement| matches!(statement.body, Body::Int(_)))
                .count();
            let selected = rank.checked_rem(count).and_then(|rank| {
                statements
                    .iter()
                    .enumerate()
                    .filter(|&(_, statement)| matches!(statement.body, Body::Int(_)))
                    .nth(rank)
                    .map(|(index, _)| index)
            });
            ret.len() == statements.len()
                && ret
                    .iter()
                    .zip(statements)
                    .enumerate()
                    .all(|(index, (row, before))| {
                        if selected == Some(index) {
                            row.name == before.name
                                && row.ascription == before.ascription
                                && row.body == Body::Int(value)
                        }
                        else {
                            row == before
                        }
                    })
        },
        | Edit::Delete(_) | Edit::Swap(..) => ret.as_slice() == statements,
    },
)]
pub fn apply(
    statements: &[Stmt],
    edit: &Edit,
) -> Vec<Stmt>
{
    let mut edited = statements.to_vec();
    match *edit {
        | Edit::Replace(at, ref statement) => {
            if let Some(slot) = edited.get_mut(at) {
                slot.clone_from(statement);
            }
        },
        | Edit::Insert(at, ref statement) => {
            edited.insert(at.min(edited.len()), statement.clone());
        },
        | Edit::Delete(at) => {
            if at < edited.len() {
                let _removed = edited.remove(at);
            }
        },
        | Edit::Rename(at, ref to) => {
            if let Some(old) = edited.get(at).map(|slot| slot.name.clone()) {
                for slot in &mut edited {
                    if slot.name == old {
                        slot.name.clone_from(to);
                    }
                    if let Body::Ref(ref mut read) = slot.body
                        && *read == old
                    {
                        read.clone_from(to);
                    }
                    if let Some(Ascription::CodeOf(ref mut read)) = slot.ascription
                        && *read == old
                    {
                        read.clone_from(to);
                    }
                }
            }
        },
        | Edit::Swap(first, second) => {
            if first < edited.len() && second < edited.len() {
                edited.swap(first, second);
            }
        },
        | Edit::Ascribe(at, ref ascription) => {
            if let Some(slot) = edited.get_mut(at) {
                slot.ascription.clone_from(ascription);
            }
        },
        | Edit::Revalue(rank, value) => {
            let _revalued = revalue(&mut edited, Rank(rank), Natural(value));
        },
    }
    edited
}

/// What a value-only edit did.
///
/// # Specification
/// - executable: none — these outcome tags have no invocation; revalue relates
///   them to the selected old and new values.
///
/// # Adequacy
/// - hypothesis: L3 — absence of integer bodies, an equal replacement and a
///   changed replacement select distinct outcomes while retaining other
///   metadata.
/// - witness: `tests::generate::revalue_preserves_metadata_and_classifies_exactly`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Revalued
{
    /// An integer body took a different value.
    Changed,
    /// The integer body already held the value.
    Same,
    /// No statement has an integer body.
    Absent,
}

/// The rank of an integer-bodied statement, counted modulo how many there are.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Rank(pub usize);

/// Give the integer-bodied statement of `rank` the value `value`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: rank selects modulo the number of integer bodies; only that body
///   changes. The result distinguishes no integer, equal value and change.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a maximal rank selects the second of two interspersed
///   integers, keeps names and ascriptions, and distinguishes change from
///   equality. Thunk/string-only input is absent, not an integer candidate. The
///   predicate captures only the selected ordinal and old number.
/// - witness: `tests::generate::revalue_preserves_metadata_and_classifies_exactly`
#[spec(
    captures: [selected = 'selected: {
        let count = statements
            .iter()
            .filter(|statement| matches!(statement.body, Body::Int(_)))
            .count();
        let Some(rank) = rank.0.checked_rem(count)
        else {
            break 'selected None;
        };
        statements
            .iter()
            .enumerate()
            .filter_map(|(index, statement)| match statement.body {
                | Body::Int(old) => Some((index, old)),
                | _ => None,
            })
            .nth(rank)
    }],
    ensures: |ret| match selected {
        | None => ret == Revalued::Absent,
        | Some((index, old)) => {
            ret == (if old == value.0 {
                Revalued::Same
            }
            else {
                Revalued::Changed
            }) && statements
                .get(index)
                .is_some_and(|statement| statement.body == Body::Int(value.0))
        },
    },
)]
pub fn revalue(
    statements: &mut [Stmt],
    rank: Rank,
    value: Natural,
) -> Revalued
{
    let count = statements
        .iter()
        .filter(|statement| matches!(statement.body, Body::Int(_)))
        .count();
    let slot = rank.0.checked_rem(count).and_then(|rank| {
        statements
            .iter_mut()
            .filter(|statement| matches!(statement.body, Body::Int(_)))
            .nth(rank)
    });
    match slot {
        | Some(&mut Stmt {
            body: Body::Int(ref mut old),
            ..
        }) => {
            if *old == value.0 {
                Revalued::Same
            }
            else {
                *old = value.0;
                Revalued::Changed
            }
        },
        | Some(_) | None => Revalued::Absent,
    }
}

#[test]
fn retarget_preserves_unselected_rows()
{
    let source = vec![
        Stmt {
            name: String::from("first"),
            ascription: Some(Ascription::CodeOf(String::from("leave-first"))),
            body: Body::Int(1),
        },
        Stmt {
            name: String::from("second"),
            ascription: Some(Ascription::CodeOf(String::from("forward"))),
            body: Body::Ref(String::from("first")),
        },
        Stmt {
            name: String::from("third"),
            ascription: Some(Ascription::CodeOf(String::from("leave-third"))),
            body: Body::Thunk(2),
        },
    ];
    assert_eq!(retarget(source.clone(), &[]), source);
    let tree = proptest::collection::vec(any::<Index>(), 2_usize)
        .new_tree(&mut proptest::test_runner::TestRunner::deterministic())
        .expect("two picks");
    let picks = proptest::strategy::ValueTree::current(&tree);
    let mut expected = source.clone();
    expected.get_mut(1).expect("second row").ascription =
        Some(Ascription::CodeOf(String::from("first")));
    assert_eq!(retarget(source, &picks), expected);
}

#[test]
fn edits_have_total_boundary_semantics()
{
    let a = Stmt {
        name: String::from("a"),
        ascription: None,
        body: Body::Int(1),
    };
    let b = Stmt {
        name: String::from("b"),
        ascription: Some(Ascription::Integer),
        body: Body::Int(2),
    };
    let new = Stmt {
        name: String::from("new"),
        ascription: Some(Ascription::Text),
        body: Body::Str(String::from("x")),
    };
    let source = [a.clone(), b.clone()];
    for edit in [
        Edit::Replace(usize::MAX, new.clone()),
        Edit::Delete(usize::MAX),
        Edit::Rename(usize::MAX, String::from("other")),
        Edit::Swap(0, usize::MAX),
        Edit::Ascribe(usize::MAX, None),
    ] {
        assert_eq!(apply(&source, &edit), source);
        assert_eq!(apply(&[], &edit), []);
    }
    assert_eq!(apply(&[], &Edit::Revalue(usize::MAX, 7)), []);
    assert_eq!(
        apply(&[], &Edit::Insert(usize::MAX, new.clone())),
        core::slice::from_ref(&new)
    );
    for (edit, expected) in [
        (Edit::Insert(usize::MAX, new.clone()), vec![
            a.clone(),
            b.clone(),
            new.clone(),
        ]),
        (Edit::Insert(0, new.clone()), vec![
            new.clone(),
            a.clone(),
            b.clone(),
        ]),
        (Edit::Replace(1, new.clone()), vec![a.clone(), new]),
        (Edit::Delete(0), vec![b.clone()]),
        (Edit::Swap(0, 1), vec![b, a.clone()]),
        (Edit::Ascribe(1, Some(Ascription::Text)), vec![a, Stmt {
            name: String::from("b"),
            ascription: Some(Ascription::Text),
            body: Body::Int(2),
        }]),
    ] {
        assert_eq!(apply(&source, &edit), expected);
    }
}

#[test]
fn coordinated_rename_rewrites_bindings_and_reads()
{
    let source = [
        Stmt {
            name: String::from("x"),
            ascription: None,
            body: Body::Int(1),
        },
        Stmt {
            name: String::from("x"),
            ascription: Some(Ascription::CodeOf(String::from("x"))),
            body: Body::Ref(String::from("x")),
        },
        Stmt {
            name: String::from("z"),
            ascription: Some(Ascription::CodeOf(String::from("x"))),
            body: Body::Str(String::from("x")),
        },
        Stmt {
            name: String::from("other"),
            ascription: Some(Ascription::Text),
            body: Body::Ref(String::from("elsewhere")),
        },
    ];
    let expected = [
        Stmt {
            name: String::from("z"),
            ascription: None,
            body: Body::Int(1),
        },
        Stmt {
            name: String::from("z"),
            ascription: Some(Ascription::CodeOf(String::from("z"))),
            body: Body::Ref(String::from("z")),
        },
        Stmt {
            name: String::from("z"),
            ascription: Some(Ascription::CodeOf(String::from("z"))),
            body: Body::Str(String::from("x")),
        },
        source.get(3).expect("untouched row").clone(),
    ];
    assert_eq!(
        apply(&source, &Edit::Rename(0, String::from("z"))),
        expected
    );
}

#[test]
fn revalue_preserves_metadata_and_classifies_exactly()
{
    let mut source = vec![
        Stmt {
            name: String::from("first"),
            ascription: Some(Ascription::Integer),
            body: Body::Int(1),
        },
        Stmt {
            name: String::from("text"),
            ascription: Some(Ascription::Text),
            body: Body::Str(String::from("7")),
        },
        Stmt {
            name: String::from("second"),
            ascription: Some(Ascription::CodeOf(String::from("first"))),
            body: Body::Int(7),
        },
    ];
    let before = source.clone();
    assert_eq!(
        revalue(&mut source, Rank(usize::MAX), Natural(99)),
        Revalued::Changed
    );
    let expected = vec![
        before.first().expect("first row").clone(),
        before.get(1).expect("text row").clone(),
        Stmt {
            name: String::from("second"),
            ascription: Some(Ascription::CodeOf(String::from("first"))),
            body: Body::Int(99),
        },
    ];
    assert_eq!(source, expected);
    assert_eq!(apply(&before, &Edit::Revalue(usize::MAX, 99)), expected);
    assert_eq!(
        revalue(&mut source, Rank(usize::MAX), Natural(99)),
        Revalued::Same
    );
    assert_eq!(source, expected);
    let mut no_integer = [
        Stmt {
            name: String::from("thunk"),
            ascription: None,
            body: Body::Thunk(7),
        },
        Stmt {
            name: String::from("text"),
            ascription: None,
            body: Body::Str(String::from("7")),
        },
    ];
    let before = no_integer.clone();
    assert_eq!(
        revalue(&mut no_integer, Rank(usize::MAX), Natural(99)),
        Revalued::Absent
    );
    assert_eq!(no_integer, before);
}
