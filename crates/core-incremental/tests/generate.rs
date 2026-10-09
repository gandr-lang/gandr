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

/// An edit to a statement list. An index the edit cannot address makes it a
/// no-op, so a sequence sized to its first program stays total as later edits
/// change the length.
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
/// trivial.
pub fn name() -> impl Strategy<Value = String>
{
    (0_usize .. 8_usize).prop_map(|index| format!("d{index}"))
}

/// A name from the statement pool.
///
/// # Specification
/// trivial.
pub fn statement_name() -> impl Strategy<Value = String>
{
    (0_usize .. 6_usize).prop_map(|index| format!("d{index}"))
}

/// An ascription, or none.
///
/// # Specification
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
