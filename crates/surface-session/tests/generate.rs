//! Generated revisions and edits for the session's differential.
//!
//! The shape follows the incremental checker's own generator, spelled as
//! surface text: a revision holds one to six statements named from `d0`–`d5`,
//! so a second signature or definition of one name and a reference forward or
//! to nothing are common. A statement is an optional signature line and an
//! optional definition line, or a function tail; bodies change type (integer,
//! string, thunk) and value, a thunk may apply another statement's function,
//! and one edit changes a literal alone, keeping its name and type.

use core::fmt::Write as _;

use proptest::prelude::Just;
use proptest::prelude::Strategy;
use proptest::prop_oneof;
use proptest::sample::select;

/// The cases each property runs.
pub const CASES: u32 = 200;

/// A signature a statement may carry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Ascription
{
    /// `Integer`.
    Integer,
    /// `String`.
    Text,
    /// `U (F Integer)`: a delayed integer computation.
    Delayed,
}

/// What a statement defines.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body
{
    /// An integer literal.
    Int(u64),
    /// A string literal.
    Str(&'static str),
    /// A reference to the statement name of this index.
    Ref(usize),
    /// A thunk returning an integer literal.
    Delay(u64),
    /// A thunk applying the function of this index to `0`.
    Call(usize),
    /// A function tail `(x: Integer) -> F Integer` returning an integer
    /// literal; it carries its own signature, so the statement's ascription
    /// is not written.
    Function(u64),
    /// No definition: the signature alone, owed.
    Absent,
}

/// One statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Stmt
{
    /// The index of its name in the pool.
    pub name: usize,
    /// Its signature line, if any.
    pub ascription: Option<Ascription>,
    /// Its definition.
    pub body: Body,
}

/// An edit to a statement list. An index the edit cannot address makes it a
/// no-op, so a chain sized to its first revision stays total as later edits
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
    /// Rename the statement at the index, every statement of the same name
    /// and every reader of it, in one edit.
    Rename(usize, usize),
    /// Exchange two statements.
    Swap(usize, usize),
    /// Set or clear the signature of the statement at the index.
    Ascribe(usize, Option<Ascription>),
    /// Give the literal of the statement at the index this value, keeping its
    /// name, its signature and its body's type.
    Revalue(usize, u64),
}

/// A name from the statement pool.
///
/// # Specification
/// trivial.
fn name() -> impl Strategy<Value = usize>
{
    0_usize .. 6_usize
}

/// A signature, or none.
///
/// # Specification
/// trivial.
fn ascription() -> impl Strategy<Value = Option<Ascription>>
{
    prop_oneof![
        3 => Just(None),
        2 => Just(Some(Ascription::Integer)),
        1 => Just(Some(Ascription::Text)),
        2 => Just(Some(Ascription::Delayed)),
    ]
}

/// A body.
///
/// # Specification
/// trivial.
fn body() -> impl Strategy<Value = Body>
{
    prop_oneof![
        3 => (0_u64 .. 20_u64).prop_map(Body::Int),
        3 => name().prop_map(Body::Ref),
        1 => select(["", "a", "hi"].as_slice()).prop_map(Body::Str),
        1 => (0_u64 .. 3_u64).prop_map(Body::Delay),
        2 => name().prop_map(Body::Call),
        2 => (0_u64 .. 3_u64).prop_map(Body::Function),
        1 => Just(Body::Absent),
    ]
}

/// A statement.
///
/// # Specification
/// trivial.
pub fn statement() -> impl Strategy<Value = Stmt>
{
    (name(), ascription(), body()).prop_map(|(name, ascription, body)| Stmt {
        name,
        ascription,
        body,
    })
}

/// A revision of one to six statements.
///
/// # Specification
/// trivial.
pub fn program() -> impl Strategy<Value = Vec<Stmt>>
{
    proptest::collection::vec(statement(), 1_usize .. 7_usize)
}

/// How many statements a revision holds: the span an edit's indices come
/// from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ProgramLength(usize);

/// One edit sized to a revision of `length` statements.
///
/// # Specification
/// trivial.
fn edit(length: ProgramLength) -> impl Strategy<Value = Edit>
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

/// A revision and a chain of one to four edits sized to it.
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
        | Edit::Rename(at, to) => {
            if let Some(old) = edited.get(at).map(|slot| slot.name) {
                for slot in &mut edited {
                    if slot.name == old {
                        slot.name = to;
                    }
                    if let Body::Ref(ref mut read) | Body::Call(ref mut read) = slot.body
                        && *read == old
                    {
                        *read = to;
                    }
                }
            }
        },
        | Edit::Swap(first, second) => {
            if first < edited.len() && second < edited.len() {
                edited.swap(first, second);
            }
        },
        | Edit::Ascribe(at, ascription) => {
            if let Some(slot) = edited.get_mut(at) {
                slot.ascription = ascription;
            }
        },
        | Edit::Revalue(at, value) => {
            if let Some(slot) = edited.get_mut(at)
                && let Body::Int(ref mut literal)
                | Body::Delay(ref mut literal)
                | Body::Function(ref mut literal) = slot.body
            {
                *literal = value;
            }
        },
    }
    edited
}

/// The surface text of `statements`, one line per signature and definition.
///
/// # Specification
/// trivial.
pub fn render(statements: &[Stmt]) -> String
{
    let mut text = String::new();
    for statement in statements {
        let name = statement.name;
        if let Body::Function(literal) = statement.body {
            writeln!(
                text,
                "def d{name}(x: Integer) -> F Integer {{ ret {literal} }}"
            )
            .expect("a string takes every write");
            continue;
        }
        if let Some(ascription) = statement.ascription {
            let written = match ascription {
                | Ascription::Integer => "Integer",
                | Ascription::Text => "String",
                | Ascription::Delayed => "U (F Integer)",
            };
            writeln!(text, "def d{name} : {written} ;").expect("a string takes every write");
        }
        let defined = match statement.body {
            | Body::Int(literal) => format!("{literal}"),
            | Body::Str(content) => format!("\"{content}\""),
            | Body::Ref(read) => format!("d{read}"),
            | Body::Delay(literal) => format!("thunk {{ ret {literal} }}"),
            | Body::Call(read) => format!("thunk {{ (force d{read})(0) }}"),
            | Body::Function(_) | Body::Absent => continue,
        };
        writeln!(text, "def d{name} = {defined} ;").expect("a string takes every write");
    }
    text
}
