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

use anodized::spec;
use proptest::prelude::Just;
use proptest::prelude::Strategy;
use proptest::prop_oneof;
use proptest::sample::select;

/// The cases each property runs.
pub const CASES: u32 = 200;

/// A signature a statement may carry.
///
/// # Specification
/// - requires: the consuming operation’s documented context.
/// - ensures: Each variant names the corresponding scalar or delayed-integer
///   signature.
/// - executable: none — The model declaration has no runtime invocation; apply
///   and render state executable relations over its payload and the surrounding
///   statement list.
///
/// # Adequacy
/// - hypothesis: L2 — the configured finite-size generated revisions and edit
///   chains, observed as complete core-image replay and fresh/incremental
///   typing agreement. The operation predicates distinguish mutations to each
///   model field.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Ascription
{
    /// `Integer`.
    Integer,
    /// `String`.
    Text,
    /// `+U (-F Integer)`: a delayed integer computation.
    Delayed,
}

/// What a statement defines.
///
/// # Specification
/// - requires: the consuming operation’s documented context.
/// - ensures: Each variant retains the payload of its literal, reference,
///   delayed computation, function or absent body.
/// - executable: none — The model declaration has no runtime invocation; apply
///   and render state executable relations over its payload and the surrounding
///   statement list.
///
/// # Adequacy
/// - hypothesis: L2 — the configured finite-size generated revisions and edit
///   chains, observed as complete core-image replay and fresh/incremental
///   typing agreement. The operation predicates distinguish mutations to each
///   model field.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
    /// A function tail `(x: Integer) -> -F Integer` returning an integer
    /// literal; it carries its own signature, so the statement's ascription
    /// is not written.
    Function(u64),
    /// No definition: the signature alone, owed.
    Absent,
}

/// One statement.
///
/// # Specification
/// - requires: the consuming operation’s documented context.
/// - ensures: A name, optional signature and body form one model statement;
///   repeated names and unbound readers are valid generated inputs.
/// - executable: none — The model declaration has no runtime invocation; apply
///   and render state executable relations over its payload and the surrounding
///   statement list.
///
/// # Adequacy
/// - hypothesis: L2 — the configured finite-size generated revisions and edit
///   chains, observed as complete core-image replay and fresh/incremental
///   typing agreement. The operation predicates distinguish mutations to each
///   model field.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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

/// An edit to a statement list. Unaddressed updates and deletions are no-ops;
/// insertion clamps its position to the current end, so an edit chain remains
/// total as earlier edits change its length.
///
/// # Specification
/// - requires: the consuming operation’s documented context.
/// - ensures: Each variant names one total statement-list transformation; stale
///   insertion positions clamp and other unaddressed edits do nothing.
/// - executable: none — The model declaration has no runtime invocation; apply
///   and render state executable relations over its payload and the surrounding
///   statement list.
///
/// # Adequacy
/// - hypothesis: L2 — the configured finite-size generated revisions and edit
///   chains, observed as complete core-image replay and fresh/incremental
///   typing agreement. The operation predicates distinguish mutations to each
///   model field.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - requires: nothing.
/// - ensures: Draws absence, integer, text and delayed-integer signatures.
/// - panics: none.
/// - executable: none — The result is a dormant opaque strategy, not a
///   generated value. Observing its choices requires a test runner and executes
///   generation; there is no borrowed sample to inspect at this function’s
///   return.
///
/// # Adequacy
/// - hypothesis: L2 — the configured 200 generated revision pairs or edit
///   chains over the stated finite name, literal and size bounds, observed
///   through full edit replay and incremental/fresh-checker equality. These
///   bounded draws exercise the strategy; they do not prove its distribution.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - requires: nothing.
/// - ensures: Draws literals, references, delayed returns, calls, function
///   tails and absent bodies within the documented finite pools.
/// - panics: none.
/// - executable: none — The result is a dormant opaque strategy, not a
///   generated value. Observing its choices requires a test runner and executes
///   generation; there is no borrowed sample to inspect at this function’s
///   return.
///
/// # Adequacy
/// - hypothesis: L2 — the configured 200 generated revision pairs or edit
///   chains over the stated finite name, literal and size bounds, observed
///   through full edit replay and incremental/fresh-checker equality. These
///   bounded draws exercise the strategy; they do not prove its distribution.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - requires: nothing.
/// - ensures: Combines independently drawn name, signature and body choices
///   without requiring that a reference is already bound.
/// - panics: none.
/// - executable: none — The result is a dormant opaque strategy, not a
///   generated value. Observing its choices requires a test runner and executes
///   generation; there is no borrowed sample to inspect at this function’s
///   return.
///
/// # Adequacy
/// - hypothesis: L2 — the configured 200 generated revision pairs or edit
///   chains over the stated finite name, literal and size bounds, observed
///   through full edit replay and incremental/fresh-checker equality. These
///   bounded draws exercise the strategy; they do not prove its distribution.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - requires: nothing.
/// - ensures: Draws one through six statements, including repeated names and
///   forward references.
/// - panics: none.
/// - executable: none — The result is a dormant opaque strategy, not a
///   generated value. Observing its choices requires a test runner and executes
///   generation; there is no borrowed sample to inspect at this function’s
///   return.
///
/// # Adequacy
/// - hypothesis: L2 — the configured 200 generated revision pairs or edit
///   chains over the stated finite name, literal and size bounds, observed
///   through full edit replay and incremental/fresh-checker equality. These
///   bounded draws exercise the strategy; they do not prove its distribution.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - requires: nothing.
/// - ensures: Draws every edit kind using the original revision’s extent; an
///   empty extent still offers index zero and insertions can target the end.
/// - panics: none.
/// - executable: none — The result is a dormant opaque strategy, not a
///   generated value. Observing its choices requires a test runner and executes
///   generation; there is no borrowed sample to inspect at this function’s
///   return.
///
/// # Adequacy
/// - hypothesis: L2 — the configured 200 generated revision pairs or edit
///   chains over the stated finite name, literal and size bounds, observed
///   through full edit replay and incremental/fresh-checker equality. These
///   bounded draws exercise the strategy; they do not prove its distribution.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - requires: nothing.
/// - ensures: Draws one revision and one through four edits sized to that
///   original revision, so later positions may become stale.
/// - panics: none.
/// - executable: none — The result is a dormant opaque strategy, not a
///   generated value. Observing its choices requires a test runner and executes
///   generation; there is no borrowed sample to inspect at this function’s
///   return.
///
/// # Adequacy
/// - hypothesis: L2 — the configured 200 generated revision pairs or edit
///   chains over the stated finite name, literal and size bounds, observed
///   through full edit replay and incremental/fresh-checker equality. These
///   bounded draws exercise the strategy; they do not prove its distribution.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
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
/// - ensures: applies the named edit without changing unrelated fields or
///   statement order. Rename updates all declarations and readers of the
///   selected name; revalue changes only numeric bodies. Missing updates and
///   deletions are identities, while insertion clamps to the current end.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — bounded generated edit chains, including positions made
///   stale by preceding edits, checked through full incremental/fresh-checker
///   equality. The executable per-position relation independently fixes the
///   edit’s requested mutation and frame conditions, without cloning a second
///   expected list.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
#[spec(
    ensures: |ret| match *edit {
    Edit::Replace(at, ref replacement) => {
        ret.len() == statements.len()
            && ret
                .iter()
                .enumerate()
                .all(|(index, found)| {
                    if index == at {
                        found == replacement
                    } else {
                        statements.get(index) == Some(found)
                    }
                })
    }
    Edit::Insert(at, ref inserted) => {
        let at = at.min(statements.len());
        ret.len() == statements.len().saturating_add(1_usize)
            && ret
                .iter()
                .enumerate()
                .all(|(index, found)| {
                    if index == at {
                        found == inserted
                    } else {
                        statements
                            .get(
                                if index < at {
                                    index
                                } else {
                                    index.saturating_sub(1_usize)
                                },
                            ) == Some(found)
                    }
                })
    }
    Edit::Delete(at) => {
        ret.len() == statements.len().saturating_sub(usize::from(at < statements.len()))
            && ret
                .iter()
                .enumerate()
                .all(|(index, found)| {
                    statements
                        .get(
                            if index < at {
                                index
                            } else {
                                index.saturating_add(1_usize)
                            },
                        ) == Some(found)
                })
    }
    Edit::Rename(at, to) => {
        statements
            .get(at)
            .map_or_else(
                || ret == statements,
                |renamed| {
                    ret.len() == statements.len()
                        && ret
                            .iter()
                            .zip(statements)
                            .all(|(found, before)| {
                                found.name
                                    == if before.name == renamed.name {
                                        to
                                    } else {
                                        before.name
                                    } && found.ascription == before.ascription
                                    && match before.body {
                                        Body::Ref(read) => {
                                            matches!(
                                                found.body, Body::Ref(actual) if actual == if read ==
                                                renamed.name { to } else { read }
                                            )
                                        }
                                        Body::Call(read) => {
                                            matches!(
                                                found.body, Body::Call(actual) if actual == if read ==
                                                renamed.name { to } else { read }
                                            )
                                        }
                                        _ => found.body == before.body,
                                    }
                            })
                },
            )
    }
    Edit::Swap(first, second) => {
        ret.len() == statements.len()
            && ret
                .iter()
                .enumerate()
                .all(|(index, found)| {
                    statements
                        .get(
                            if first < statements.len() && second < statements.len() {
                                if index == first {
                                    second
                                } else if index == second {
                                    first
                                } else {
                                    index
                                }
                            } else {
                                index
                            },
                        ) == Some(found)
                })
    }
    Edit::Ascribe(at, ascription) => {
        ret.len() == statements.len()
            && ret
                .iter()
                .zip(statements)
                .enumerate()
                .all(|(index, (found, before))| {
                    found.name == before.name && found.body == before.body
                        && found.ascription
                            == if index == at { ascription } else { before.ascription }
                })
    }
    Edit::Revalue(at, value) => {
        ret.len() == statements.len()
            && ret
                .iter()
                .zip(statements)
                .enumerate()
                .all(|(index, (found, before))| {
                    found.name == before.name && found.ascription == before.ascription
                        && if index == at {
                            match before.body {
                                Body::Int(_) => found.body == Body::Int(value),
                                Body::Delay(_) => found.body == Body::Delay(value),
                                Body::Function(_) => found.body == Body::Function(value),
                                _ => found.body == before.body,
                            }
                        } else {
                            found.body == before.body
                        }
                })
    }
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
/// - requires: text bodies contain no quotes, backslashes or line breaks; the
///   generator’s text pool satisfies this.
/// - ensures: writes each signature and body in statement order with the same
///   name, literal and reference payloads. Function tails carry their own
///   signature and ignore the separate ascription; an absent body emits no
///   definition.
/// - panics: none; writing to String cannot refuse.
///
/// # Adequacy
/// - hypothesis: L2 — bounded generated revisions through full core-image
///   replay and incremental/fresh-checker equality. The predicate independently
///   reads row boundaries and scalar payloads with standard string and integer
///   observers, catching dropped signatures, changed literals, names,
///   references and row order without rendering another string.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::edit::apply_of_diff_reproduces_new`
/// - witness: `tests::edit::self_diff_is_identity`
#[spec(
    requires: statements
    .iter()
    .all(|statement| {
        if let Body::Str(text) = statement.body {
            !text.contains(['\"', '\\', '\n', '\r'])
        } else {
            true
        }
    }),
    ensures: |ret| {
    let mut lines = ret.lines();
    let correct = statements
        .iter()
        .all(|statement| {
            if let Body::Function(literal) = statement.body {
                lines
                    .next()
                    .is_some_and(|line| {
                        line.split_once("(x: Integer) -> -F Integer { ret ")
                            .is_some_and(|(name, tail)| {
                                name
                                    .strip_prefix("def d")
                                    .is_some_and(|name| {
                                        name.parse::<usize>() == Ok(statement.name)
                                    })
                                    && tail
                                        .strip_suffix(" }")
                                        .is_some_and(|number| number.parse::<u64>() == Ok(literal))
                            })
                    })
            } else {
                let signature = statement
                    .ascription
                    .is_none_or(|ascription| {
                        lines
                            .next()
                            .is_some_and(|line| {
                                line.split_once(" : ")
                                    .is_some_and(|(name, tail)| {
                                        name
                                            .strip_prefix("def d")
                                            .is_some_and(|name| {
                                                name.parse::<usize>() == Ok(statement.name)
                                            })
                                            && tail
                                                == match ascription {
                                                    Ascription::Integer => "Integer ;",
                                                    Ascription::Text => "String ;",
                                                    Ascription::Delayed => "+U (-F Integer) ;",
                                                }
                                    })
                            })
                    });
                signature
                    && (matches!(statement.body, Body::Absent)
                        || lines
                            .next()
                            .is_some_and(|line| {
                                line.split_once(" = ")
                                    .is_some_and(|(name, tail)| {
                                        name
                                            .strip_prefix("def d")
                                            .is_some_and(|name| {
                                                name.parse::<usize>() == Ok(statement.name)
                                            })
                                            && tail
                                                .strip_suffix(" ;")
                                                .is_some_and(|body| match statement.body {
                                                    Body::Int(value) => body.parse::<u64>() == Ok(value),
                                                    Body::Str(text) => {
                                                        body
                                                            .strip_prefix('"')
                                                            .and_then(|text| text.strip_suffix('"')) == Some(text)
                                                    }
                                                    Body::Ref(index) => {
                                                        body.strip_prefix('d')
                                                            .is_some_and(|name| name.parse::<usize>() == Ok(index))
                                                    }
                                                    Body::Delay(value) => {
                                                        body.strip_prefix("thunk { ret ")
                                                            .and_then(|text| text.strip_suffix(" }"))
                                                            .is_some_and(|number| number.parse::<u64>() == Ok(value))
                                                    }
                                                    Body::Call(index) => {
                                                        body.strip_prefix("thunk { (force d")
                                                            .and_then(|text| text.strip_suffix(")(0) }"))
                                                            .is_some_and(|name| name.parse::<usize>() == Ok(index))
                                                    }
                                                    Body::Function(_) | Body::Absent => false,
                                                })
                                    })
                            }))
            }
        });
    correct && lines.next().is_none()
},
)]
pub fn render(statements: &[Stmt]) -> String
{
    let mut text = String::new();
    for statement in statements {
        let name = statement.name;
        if let Body::Function(literal) = statement.body {
            writeln!(
                text,
                "def d{name}(x: Integer) -> -F Integer {{ ret {literal} }}"
            )
            .expect("a string takes every write");
            continue;
        }
        if let Some(ascription) = statement.ascription {
            let written = match ascription {
                | Ascription::Integer => "Integer",
                | Ascription::Text => "String",
                | Ascription::Delayed => "+U (-F Integer)",
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
