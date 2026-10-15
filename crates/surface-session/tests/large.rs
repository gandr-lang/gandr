//! A generated module of thousands of top-level forms, and edits of every
//! class over it, for the edit loop's differential and its measurement.
//!
//! The forms are the staged programs' shapes — signatures and definitions of
//! values, polymorphic functions, thunks applying them, higher-kinded type
//! functions, curried functions forced and applied — and data declarations
//! with a function casing on their constructors. Under the fixture root,
//! typed holes and a case missing a constructor state their refusals; under
//! the strict root, sequenced runs stand in their place. An edit changes one
//! form, inserts, deletes or moves one, merges one with the next by dropping
//! its terminator, splits one with a terminator inside it, or inserts a
//! top-level return, which the lowering refuses as a whole.

use anodized::spec;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_session::FormCount;
use proptest::prelude::Strategy;
use proptest::prelude::any;
use proptest::prop_oneof;

/// A position in a module's form list, taken modulo the list's length when
/// an edit is applied, so an edit chain stays total as earlier edits change
/// the length.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Position(pub usize);

/// One edit to a module's form list.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each variant names one total transformation of the list; on an
///   empty list every edit but an insertion leaves it unchanged.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Module::edit`]
///   carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L2 — generated chains of every class over generated modules of
///   both roots submit to the walk's compositions.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
/// - witness: `tests::forms::a_large_module_edit_script_submits_as_the_walk_composes_it`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormEdit
{
    /// Change one form's body, keeping its name and its type.
    Change(Position),
    /// Insert a fresh value declaration before the form.
    Insert(Position),
    /// Delete the form.
    Delete(Position),
    /// Move the form to another position.
    Move(Position, Position),
    /// Drop the form's terminator, merging it with the next.
    Merge(Position),
    /// Put a terminator inside the form, splitting it in two.
    Split(Position),
    /// Insert a top-level return before the form, which the lowering refuses
    /// as a whole.
    RefuseWhole(Position),
}

impl core::fmt::Display for FormEdit
{
    /// Writes the edit's class, as the measurement's matrix names it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one class name per variant, the positions left out.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither its previous bytes
    ///   nor its sink's failure state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the measurement prints each class once per row; a
    ///   shared name would merge two rows.
    /// - witness: `tests::forms::a_large_module_edit_script_submits_as_the_walk_composes_it`
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Change(_) => "change",
            Self::Insert(_) => "insert",
            Self::Delete(_) => "delete",
            Self::Move(..) => "move",
            Self::Merge(_) => "merge",
            Self::Split(_) => "split",
            Self::RefuseWhole(_) => "refuse whole",
        })
    }
}

/// A generated module: its top-level forms, each with its attribute lines,
/// in source order.
///
/// # Specification
/// - requires: built by [`module`].
/// - ensures: the text is every form followed by a blank line.
/// - panics: none.
/// - executable: none — this data type has no call boundary; its builder and
///   edits carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L2 — generated modules of both roots, edited, submit to the
///   walk's compositions.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module
{
    /// The forms, in source order.
    forms: Vec<String>,
    /// The next fresh name's number.
    fresh: usize,
}

impl Module
{
    /// The module's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each form in order, each followed by a blank line.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every generated module's text submits to the walk's
    ///   composition of that text.
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "test fixture: the body sums every form's length to size the text; the check sums them once more"
        )
    )]
    #[spec(ensures: |ret| ret.len() == self.forms.iter().map(|form| form.len().saturating_add(2)).sum::<usize>())]
    #[must_use]
    pub fn text(&self) -> String
    {
        let mut text = String::with_capacity(
            self.forms
                .iter()
                .map(|form| form.len().saturating_add(2))
                .sum(),
        );
        for form in &self.forms {
            text.push_str(form);
            text.push_str("\n\n");
        }
        text
    }

    /// Apply `edit`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`FormEdit`] states, positions taken modulo the form
    ///   count; an insertion grows the list by one, a deletion shrinks a
    ///   non-empty one by one, a merge shrinks it by one when the form had a
    ///   terminator to drop and a next form to merge with, and the other edits
    ///   keep its length.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated chains of every class submit to the walk's
    ///   compositions of each edited text.
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    /// - witness: `tests::forms::a_large_module_edit_script_submits_as_the_walk_composes_it`
    #[spec(captures: before = self.forms.len(), ensures: |_| match *edit {
        FormEdit::Insert(_) | FormEdit::RefuseWhole(_) => self.forms.len() == before.saturating_add(1),
        FormEdit::Delete(_) => self.forms.len() == before.saturating_sub(1),
        FormEdit::Merge(_) => self.forms.len() == before || self.forms.len().saturating_add(1) == before,
        FormEdit::Change(_) | FormEdit::Move(..) | FormEdit::Split(_) => self.forms.len() == before,
    })]
    pub fn edit(
        &mut self,
        edit: &FormEdit,
    )
    {
        let count = self.forms.len();
        let at = |Position(position): Position| position.checked_rem(count).unwrap_or(0);
        match *edit {
            FormEdit::Change(position) => {
                if let Some(form) = self.forms.get_mut(at(position)) {
                    change(form);
                }
            },
            FormEdit::Insert(position) => {
                let fresh = self.fresh;
                self.fresh = self.fresh.saturating_add(1);
                self.forms
                    .insert(at(position), format!("def fresh{fresh} = {fresh} ;"));
            },
            FormEdit::Delete(position) => {
                if count > 0 {
                    let _deleted = self.forms.remove(at(position));
                }
            },
            FormEdit::Move(from, to) => {
                if count > 0 {
                    let form = self.forms.remove(at(from));
                    let to = to.0.checked_rem(count).unwrap_or(0).min(self.forms.len());
                    self.forms.insert(to, form);
                }
            },
            FormEdit::Merge(position) => {
                let position = at(position);
                let terminated = self
                    .forms
                    .get(position)
                    .is_some_and(|form| form.ends_with(';') || form.ends_with('}'));
                if terminated && position.saturating_add(1) < count {
                    let next = self.forms.remove(position.saturating_add(1));
                    if let Some(form) = self.forms.get_mut(position) {
                        let _terminator = form.pop();
                        form.push('\n');
                        form.push_str(&next);
                    }
                }
            },
            FormEdit::Split(position) => {
                if let Some(form) = self.forms.get_mut(at(position))
                    && let Some(equals) = form.find(" = ")
                {
                    form.insert_str(equals.saturating_add(2), " ;\n");
                }
            },
            FormEdit::RefuseWhole(position) => {
                let fresh = self.fresh;
                self.fresh = self.fresh.saturating_add(1);
                self.forms.insert(at(position), format!("pure {fresh}"));
            },
        }
    }
}

/// Change `form`'s body, keeping its name and its type: swap a returned
/// variable for the other one, bump an applied literal or a value's literal,
/// or else put one more space before it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the form differs from what it was and has as many lines.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — changed forms of every shape submit to the walk's
///   compositions.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "test fixture: the body searches and rewrites the form; the check copies it once and counts its lines"
    )
)]
#[spec(captures: before = form.clone(), ensures: |_| *form != before && form.lines().count() == before.lines().count())]
fn change(form: &mut String)
{
    if form.contains("return x }") {
        *form = form.replacen("return x }", "return y }", 1);
        return;
    }
    if form.contains("(7)") {
        *form = form.replacen("(7)", "(8)", 1);
        return;
    }
    if let Some(equals) = form.rfind(" = ")
        && let Some(rest) = form.get(equals.saturating_add(3) ..)
        && let Some(literal) = rest.strip_suffix(" ;")
        && let Ok(value) = literal.parse::<u64>()
    {
        *form = format!(
            "{} = {} ;",
            form.get(.. equals).unwrap_or_default(),
            value.saturating_add(1)
        );
        return;
    }
    form.insert(0, ' ');
}

/// A generated module of `forms` top-level forms under `root`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exactly `forms` forms, cycling through the shapes the module page
///   states; the fixture root's holes and non-exhaustive cases state their
///   refusal, the strict root's run sequences in their place.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated modules of both roots, edited, submit to the
///   walk's compositions.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
/// - witness: `tests::forms::a_large_module_edit_script_submits_as_the_walk_composes_it`
#[spec(ensures: |ret| ret.forms.len() == usize::from(forms))]
#[must_use]
pub fn module(
    forms: FormCount,
    root: SourceRoot,
) -> Module
{
    let count = usize::from(forms);
    let mut out = Vec::with_capacity(count);
    let mut index = 0_usize;
    while out.len() < count {
        let mut shape = Vec::with_capacity(2);
        let i = index;
        match index % 9 {
            0 => {
                shape.push(format!("@[ runs(\"{i}\") ]\ndef v{i} : Integer ;"));
                shape.push(format!("def v{i} = {i} ;"));
            },
            1 => shape.push(format!("def id{i}(a : Type, x : a) -> -F a {{ return x }}")),
            2 => {
                shape.push(format!("def t{i} : +U (-F Integer) ;"));
                shape.push(format!(
                    "def t{i} = thunk {{ id{}(Integer, v{}) }} ;",
                    i.saturating_sub(1),
                    i.saturating_sub(2)
                ));
            },
            3 => {
                shape.push(format!(
                    "def m{i} : (Type[+, 0] -> Type[-, 0]) -> Type[+, 0] -> Type[+, 0] -> Type[+, 0] ;"
                ));
                shape.push(format!(
                    "def m{i} = \\T. \\A. \\B. +U (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B)) ;"
                ));
            },
            4 => {
                shape.push(format!(
                    "def p{i} : +U (Integer -> Integer -> -F Integer) ;"
                ));
                shape.push(format!(
                    "def p{i} = thunk {{ fn (x) {{ fn (y) {{ return x }} }} }} ;"
                ));
            },
            5 => {
                shape.push(format!("def c{i} : +U (-F Integer) ;"));
                shape.push(format!(
                    "def c{i} = thunk {{ become ((force p{})(v{}))(7) }} ;",
                    i.saturating_sub(1),
                    i.saturating_sub(5)
                ));
            },
            6 => match root {
                SourceRoot::Strict => {
                    shape.push(format!(
                        "def u{i} : +U (Integer -> Integer -> -F Integer) ;"
                    ));
                    shape.push(format!(
                        "def u{i} = thunk {{ fn (x) {{ fn (y) {{ run p <- (force p{})(x)(y) ; return p }} }} }} ;",
                        i.saturating_sub(2)
                    ));
                },
                SourceRoot::Fixture | SourceRoot::Pending => {
                    shape.push(format!(
                        "@[ refuses(\"OutOfFragment\") ]\ndef h{i} = thunk {{ return ?seed{i} }} ;"
                    ));
                },
            },
            7 => {
                shape.push(format!(
                    "data Box{i} : Type {{\n  Empty{i} : Box{i};\n  Full{i} : (n : Integer) --> Box{i};\n}}"
                ));
                shape.push(format!(
                    "def unbox{i}(b : Box{i}) -> -F Integer {{\n  case b {{\n    Empty{i} => return 0,\n    Full{i}(n) => return n\n  }}\n}}"
                ));
            },
            _ => match root {
                SourceRoot::Strict => {
                    shape.push(format!("def w{i} : +U (Integer -> -F Integer) ;"));
                    shape.push(format!(
                        "def w{i} = thunk {{ fn (n) {{ run a <- (force p{})(n)(n) ; run b <- (force p{})(a)(n) ; return b }} }} ;",
                        i.saturating_sub(4),
                        i.saturating_sub(4)
                    ));
                },
                SourceRoot::Fixture | SourceRoot::Pending => {
                    let boxed = i.saturating_sub(1);
                    shape.push(format!(
                        "@[ refuses(\"NonExhaustiveMatch\") ]\ndef k{i}(b : Box{boxed}) -> -F Integer {{\n  case b {{\n    Empty{boxed} => return {i}\n  }}\n}}"
                    ));
                },
            },
        }
        for form in shape {
            if out.len() < count {
                out.push(form);
            }
        }
        index = index.saturating_add(1);
    }
    Module {
        forms: out,
        fresh: 0,
    }
}

/// A chain of one to `longest` edits of every class, at positions drawn
/// from the whole range.
///
/// # Specification
/// - requires: nothing.
/// - ensures: draws chains of one to `longest` edits, each class equally
///   likely.
/// - panics: none.
/// - executable: none — the result is a dormant strategy; observing its choices
///   runs generation.
///
/// # Adequacy
/// - hypothesis: L2 — the drawn chains submit to the walk's compositions; the
///   draws exercise the strategy, they do not prove its distribution.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
pub fn edits(longest: FormCount) -> impl Strategy<Value = Vec<FormEdit>>
{
    let position = || any::<usize>().prop_map(Position);
    let edit = prop_oneof![
        position().prop_map(FormEdit::Change),
        position().prop_map(FormEdit::Insert),
        position().prop_map(FormEdit::Delete),
        (position(), position()).prop_map(|(from, to)| FormEdit::Move(from, to)),
        position().prop_map(FormEdit::Merge),
        position().prop_map(FormEdit::Split),
        position().prop_map(FormEdit::RefuseWhole),
    ];
    proptest::collection::vec(edit, 1 .. usize::from(longest).max(2))
}

/// One edit of every class, each undone by the next where the class has an
/// inverse, spread across a module of `forms` forms.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a change, an insertion, a deletion, a move, a merge, a split and
///   a top-level return inserted and deleted again, at positions spread over
///   `forms`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the script submits to the walk's compositions over the
///   generated module of both roots.
/// - witness: `tests::forms::a_large_module_edit_script_submits_as_the_walk_composes_it`
#[spec(ensures: |ret| ret.len() == 8)]
#[must_use]
pub fn script(forms: FormCount) -> Vec<FormEdit>
{
    let count = usize::from(forms).max(1);
    let at = |eighths: usize| Position(count.saturating_mul(eighths).div_euclid(8));
    vec![
        FormEdit::Change(at(4)),
        FormEdit::Insert(at(1)),
        FormEdit::Delete(at(6)),
        FormEdit::Move(at(2), at(7)),
        FormEdit::Merge(at(3)),
        FormEdit::Split(at(5)),
        FormEdit::RefuseWhole(at(4)),
        FormEdit::Delete(at(4)),
    ]
}
