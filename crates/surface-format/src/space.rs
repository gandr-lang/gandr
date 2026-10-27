//! The space between two tokens on one line, decided by the tokens and the
//! forms they belong to, never by the source's spacing.
//!
//! A token reads as its text beside its [`Context`]: the part its form gives
//! it where one text plays two parts — a `(` applied to the name before it or
//! opening an operand of its own, a `.` joining a path or ending a binder, a
//! `-` subtracting or negating. [`join`] decides the space between two
//! neighbours and [`padding`] the space inside a group's brackets; the
//! crate's README states the rules they decide.

use anodized::spec;
use gandr_surface_grammar::RCtxStep;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::StepSym;
use gandr_surface_syntax::SourceFragment;

/// The rules a `(` or `[` opens an operand of its own in: a parenthesised
/// term or type, a tuple pattern, a list, an import's list of names.
const OPERANDS: [&str; 6] = [
    "parenthesized_expression",
    "parenthesized_type",
    "tuple_pattern",
    "list_expression",
    "list_pattern",
    "import_declaration",
];

/// The rules a `[` stands apart from the word before it in, as an operand's
/// does: a computation's effect row, the world a migration or a package
/// names, a theory's or a data type's bracketed parameters.
const APART: [&str; 9] = [
    "f_type.result",
    "f_type.result.labelled",
    "f_type.row",
    "f_type.row.labelled",
    "migrate_expression",
    "pack_expression",
    "package_type",
    "theory_declaration",
    "data_declaration",
];

/// The rules a `.` ends a binder or a session's message in, a body after it.
const BINDINGS: [&str; 6] = [
    "static_abstraction",
    "bind_expression",
    "theory_declaration",
    "mu_session_type",
    "send_session_type",
    "receive_session_type",
];

/// The rules whose `{` lists labelled entries hugged by their braces, written
/// against the `+` or `&` before it: a sum and a lazy record.
const TELESCOPES: [&str; 5] = [
    "labelled_sum_type",
    "labelled_sum_expression",
    "labelled_sum_pattern",
    "lazy_record_type",
    "lazy_record_expression",
];

/// What a shape face's `{` follows in a theory: its `=`, the one `{` of the
/// rule written there. The face lists the points it holds, hugged by its
/// braces: `left = {0, 2}`.
const FACE: &[RCtxStep] = &[RCtxStep {
    crossed: StepSym::Tile("="),
}];

/// The rules whose `@[` opens a block of attributes, padded by its brackets:
/// a declaration's, a module member's and a theory member's; any other `@[`
/// opens an implicit telescope, hugged by them.
const ATTRIBUTES: [&str; 3] = [
    "attribute_block",
    "attributed_module_member",
    "theory_declaration",
];

/// The rules whose `#{` opens a module signature, padded by its braces; any
/// other `#{` opens a record, hugged by them.
const SIGNATURES: [&str; 2] = ["module_declaration", "nested_module_member"];

/// The rules a `<` or `>` marks the bound or direction it touches in.
const MARKS: [&str; 4] = [
    "staged_type",
    "instantiation.direction.descent",
    "instantiation.direction.productivity",
    "instantiation.named_measure",
];

/// The keywords whose parenthesis lists binders, one space after the keyword:
/// `fn (x)`, `fork (seat : end)`, `bind (a : Name)`, `pi+ (x : A)`.
const BINDERS: [&str; 4] = ["fn", "fork", "bind", "pi+"];

/// The part a token plays where its text alone does not decide its spacing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Context
{
    /// A `(` or `[` standing apart from the word before it: one opening an
    /// operand of its own (a parenthesised term or type, a tuple pattern, a
    /// list, an import's list of names), an effect row, a migration's or a
    /// package's world, a theory's or a data type's bracketed parameters.
    Operand,
    /// An operator touching what follows it: a negation, a session's `!` or
    /// `?`, a universe's `+` or `-`, a staged bound's `<` or `>`, a lambda's
    /// `\`, a rest pattern's `..`, a splice's `~`, and the `+` or `&` of a sum
    /// or lazy record.
    Prefix,
    /// A `.` ending a binder or a session's message.
    Binding,
    /// The `{` of a sum, a lazy record or a shape's face.
    Telescope,
    /// The `@[` of an implicit telescope, set apart from a `(` after it.
    Implicit,
    /// The `#{` of a module signature.
    Signature,
    /// Any other token.
    Plain,
    /// A token a rewrite wrote, outside the source: the spacing the rewrite
    /// wrote around it stands.
    Written,
}

impl Context
{
    /// The part the token `text` plays as a tile of `rule`, written after one
    /// of the symbols `before`.
    ///
    /// # Specification
    /// trivial.
    pub fn of(
        rule: RuleName,
        text: SourceFragment<'_>,
        before: &[RCtxStep],
    ) -> Self
    {
        let rule = rule.0;
        match <&str>::from(text) {
            "(" | "[" if OPERANDS.contains(&rule) => Self::Operand,
            // A theory's dotted name, `theory Gandr.Package`, is the keyword,
            // type names and dots alone, where a binder's `.` follows a
            // rule's sides.
            "." if BINDINGS.contains(&rule)
                && !(rule == "theory_declaration"
                    && before.iter().all(|step| {
                        matches!(
                            step.crossed,
                            StepSym::Tile("theory" | "type_identifier" | ".")
                        )
                    })) =>
            {
                Self::Binding
            },
            "[" if APART.contains(&rule) => Self::Operand,
            "{" if TELESCOPES.contains(&rule) => Self::Telescope,
            "{" if rule == "theory_declaration" && before == FACE => Self::Telescope,
            "@[" if !ATTRIBUTES.contains(&rule) => Self::Implicit,
            "#{" if SIGNATURES.contains(&rule) => Self::Signature,
            "+" | "&" if TELESCOPES.contains(&rule) => Self::Prefix,
            "-" if rule == "unary_expression" || rule == "universe_type" => Self::Prefix,
            "+" if rule == "universe_type" => Self::Prefix,
            "?" if rule == "receive_session_type" => Self::Prefix,
            "<" | ">" if MARKS.contains(&rule) => Self::Prefix,
            "!" | "\\" | ".." | "~" => Self::Prefix,
            _ => Self::Plain,
        }
    }
}

/// Whether two neighbours on one line touch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Join
{
    /// They touch.
    Touch,
    /// One space stands between them.
    Space,
}

/// Whether a group's brackets hug what they hold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Padding
{
    /// They do: `(x)`, `[x]`, `#{a, b}`, `+{a : A}`, `@[r : Row]`.
    Hug,
    /// One space stands inside each: `{ x }`, `@[ checks ]`, `#{ type T }`.
    Pad,
}

impl Padding
{
    /// The space between a bracket of a group padded so and the element
    /// beside it.
    ///
    /// # Specification
    /// trivial.
    pub const fn join(self) -> Join
    {
        match self {
            Self::Hug => Join::Touch,
            Self::Pad => Join::Space,
        }
    }
}

/// The padding of the group the bracket `open` opens.
///
/// # Specification
/// trivial.
pub fn padding(open: Token<'_>) -> Padding
{
    match <&str>::from(open.text) {
        "@[" | "{" => match open.context {
            Context::Telescope | Context::Implicit | Context::Written => Padding::Hug,
            Context::Operand
            | Context::Prefix
            | Context::Binding
            | Context::Signature
            | Context::Plain => Padding::Pad,
        },
        "#{" => match open.context {
            Context::Signature => Padding::Pad,
            Context::Operand
            | Context::Prefix
            | Context::Binding
            | Context::Telescope
            | Context::Implicit
            | Context::Plain
            | Context::Written => Padding::Hug,
        },
        _ => Padding::Hug,
    }
}

/// One neighbour of a space, as [`join`] reads it.
#[derive(Clone, Copy, Debug)]
pub struct Token<'text>
{
    /// What it spells: a token, or a bracket of a group.
    pub text: SourceFragment<'text>,
    /// The part it plays; a closing bracket plays its opening one's.
    pub context: Context,
    /// What it is beside its text.
    pub kind: Kind,
}

/// What a neighbour of a space is beside its text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind
{
    /// A token of a form.
    Token,
    /// A group's opening bracket, seen from before the group.
    Open,
    /// A group's closing bracket, seen from after the group, and the
    /// group's padding.
    Close(Padding),
    /// Material laid down as written: a string, a shell block, a hole.
    Material,
    /// A comment.
    Comment,
}

/// Whether `text` reads as a word: a name, a keyword or a literal.
///
/// # Specification
/// trivial.
fn word(text: SourceFragment<'_>) -> Wordlike
{
    let text = <&str>::from(text);
    let named = text
        .chars()
        .next()
        .is_some_and(|first| first.is_alphanumeric() || first == '_' || first == '\'');
    if named || matches!(text, "+U" | "-F" | "pi+" | "Type+") {
        Wordlike::Yes
    }
    else {
        Wordlike::No
    }
}

/// Whether a token reads as a word.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Wordlike
{
    /// It does.
    Yes,
    /// It does not.
    No,
}

/// Whether `left` ends an operand a bracket or a `.` after it applies to: a
/// word, material, or the closer of a hugging group other than an implicit
/// telescope.
///
/// # Specification
/// trivial.
fn applied(left: Token<'_>) -> Wordlike
{
    match left.kind {
        Kind::Material => Wordlike::Yes,
        Kind::Close(Padding::Hug) => match left.context {
            Context::Implicit => Wordlike::No,
            Context::Operand
            | Context::Prefix
            | Context::Binding
            | Context::Telescope
            | Context::Signature
            | Context::Plain
            | Context::Written => Wordlike::Yes,
        },
        Kind::Token => word(left.text),
        Kind::Open | Kind::Close(Padding::Pad) | Kind::Comment => Wordlike::No,
    }
}

/// The space between `left` and `right`, neighbours on one line, neither a
/// bracket of a group the other stands just inside.
///
/// # Specification
/// - requires: `left` stands directly before `right` on one line, and neither
///   is the bracket of a group the other is the first or last element of.
/// - ensures: a `,` or `;` touches what stands before it and is followed by one
///   space; a comment has one space on either side; a `.` touches the word or
///   bracket before it, and the word after it unless it ends a binder; a prefix
///   operator touches what follows it; a `(` or `[` touches the word or hugging
///   bracket before it, unless it opens an operand or the binders of `fn`,
///   `fork`, `bind` or `pi+`; any other two are one space apart.
/// - provides: the space [`crate::layout`] writes between two elements of a
///   line.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the spacing golden fixes each rule at a source spaced
///   against it, and the corpus sweep formats every source once and again
///   unchanged.
/// - witness: `tests::format::the_printer_decides_every_inner_space`
/// - witness: `tests::format::a_terminator_touches_the_form_it_ends`
/// - witness: `tests::format::sweeps::every_source_keeps_its_meaning_and_formats_once`
#[spec(ensures: |ret| right.kind != Kind::Token
    || !matches!(<&str>::from(right.text), "," | ";")
    || ret == Join::Touch)]
pub fn join(
    left: Token<'_>,
    right: Token<'_>,
) -> Join
{
    let right_text = <&str>::from(right.text);
    let left_text = <&str>::from(left.text);
    if right.kind == Kind::Token && matches!(right_text, "," | ";") {
        return Join::Touch;
    }
    if left.kind == Kind::Token && matches!(left_text, "," | ";") {
        return Join::Space;
    }
    if left.kind == Kind::Comment || right.kind == Kind::Comment {
        return Join::Space;
    }
    if right.kind == Kind::Token && right_text == "." && applied(left) == Wordlike::Yes {
        return Join::Touch;
    }
    if left.kind == Kind::Token && left_text == "." {
        return match left.context {
            Context::Binding => Join::Space,
            Context::Operand
            | Context::Prefix
            | Context::Telescope
            | Context::Implicit
            | Context::Signature
            | Context::Plain
            | Context::Written => Join::Touch,
        };
    }
    if left.kind == Kind::Token && left.context == Context::Prefix {
        return Join::Touch;
    }
    if right.kind == Kind::Open
        && matches!(right_text, "(" | "[")
        && right.context != Context::Operand
        && applied(left) == Wordlike::Yes
        && !(left.kind == Kind::Token && BINDERS.contains(&left_text))
    {
        return Join::Touch;
    }
    Join::Space
}
