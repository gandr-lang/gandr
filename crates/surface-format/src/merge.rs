//! A signature and the definition after it written as one function form:
//! `def f : () => B ; def f = thunk { c } ;` and `def f() -> -F B { c }`,
//! which lower to the same thunk at the same type.
//!
//! The merge reads two top-level forms, so it is not a respelling of one form
//! as the other rewrites are: [`crate::format_beside`] offers each signature
//! and the definition laid out after it, both respelled, to [`merged`], and
//! lays out the one form it returns in their place. The meaning check pairs
//! declarations by name, which the merge keeps; a declaration whose merged
//! form lowers or elaborates otherwise is laid out apart again, unreported
//! ([`Apart`]).

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;

use crate::leaf::Documentation;
use crate::leaf::Leaf;
use crate::leaf::Material;

/// The tokens that open a bracketed group.
const OPENERS: [&str; 7] = ["(", "[", "{", "#{", "&{", "+{", "@["];

/// The tokens that close one.
const CLOSERS: [&str; 3] = [")", "]", "}"];

/// How a signature and the definition after it are laid out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pairing
{
    /// As one function form.
    Merged,
    /// Each as the source writes it.
    Apart,
}

/// The top-level forms the merge leaves apart: the signature and definition
/// of each declaration whose merged form lowered or elaborated otherwise.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Apart(Vec<ByteSpan>);

impl Apart
{
    /// How the form at `span` is laid out: [`Pairing::Apart`] when it is
    /// left apart.
    ///
    /// # Specification
    /// trivial.
    pub fn pairing(
        &self,
        span: ByteSpan,
    ) -> Pairing
    {
        if self.0.binary_search(&span).is_ok() {
            Pairing::Apart
        }
        else {
            Pairing::Merged
        }
    }

    /// Leave the forms at `forms` apart.
    ///
    /// # Specification
    /// trivial.
    pub fn keep(
        &mut self,
        forms: &[ByteSpan],
    )
    {
        self.0.extend_from_slice(forms);
        self.0.sort_unstable();
        self.0.dedup();
    }
}

/// Whether the top-level form whose leaves are `written` opens as a
/// definition the merge reads, `def f = thunk {`: the check before its
/// signature and it are respelled together. [`Pairing::Merged`] when it does.
///
/// # Specification
/// trivial.
pub fn candidate(written: &[Leaf<'_>]) -> Pairing
{
    let mut texts = written
        .iter()
        .filter(|leaf| leaf.material != Material::Whitespace)
        .map(|leaf| <&str>::from(leaf.text));
    if matches!(
        (
            texts.next(),
            texts.next(),
            texts.next(),
            texts.next(),
            texts.next()
        ),
        (Some("def"), Some(_), Some("="), Some("thunk"), Some("{"))
    ) {
        Pairing::Merged
    }
    else {
        Pairing::Apart
    }
}

/// The signature whose respelled leaves are `signature` and the definition
/// after it, whose leaves are `written` as the source writes them and
/// `definition` respelled, merged into one function form: the signature's
/// leaves to its name, `()`, `->`, the returner its type suspends, then the
/// definition's body in braces — what the thunk the source writes holds, or
/// the computation the respelling left the checker to wrap.
///
/// # Specification
/// - requires: each slice is one top-level form's leaves, in offset order.
/// - ensures: `None` unless the signature is `def f : () => B ;` or `def f : +U
///   (-F B) ;` behind any attributes and documentation, the definition is
///   written `def f = thunk { … } ;` under the same name, its thunk ungraded,
///   and neither holds a comment after its documentation; otherwise the
///   signature's leaves to the name, then `() -> -F B` with `B` parenthesised
///   unless it is one token, one bracketed group or a name applied to one, then
///   the body in braces.
/// - provides: the leaves [`crate::format_beside`] lays out for the two forms.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over each form's leaves.
///
/// # Adequacy
/// - hypothesis: L3 — a `become` thunk and a statement block merge in both
///   forms, a thunk the respelling left out merges as its computation, and a
///   graded thunk, a commented definition and a value definition stay apart.
/// - witness: `tests::rewrite::a_signed_thunk_merges_into_its_function_form_1449`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|leaves| !leaves.is_empty()))]
#[must_use]
pub fn merged<'source>(
    signature: &[Leaf<'source>],
    (written, definition): (&[Leaf<'source>], &[Leaf<'source>]),
) -> Option<Vec<Leaf<'source>>>
{
    let head = signature
        .iter()
        .position(|leaf| leaf.material == Material::Token && <&str>::from(leaf.text) == "def")?;
    let declared = signature.get(head ..)?;
    if [declared, written, definition]
        .into_iter()
        .any(|leaves| commented(leaves) == Commentary::Commented)
    {
        return None;
    }
    let signed = tokens(declared);
    let &[
        Token(_, "def"),
        Token(LeafIndex(named), name),
        Token(_, ":"),
        ref ty @ ..,
        Token(LeafIndex(ended), ";"),
    ] = signed.as_slice()
    else {
        return None;
    };
    let codomain = match *ty {
        [
            Token(_, "("),
            Token(_, ")"),
            Token(LeafIndex(arrow), "=>"),
            ref result @ ..,
        ]
        | [
            Token(_, "()"),
            Token(LeafIndex(arrow), "=>"),
            ref result @ ..,
        ] if result.first().is_some_and(|&Token(_, first)| first != "[") => {
            let leaves = trimmed(declared.get(arrow.saturating_add(1) .. ended)?);
            Codomain::Result(leaves, atomic(result))
        },
        [
            Token(_, "+U"),
            Token(open, "("),
            Token(_, "-F"),
            ref returned @ ..,
            Token(close, ")"),
        ] if closing(&signed, open) == Some(close) && atomic(rowless(returned)) == Atomic::Yes => {
            Codomain::Returner(trimmed(declared.get(open.0.saturating_add(1) .. close.0)?))
        },
        _ => return None,
    };
    let source = tokens(written);
    let &[
        Token(_, "def"),
        Token(_, own),
        Token(_, "="),
        Token(_, "thunk"),
        Token(open, "{"),
        ..,
        Token(close, "}"),
        Token(_, ";"),
    ] = source.as_slice()
    else {
        return None;
    };
    if own != name || closing(&source, open) != Some(close) {
        return None;
    }
    let defined = tokens(definition);
    let &[
        Token(_, "def"),
        Token(_, respelled),
        Token(LeafIndex(equals), "="),
        ref rest @ ..,
        Token(LeafIndex(ends), ";"),
    ] = defined.as_slice()
    else {
        return None;
    };
    if respelled != name {
        return None;
    }
    let body = match *rest {
        [Token(_, "thunk"), Token(open, "{"), .., Token(close, "}")]
            if closing(&defined, open) == Some(close) =>
        {
            definition.get(open.0.saturating_add(1) .. close.0)?
        },
        _ => definition.get(equals.saturating_add(1) .. ends)?,
    };
    let first = signature.first()?;
    let position = ByteSpan::new(first.span.start(), first.span.start()).unwrap_or(first.span);
    let made = |text: &'static str, material: Material| Leaf {
        span: position,
        text: SourceFragment::from(text),
        material,
        owner: first.owner,
        documentation: Documentation::Outside,
    };
    let mut out: Vec<Leaf<'source>> = Vec::with_capacity(
        signature
            .len()
            .saturating_add(definition.len())
            .saturating_add(12_usize),
    );
    out.extend_from_slice(signature.get(..= head.saturating_add(named))?);
    out.extend([
        made("(", Material::Token),
        made(")", Material::Token),
        made(" ", Material::Whitespace),
        made("->", Material::Token),
        made(" ", Material::Whitespace),
    ]);
    match codomain {
        Codomain::Result(result, Atomic::Yes) => {
            out.extend([made("-F", Material::Token), made(" ", Material::Whitespace)]);
            out.extend_from_slice(result);
        },
        Codomain::Result(result, Atomic::No) => {
            out.extend([
                made("-F", Material::Token),
                made(" ", Material::Whitespace),
                made("(", Material::Token),
            ]);
            out.extend_from_slice(result);
            out.push(made(")", Material::Token));
        },
        Codomain::Returner(returner) => out.extend_from_slice(returner),
    }
    out.extend([
        made(" ", Material::Whitespace),
        made("{", Material::Token),
        made(" ", Material::Whitespace),
    ]);
    out.extend_from_slice(trimmed(body));
    out.extend([made(" ", Material::Whitespace), made("}", Material::Token)]);
    for leaf in &mut out {
        leaf.owner = first.owner;
    }
    Some(out)
}

/// The returner a signature's type suspends.
enum Codomain<'leaves, 'source>
{
    /// The result `B` of `() => B`, and whether it stands bare after `-F`.
    Result(&'leaves [Leaf<'source>], Atomic),
    /// The `-F B` of `+U (-F B)`.
    Returner(&'leaves [Leaf<'source>]),
}

/// Whether a type stands bare after `-F`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Atomic
{
    /// It does: one token, one bracketed group, or a name applied to one.
    Yes,
    /// It is parenthesised.
    No,
}

/// Whether a form's leaves hold a comment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Commentary
{
    /// They hold one.
    Commented,
    /// They hold none.
    Clean,
}

/// The index of a leaf among a form's leaves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LeafIndex(usize);

/// A leaf of a form other than whitespace: its index and its text.
#[derive(Clone, Copy, Debug)]
struct Token<'text>(LeafIndex, &'text str);

/// Whether `leaves` hold a comment.
///
/// # Specification
/// trivial.
fn commented(leaves: &[Leaf<'_>]) -> Commentary
{
    if leaves.iter().any(|leaf| {
        matches!(
            leaf.material,
            Material::LineComment | Material::BlockComment
        )
    }) {
        Commentary::Commented
    }
    else {
        Commentary::Clean
    }
}

/// The leaves of `leaves` other than whitespace, each beside its index.
///
/// # Specification
/// trivial.
fn tokens<'leaves>(leaves: &'leaves [Leaf<'_>]) -> Vec<Token<'leaves>>
{
    leaves
        .iter()
        .enumerate()
        .filter(|&(_, leaf)| leaf.material != Material::Whitespace)
        .map(|(index, leaf)| Token(LeafIndex(index), <&str>::from(leaf.text)))
        .collect()
}

/// `leaves` without the whitespace at either end.
///
/// # Specification
/// trivial.
fn trimmed<'leaves, 'source>(leaves: &'leaves [Leaf<'source>]) -> &'leaves [Leaf<'source>]
{
    let start = leaves
        .iter()
        .position(|leaf| leaf.material != Material::Whitespace)
        .unwrap_or(leaves.len());
    let end = leaves
        .iter()
        .rposition(|leaf| leaf.material != Material::Whitespace)
        .map_or(start, |last| last.saturating_add(1));
    leaves.get(start .. end.max(start)).unwrap_or_default()
}

/// The leaf index of the token closing the group the token at leaf index
/// `open` of `tokens` opens.
///
/// # Specification
/// trivial.
fn closing(
    tokens: &[Token<'_>],
    open: LeafIndex,
) -> Option<LeafIndex>
{
    let from = tokens.iter().position(|&Token(index, _)| index == open)?;
    let mut depth = 0_usize;
    for &Token(index, text) in tokens.get(from ..)? {
        if OPENERS.contains(&text) {
            depth = depth.saturating_add(1);
        }
        else if CLOSERS.contains(&text) {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

/// The tokens of what a returner returns, `tokens` after its `-F`, without
/// the effect row `[…]` that may open them.
///
/// # Specification
/// trivial.
fn rowless<'tokens, 'text>(tokens: &'tokens [Token<'text>]) -> &'tokens [Token<'text>]
{
    let Some(&Token(open, "[")) = tokens.first()
    else {
        return tokens;
    };
    closing(tokens, open)
        .and_then(|close| tokens.iter().position(|&Token(index, _)| index == close))
        .and_then(|at| tokens.get(at.saturating_add(1) ..))
        .unwrap_or(tokens)
}

/// Whether the type whose tokens are `tokens` stands bare after `-F`: one
/// token, one bracketed group, or a name and one group after it.
///
/// # Specification
/// trivial.
fn atomic(tokens: &[Token<'_>]) -> Atomic
{
    let mut chunks: Vec<&str> = Vec::new();
    let mut depth = 0_usize;
    for &Token(_, text) in tokens {
        if depth == 0 {
            chunks.push(text);
        }
        if OPENERS.contains(&text) {
            depth = depth.saturating_add(1);
        }
        else if CLOSERS.contains(&text) {
            depth = depth.saturating_sub(1);
        }
    }
    let named = |text: &str| {
        text.chars()
            .next()
            .is_some_and(|first| first.is_alphabetic() || first == '_')
    };
    let atomic = match *chunks.as_slice() {
        [_] => true,
        [name, group] => named(name) && (group == "(" || group == "["),
        _ => false,
    };
    if atomic { Atomic::Yes } else { Atomic::No }
}
