//! A signature and the definition after it written as one form.
//!
//! The function form: `def f : () => B ; def f = thunk { c } ;` and `def
//! f() -> -F B { c }`, which lower to the same thunk at the same type, and
//! `def f : A => B ; def f = thunk { fn (x) { c } } ;` or `def f = fn (x) {
//! c } ;` and `def f(x : A) -> -F B { c }`, the lambda's binders the
//! function form's parameters.
//!
//! The joined form, for every other pair: `def x : T ; def x = e ;` and `def
//! x : T = e ;`, the definition directly after the signature with nothing
//! but whitespace between them.
//!
//! Either reads two top-level forms, so it is not a respelling of one form
//! as the other rewrites are: [`crate::format_beside`] offers each signature
//! and the definition laid out after it, both respelled, to [`merged`] and
//! then [`joined`], and lays out the one form returned in their place. The
//! meaning check pairs declarations by name, which both keep; a declaration
//! whose one form lowers or elaborates otherwise is laid out apart again,
//! unreported ([`Apart`]).

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;

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

/// The one form a signature and the definition after it are written as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OneForm
{
    /// The function form, `def f(x : A) -> -F B { c }`.
    Function,
    /// The joined form, `def x : T = e ;`.
    Joined,
}

/// What a formatting does with a signature beside its definition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Joining
{
    /// Joins a pair directly adjacent into one form.
    Join,
    /// Splits a joined definition into its signature and definition.
    Split,
    /// Leaves each as the source writes it.
    Keep,
}

/// The top-level forms the merge leaves apart: the signature and definition
/// of each declaration whose one form lowered or elaborated otherwise, by
/// the one form. A pair held from the function form may still join.
#[derive(Clone, Debug, Default)]
pub struct Apart
{
    /// The forms held from the function form, ascending.
    function: Vec<ByteSpan>,
    /// The forms held from the joined form, ascending.
    joined: Vec<ByteSpan>,
}

impl Apart
{
    /// How the form at `span` is laid out as `one`: [`Pairing::Apart`] when
    /// it is held from it.
    ///
    /// # Specification
    /// trivial.
    pub fn pairing(
        &self,
        span: ByteSpan,
        one: OneForm,
    ) -> Pairing
    {
        let held = match one {
            OneForm::Function => &self.function,
            OneForm::Joined => &self.joined,
        };
        if held.binary_search(&span).is_ok() {
            Pairing::Apart
        }
        else {
            Pairing::Merged
        }
    }

    /// Hold the forms at `forms` from `one`.
    ///
    /// # Specification
    /// trivial.
    pub fn keep(
        &mut self,
        forms: &[ByteSpan],
        one: OneForm,
    )
    {
        let held = match one {
            OneForm::Function => &mut self.function,
            OneForm::Joined => &mut self.joined,
        };
        held.extend_from_slice(forms);
        held.sort_unstable();
        held.dedup();
    }
}

/// Whether the top-level form whose leaves are `written` opens as a
/// definition the function form reads, `def f = thunk {` or `def f = fn`: the
/// check before its signature and it are respelled together.
/// [`Pairing::Merged`] when it does.
///
/// # Specification
/// trivial.
pub fn candidate(written: &[Leaf<'_>]) -> Pairing
{
    let mut texts = written
        .iter()
        .filter(|leaf| leaf.material != Material::Whitespace)
        .map(|leaf| <&str>::from(leaf.text));
    match (
        texts.next(),
        texts.next(),
        texts.next(),
        texts.next(),
        texts.next(),
    ) {
        (Some("def"), Some(_), Some("="), Some("thunk"), Some("{"))
        | (Some("def"), Some(_), Some("="), Some("fn"), _) => Pairing::Merged,
        _ => Pairing::Apart,
    }
}

/// The span of the `=` the top-level form `form` of `tree` writes among its
/// own tiles, a definition's or a joined definition's; none for a signature
/// alone.
///
/// # Specification
/// trivial.
pub fn defines(
    tree: &SyntaxTree<'_>,
    form: NodeIndex,
) -> Option<ByteSpan>
{
    tree.children(form).find_map(|child| {
        let node = tree.node(child)?;
        (matches!(node.label(), NodeLabel::Tile(_))
            && tree
                .fragment(child)
                .is_some_and(|text| <&str>::from(text) == "="))
        .then(|| node.span())
    })
}

/// The joined definition whose respelled leaves are `joined`, its own `=`
/// standing at `equals`, written apart: the signature, then the definition.
///
/// # Specification
/// - requires: `joined` is one top-level form's leaves, in offset order.
/// - ensures: `None` unless the form is `def x : T = e ;` behind any attributes
///   and documentation, its `=` at `equals` and no comment before it; otherwise
///   the leaves to the last of `T` and ` ;`, beside `def x = ` and the leaves
///   after the `=`, its `;` included.
/// - provides: the leaves [`crate::format_beside`] lays out for the two forms.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over the form's leaves.
///
/// # Adequacy
/// - hypothesis: L3 — a joined definition, documented or not, splits into the
///   pair it joins.
/// - witness: `tests::rewrite::an_adjacent_pair_joins_into_one_definition_2228`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(ref signed, ref defined)| !signed.is_empty() && !defined.is_empty()))]
#[must_use]
pub fn separated<'source>(
    joined: &[Leaf<'source>],
    equals: ByteSpan,
) -> Option<(Vec<Leaf<'source>>, Vec<Leaf<'source>>)>
{
    let head = joined
        .iter()
        .position(|leaf| leaf.material == Material::Token && <&str>::from(leaf.text) == "def")?;
    let at = joined.iter().position(|leaf| {
        leaf.material == Material::Token && leaf.span == equals && <&str>::from(leaf.text) == "="
    })?;
    let declared = joined.get(head .. at)?;
    if commented(declared) == Commentary::Commented {
        return None;
    }
    let &[
        Token(_, "def"),
        Token(LeafIndex(named), _),
        Token(_, ":"),
        ..,
        Token(LeafIndex(last), _),
    ] = tokens(declared).as_slice()
    else {
        return None;
    };
    let first = joined.first()?;
    let name = *declared.get(named)?;
    let made = |text: &'static str, material: Material| Leaf {
        span: ByteSpan::new(name.span.start(), name.span.start()).unwrap_or(name.span),
        text: SourceFragment::from(text),
        material,
        owner: first.owner,
        documentation: Documentation::Outside,
    };
    let mut signed: Vec<Leaf<'source>> =
        Vec::with_capacity(head.saturating_add(last).saturating_add(3));
    signed.extend_from_slice(joined.get(..= head.saturating_add(last))?);
    signed.extend([made(" ", Material::Whitespace), made(";", Material::Token)]);
    let mut defined: Vec<Leaf<'source>> =
        Vec::with_capacity(joined.len().saturating_sub(at).saturating_add(5));
    defined.extend([
        made("def", Material::Token),
        made(" ", Material::Whitespace),
        name,
    ]);
    defined.extend([made(" ", Material::Whitespace), made("=", Material::Token)]);
    defined.extend_from_slice(joined.get(at.saturating_add(1) ..)?);
    Some((signed, defined))
}

/// The signature whose respelled leaves are `signature` and the definition
/// directly after it, whose leaves are `written` as the source writes them
/// and `definition` respelled, joined into one form: the signature's leaves
/// to its type, then `=`, then the definition's from its value on.
///
/// # Specification
/// - requires: each slice is one top-level form's leaves, in offset order, and
///   the signature holds no definition already.
/// - ensures: `None` unless the signature is `def x : T ;` behind any
///   attributes and documentation, holding no comment, and the definition is
///   `def x = e ;` under the same name with nothing written before its `def`
///   and no comment before its value or after its `;`; otherwise the
///   signature's leaves to the last of `T`, then ` = `, then the definition's
///   leaves after its `=`, its `;` included.
/// - provides: the leaves [`crate::format_beside`] lays out for the two forms.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over each form's leaves.
///
/// # Adequacy
/// - hypothesis: L3 — an adjacent pair joins, a comment inside the value kept;
///   a pair a comment parts, a definition under an attribute or its own
///   documentation, a commented signature and a pair under two names stay
///   apart.
/// - witness: `tests::rewrite::an_adjacent_pair_joins_into_one_definition_2228`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|leaves| !leaves.is_empty()))]
#[must_use]
pub fn joined<'leaves, 'source>(
    signature: &'leaves [Leaf<'source>],
    (written, definition): (&'leaves [Leaf<'source>], &'leaves [Leaf<'source>]),
) -> Option<Vec<Leaf<'source>>>
{
    let head = signature
        .iter()
        .position(|leaf| leaf.material == Material::Token && <&str>::from(leaf.text) == "def")?;
    let declared = signature.get(head ..)?;
    if commented(declared) == Commentary::Commented
        || written
            .iter()
            .find(|leaf| leaf.material != Material::Whitespace)
            .is_none_or(|leaf| leaf.material != Material::Token || <&str>::from(leaf.text) != "def")
    {
        return None;
    }
    let signed = tokens(declared);
    let &[
        Token(_, "def"),
        Token(_, name),
        Token(_, ":"),
        ..,
        Token(LeafIndex(last), _),
        Token(_, ";"),
    ] = signed.as_slice()
    else {
        return None;
    };
    let defined = tokens(definition);
    let &[
        Token(_, "def"),
        Token(_, own),
        Token(LeafIndex(equals), "="),
        _,
        ..,
        Token(_, ";"),
    ] = defined.as_slice()
    else {
        return None;
    };
    if own != name || commented(definition.get(.. equals)?) == Commentary::Commented {
        return None;
    }
    let first = signature.first()?;
    let position = ByteSpan::new(first.span.start(), first.span.start()).unwrap_or(first.span);
    let made = |text: &'static str, material: Material| Leaf {
        span: position,
        text: SourceFragment::from(text),
        material,
        owner: first.owner,
        documentation: Documentation::Outside,
    };
    let mut out: Vec<Leaf<'source>> =
        Vec::with_capacity(signature.len().saturating_add(definition.len()));
    out.extend_from_slice(signature.get(..= head.saturating_add(last))?);
    out.extend([made(" ", Material::Whitespace), made("=", Material::Token)]);
    out.extend_from_slice(definition.get(equals.saturating_add(1) ..)?);
    for leaf in &mut out {
        leaf.owner = first.owner;
    }
    Some(out)
}

/// The signature whose respelled leaves are `signature` and the definition
/// after it, whose leaves are `written` as the source writes them and
/// `definition` respelled, merged into one function form: the signature's
/// leaves to its name, the parameters, `->`, the returner its type
/// suspends, then the definition's body in braces — what the thunk the
/// source writes holds, or the computation the respelling left the checker
/// to wrap, under one lambda binder per parameter.
///
/// # Specification
/// - requires: each slice is one top-level form's leaves, in offset order.
/// - ensures: `None` unless the signature is `def f : T ;` behind any
///   attributes and documentation, `T` one of `() => B`, `+U (-F B)`, `D => B`
///   with `D` one domain or a parenthesised list of them, or `+U (D1 -> … -> Dn
///   -> -F B)`, the definition is written `def f = thunk { … } ;` under the
///   same name, its thunk ungraded, or `def f = fn …` when `T` has a domain,
///   holding one `fn (x) { … }` per domain each directly in the last, every
///   binder bare and the name a dependent domain `(x : A)` gives it, and
///   neither form holds a comment after its documentation; otherwise the
///   signature's leaves to the name, then each binder `x : A` in parentheses,
///   `A` its domain, then `-> -F B` with `B` parenthesised unless it is one
///   token, one bracketed group or a name applied to one, then the innermost
///   body in braces.
/// - provides: the leaves [`crate::format_beside`] lays out for the two forms.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over each form's leaves.
///
/// # Adequacy
/// - hypothesis: L3 — a `become` thunk and a statement block merge in both
///   forms, a thunk the respelling left out merges as its computation, a one-
///   and a two-binder lambda merge, thunked or not, and a graded thunk, a
///   commented definition, a value definition, a lambda short of the arrows, an
///   annotated binder and a binder a dependent domain names otherwise stay
///   apart.
/// - witness: `tests::rewrite::a_signed_thunk_merges_into_its_function_form_1449`
/// - witness: `tests::rewrite::a_signed_lambda_merges_into_its_function_form_1899`
/// - witness: `tests::rewrite::a_lambda_the_checker_thunks_merges_into_its_function_form_2228`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|leaves| !leaves.is_empty()))]
#[must_use]
pub fn merged<'leaves, 'source>(
    signature: &'leaves [Leaf<'source>],
    (written, definition): (&'leaves [Leaf<'source>], &'leaves [Leaf<'source>]),
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
        Token(_, ";"),
    ] = signed.as_slice()
    else {
        return None;
    };
    let (domains, codomain) = abstracted(declared, ty)?;
    let source = tokens(written);
    let own = match *source.as_slice() {
        [
            Token(_, "def"),
            Token(_, own),
            Token(_, "="),
            Token(_, "thunk"),
            Token(open, "{"),
            ..,
            Token(close, "}"),
            Token(_, ";"),
        ] if closing(&source, open) == Some(close) => own,
        [
            Token(_, "def"),
            Token(_, own),
            Token(_, "="),
            Token(_, "fn"),
            ..,
            Token(_, ";"),
        ] if !domains.is_empty() => own,
        _ => return None,
    };
    if own != name {
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
    let (parameters, inside) = applied(body, &domains)?;
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
    out.push(made("(", Material::Token));
    for (index, &(binder, ty)) in parameters.iter().enumerate() {
        if index > 0_usize {
            out.extend([made(",", Material::Token), made(" ", Material::Whitespace)]);
        }
        out.extend_from_slice(binder);
        out.extend([
            made(" ", Material::Whitespace),
            made(":", Material::Token),
            made(" ", Material::Whitespace),
        ]);
        out.extend_from_slice(ty);
    }
    out.extend([
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
    out.extend_from_slice(inside);
    out.extend([made(" ", Material::Whitespace), made("}", Material::Token)]);
    for leaf in &mut out {
        leaf.owner = first.owner;
    }
    Some(out)
}

/// One domain a signature's type abstracts: the name a dependent domain
/// `(x : A)` gives its binder, and the leaves of its type.
#[derive(Clone, Copy, Debug)]
struct Domain<'leaves, 'source>
{
    /// The binder's name, when the domain is dependent.
    named: Option<&'leaves str>,
    /// The domain's type.
    ty: &'leaves [Leaf<'source>],
}

/// The domains and the returner of the type whose tokens are `ty`, among the
/// leaves `declared`, when it is a function form's: `() => B`, `+U (-F B)`,
/// `D => B` or `+U (D1 -> … -> Dn -> -F B)`.
///
/// # Specification
/// trivial.
fn abstracted<'leaves, 'source>(
    declared: &'leaves [Leaf<'source>],
    ty: &[Token<'leaves>],
) -> Option<(Vec<Domain<'leaves, 'source>>, Codomain<'leaves, 'source>)>
{
    if let [
        Token(_, "+U"),
        Token(open, "("),
        ref inner @ ..,
        Token(close, ")"),
    ] = *ty
    {
        if closing(ty, open) != Some(close) {
            return None;
        }
        let segments = split(inner, Separator::Arrow);
        let (&last, domains) = segments.split_last()?;
        let [Token(_, "-F"), ref returned @ ..] = *last
        else {
            return None;
        };
        if atomic(rowless(returned)) == Atomic::No {
            return None;
        }
        let domains = domains
            .iter()
            .map(|&segment| domain(declared, segment))
            .collect::<Option<Vec<_>>>()?;
        return Some((domains, Codomain::Returner(spanned(declared, last)?)));
    }
    let pieces = split(ty, Separator::Function);
    let &[given, result] = pieces.as_slice()
    else {
        return None;
    };
    if result.first().is_none_or(|&Token(_, first)| first == "[") {
        return None;
    }
    let domains = match *given {
        [Token(_, "()")] => Vec::new(),
        [Token(open, "("), ref listed @ .., Token(close, ")")]
            if closing(given, open) == Some(close) =>
        {
            split(listed, Separator::Comma)
                .into_iter()
                .filter(|piece| !piece.is_empty())
                .map(|piece| domain(declared, piece))
                .collect::<Option<Vec<_>>>()?
        },
        _ => Vec::from([domain(declared, given)?]),
    };
    Some((
        domains,
        Codomain::Result(spanned(declared, result)?, atomic(result)),
    ))
}

/// The domain whose tokens are `tokens`, among the leaves `declared`: `x :
/// A`, in parentheses or not, names its binder.
///
/// # Specification
/// trivial.
fn domain<'leaves, 'source>(
    declared: &'leaves [Leaf<'source>],
    tokens: &[Token<'leaves>],
) -> Option<Domain<'leaves, 'source>>
{
    let bare = match *tokens {
        [Token(open, "("), ref inner @ .., Token(close, ")")]
            if closing(tokens, open) == Some(close) =>
        {
            inner
        },
        _ => tokens,
    };
    if let [named @ Token(_, name), Token(_, ":"), ref ty @ ..] = *bare
        && identifier(named) == Identifier::Yes
    {
        return Some(Domain {
            named: Some(name),
            ty: spanned(declared, ty)?,
        });
    }
    Some(Domain {
        named: None,
        ty: spanned(declared, tokens)?,
    })
}

/// One binder a lambda abstracts and the type the function form writes it
/// at.
type Parameter<'leaves, 'source> = (&'leaves [Leaf<'source>], &'leaves [Leaf<'source>]);

/// The function form's parameters and its body, when `body`, the leaves of
/// a thunk's computation, is one `fn (x) { … }` per domain of `domains`,
/// each directly in the last and each binder bare: each binder beside its
/// domain, and the innermost lambda's body. An annotated binder, `fn (x :
/// A)`, lowers with its annotation, which the function form does not write.
///
/// # Specification
/// trivial.
fn applied<'leaves, 'source>(
    body: &'leaves [Leaf<'source>],
    domains: &[Domain<'leaves, 'source>],
) -> Option<(Vec<Parameter<'leaves, 'source>>, &'leaves [Leaf<'source>])>
{
    if domains.is_empty() {
        return Some((Vec::new(), trimmed(body)));
    }
    let all = tokens(body);
    let mut rest = all.as_slice();
    let mut parameters = Vec::with_capacity(domains.len());
    for &Domain { named, ty } in domains {
        let [Token(_, "fn"), ref lambda @ ..] = *rest
        else {
            return None;
        };
        let (binders, block) = matched(lambda)?;
        let &[binder @ Token(_, name)] = binders
        else {
            return None;
        };
        if identifier(binder) == Identifier::No || named.is_some_and(|named| named != name) {
            return None;
        }
        let (inside, after) = matched(block)?;
        if !after.is_empty() || block.first().is_none_or(|&Token(_, open)| open != "{") {
            return None;
        }
        parameters.push((spanned(body, &[binder])?, ty));
        rest = inside;
    }
    Some((parameters, spanned(body, rest)?))
}

/// What a token list is split at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Separator
{
    /// A computation arrow, `->`.
    Arrow,
    /// A value function's arrow, `=>`.
    Function,
    /// A comma.
    Comma,
}

impl Separator
{
    /// The separator `token` is, if any.
    ///
    /// # Specification
    /// trivial.
    fn of(Token(_, text): Token<'_>) -> Option<Self>
    {
        match text {
            "->" => Some(Self::Arrow),
            "=>" => Some(Self::Function),
            "," => Some(Self::Comma),
            _ => None,
        }
    }
}

/// `tokens` split at each `separator` outside every bracketed group.
///
/// # Specification
/// trivial.
fn split<'tokens, 'text>(
    tokens: &'tokens [Token<'text>],
    separator: Separator,
) -> Vec<&'tokens [Token<'text>]>
{
    let mut pieces = Vec::new();
    let mut depth = 0_usize;
    let mut start = 0_usize;
    for (at, &token) in tokens.iter().enumerate() {
        let Token(_, text) = token;
        if OPENERS.contains(&text) {
            depth = depth.saturating_add(1);
        }
        else if CLOSERS.contains(&text) {
            depth = depth.saturating_sub(1);
        }
        else if depth == 0 && Separator::of(token) == Some(separator) {
            pieces.push(tokens.get(start .. at).unwrap_or_default());
            start = at.saturating_add(1);
        }
    }
    pieces.push(tokens.get(start ..).unwrap_or_default());
    pieces
}

/// The tokens inside the group the first of `tokens` opens, and those after
/// the token closing it.
///
/// # Specification
/// trivial.
fn matched<'tokens, 'text>(
    tokens: &'tokens [Token<'text>]
) -> Option<(&'tokens [Token<'text>], &'tokens [Token<'text>])>
{
    let mut depth = 0_usize;
    for (at, &Token(_, text)) in tokens.iter().enumerate() {
        if OPENERS.contains(&text) {
            depth = depth.saturating_add(1);
        }
        else if CLOSERS.contains(&text) {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some((tokens.get(1 .. at)?, tokens.get(at.saturating_add(1) ..)?));
            }
        }
        else if depth == 0 {
            return None;
        }
    }
    None
}

/// The leaves of `leaves` from the first of `tokens` to the last.
///
/// # Specification
/// trivial.
fn spanned<'leaves, 'source>(
    leaves: &'leaves [Leaf<'source>],
    tokens: &[Token<'_>],
) -> Option<&'leaves [Leaf<'source>]>
{
    let (&Token(LeafIndex(first), _), &Token(LeafIndex(last), _)) =
        (tokens.first()?, tokens.last()?);
    leaves.get(first ..= last)
}

/// Whether a token is a name a binder may take.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Identifier
{
    /// It is.
    Yes,
    /// It is not.
    No,
}

/// Whether `token` is a name a binder may take: a letter or `_`, then
/// letters, digits and `_`.
///
/// # Specification
/// trivial.
fn identifier(Token(_, text): Token<'_>) -> Identifier
{
    let mut chars = text.chars();
    if chars
        .next()
        .is_some_and(|first| first.is_alphabetic() || first == '_')
        && chars.all(|next| next.is_alphanumeric() || next == '_')
    {
        Identifier::Yes
    }
    else {
        Identifier::No
    }
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
