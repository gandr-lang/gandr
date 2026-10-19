//! The formatter at token parity with the printer (#755). For each
//! declaration a corpus source signs `def name : T ;`, the printer spells its
//! type in the sugared and the explicit form, and the formatter, given the
//! source with that signature written in one form, writes it in the other
//! exactly as the printer does, and keeps it in its own. For each declaration
//! the lowering completes, the same holds of its whole printing, `def name :
//! T ;` and `def name = body ;`, where the printing reads back to itself.
//! Tokens are compared, never bytes: the two lay out apart.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use std::path::Path;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::equal_type_syntax;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_format::Beside;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::Formatted;
use gandr_surface_format::format_beside;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::Unreadable;
use gandr_surface_pretty::Unspelled;
use gandr_surface_pretty::present_computation;
use gandr_surface_pretty::present_type;
use gandr_surface_pretty::present_value;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_workflow_sweep::CorpusName;
use quenchant_shape::shape::Maybe;

/// The page the printer spells a signature on: wide, so a type is one line.
const PAGE: u32 = 1_000;

/// The declarations kept out of the parity, each by its source, its name and
/// the issue that keeps it out: the parity holds for every other. The
/// formatter withdraws both of `empty.gandr`'s from either rewrite of their
/// value function: rewritten, the body's empty case lowers to other core or
/// is refused (#808). It withdraws `path-operand.gandr`'s `stay` from either
/// rewrite of its dependent alias: `stayUp`'s call reads the alias and not
/// the explicit thunk (#812).
const EXCLUDED: [(&str, &str, &str); 3] = [
    ("fixture/model/data/empty.gandr", "viaLambda", "#808"),
    ("fixture/model/data/empty.gandr", "viaStated", "#808"),
    ("fixture/model/identity/path-operand.gandr", "stay", "#812"),
];

/// A source's text, its path standing for its import closure.
#[derive(Clone, Copy, Debug)]
struct Written<'text>
{
    /// The source's path.
    path: &'text Path,
    /// Its text.
    text: SourceText<'text>,
}

/// One signature `def name : T ;` a source writes.
#[derive(Clone, Debug)]
struct Signed
{
    /// The signature form's key.
    key: NodeKey,
    /// The declaration's name.
    name: String,
    /// The span of `T`.
    ty: ByteSpan,
}

/// The tokens of `text`, whitespace and comments left out.
///
/// # Specification
/// trivial.
fn tokens(fragment: SourceFragment<'_>) -> Vec<String>
{
    let text = <&str>::from(fragment);
    label(fragment)
        .into_iter()
        .filter(|token| token.lexeme != Lexeme::Space)
        .filter_map(|token| {
            text.get(usize::try_from(token.start).ok()? .. usize::try_from(token.end).ok()?)
                .map(String::from)
        })
        .collect()
}

/// The signatures `def name : T ;` among the top-level forms of `text`.
///
/// # Specification
/// trivial.
fn signed(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> Vec<Signed>
{
    let Ok(parsed) = parse(grammar, text)
    else {
        return Vec::new();
    };
    let text = <&str>::from(text);
    let tree = parsed.tree();
    let mut found = Vec::new();
    for form in tree.children(tree.root()) {
        let (Some(key), Some(node)) = (tree.key(form), tree.node(form))
        else {
            continue;
        };
        let span = node.span();
        let Some(written) = text.get(usize::from(span.start()) .. usize::from(span.end()))
        else {
            continue;
        };
        let read: Vec<(usize, usize)> = label(SourceFragment::from(written))
            .into_iter()
            .filter(|token| token.lexeme != Lexeme::Space)
            .filter_map(|token| {
                Some((
                    usize::try_from(token.start).ok()?,
                    usize::try_from(token.end).ok()?,
                ))
            })
            .collect();
        let at = |index: usize| {
            let &(start, end) = read.get(index)?;
            written.get(start .. end)
        };
        let (Some("def"), Some(name), Some(":"), Some(&(first, _)), Some(&(_, last)), Some(";")) = (
            at(0),
            at(1),
            at(2),
            read.get(3),
            read.len().checked_sub(2).and_then(|index| read.get(index)),
            read.len().checked_sub(1).and_then(at),
        )
        else {
            continue;
        };
        let start = usize::from(span.start()).saturating_add(first);
        let end = usize::from(span.start()).saturating_add(last);
        let Ok(ty) = ByteSpan::new(start.into(), end.into())
        else {
            continue;
        };
        found.push(Signed {
            key,
            name: String::from(name),
            ty,
        });
    }
    found
}

/// The type table of `written`, typed beside the siblings it imports.
///
/// # Specification
/// trivial.
fn typed(
    grammar: &Pbg,
    written: Written<'_>,
) -> Option<TypeTable>
{
    let text = written.text;
    match lay_out(grammar, written.path, classify(written.path), text) {
        Maybe::Present(laid) => TypeTable::of_unit(
            grammar,
            SourceText::from(laid.text.as_str()),
            &laid.unit,
            laid.base,
        )
        .ok(),
        Maybe::Absent(_) => TypeTable::of(grammar, text).ok(),
    }
}

/// `written` formatted into `form` beside the siblings it imports: the text
/// and the rewrites withdrawn from it.
///
/// # Specification
/// trivial.
fn formatted(
    grammar: &Pbg,
    written: Written<'_>,
    form: gandr_surface_format::Form,
) -> Result<Formatted, String>
{
    let text = written.text;
    let parsed = parse(grammar, text).map_err(|error| format!("does not parse: {error}"))?;
    let laid = lay_out(grammar, written.path, classify(written.path), text);
    let beside = match laid {
        Maybe::Present(ref laid) => Beside::Imports {
            before: SourceText::from(laid.text.get(.. usize::from(laid.base)).unwrap_or_default()),
            unit: &laid.unit,
        },
        Maybe::Absent(_) => Beside::Alone,
    };
    let options = FormatOptions {
        form,
        ..FormatOptions::default()
    };
    format_beside(grammar, &parsed, options, beside)
        .map_err(|error| format!("does not format: {error}"))
}

/// What the printer spells for one declaration in one form.
#[derive(Clone, Debug)]
enum Spelled
{
    /// Its type, faithfully and whole.
    Faithful(String),
    /// Its type, which the printer does not spell faithfully: the text it
    /// wrote.
    Unfaithful(String),
    /// No type: the lowering refused the declaration, so no form is in
    /// question.
    Untyped,
}

/// The printer's spelling of each signed declaration's type in the sugared
/// and the explicit form, by name.
///
/// # Specification
/// trivial.
fn printed(
    table: &TypeTable,
    signatures: &[Signed],
) -> BTreeMap<String, (Spelled, Spelled)>
{
    let spell = |key: NodeKey, form: Form| {
        let style = Style {
            form,
            spelling: Spelling::Ascii,
        };
        match table.declared(key, PageWidth::from(PAGE), style) {
            Maybe::Present(Declared::Typed(ty))
                if ty.fidelity() == Fidelity::Faithful && ty.unspelled().is_empty() =>
            {
                Spelled::Faithful(String::from(ty.as_ref()))
            },
            Maybe::Present(Declared::Typed(ty)) => Spelled::Unfaithful(String::from(ty.as_ref())),
            Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => Spelled::Untyped,
        }
    };
    signatures
        .iter()
        .map(|signed| {
            (
                signed.name.clone(),
                (
                    spell(signed.key, Form::Sugared),
                    spell(signed.key, Form::Explicit),
                ),
            )
        })
        .collect()
}

/// `text` with each signature's type written as `spelling` gives it.
///
/// # Specification
/// trivial.
fn respelled(
    text: SourceText<'_>,
    signatures: &[Signed],
    spelling: impl Fn(&str) -> Option<String>,
) -> String
{
    let mut out = String::from(<&str>::from(text));
    for signed in signatures.iter().rev() {
        if let Some(ty) = spelling(&signed.name) {
            out.replace_range(
                usize::from(signed.ty.start()) .. usize::from(signed.ty.end()),
                &ty,
            );
        }
    }
    out
}

/// How a source's own signatures stand against the printer: each counted
/// by which of the printer's spellings its tokens match. Reported, never
/// gated: binder names, labels, alias unfolding and grades part an author's
/// spelling from the printer's, and none of them is a form question.
#[derive(Clone, Copy, Debug, Default)]
struct Census
{
    /// Signatures written as the printer spells them sugared, and not
    /// explicitly.
    sugared: usize,
    /// Signatures written as the printer spells them explicitly, and not
    /// sugared.
    explicit: usize,
    /// Signatures the printer spells alike in both forms, written so.
    either: usize,
    /// Signatures written as the printer spells them in neither form.
    neither: usize,
}

impl Census
{
    /// This census with `other`'s counts added.
    ///
    /// # Specification
    /// trivial.
    const fn add(
        self,
        other: Self,
    ) -> Self
    {
        Self {
            sugared: self.sugared.saturating_add(other.sugared),
            explicit: self.explicit.saturating_add(other.explicit),
            either: self.either.saturating_add(other.either),
            neither: self.neither.saturating_add(other.neither),
        }
    }
}

/// The census of `written`'s signatures the printer spells faithfully.
///
/// # Specification
/// trivial.
fn census(
    grammar: &Pbg,
    written: Written<'_>,
) -> Census
{
    let mut census = Census::default();
    let signatures = signed(grammar, written.text);
    if signatures.is_empty() {
        return census;
    }
    let Some(table) = typed(grammar, written)
    else {
        return census;
    };
    let spelled = printed(&table, &signatures);
    let text = <&str>::from(written.text);
    for signature in &signatures {
        let Some(&(Spelled::Faithful(ref sugared), Spelled::Faithful(ref explicit))) =
            spelled.get(&signature.name)
        else {
            continue;
        };
        let Some(own) =
            text.get(usize::from(signature.ty.start()) .. usize::from(signature.ty.end()))
        else {
            continue;
        };
        let own = tokens(SourceFragment::from(own));
        let matches = |spelling: &String| tokens(SourceFragment::from(spelling.as_str())) == own;
        let count = match (matches(sugared), matches(explicit)) {
            (true, true) => &mut census.either,
            (true, false) => &mut census.sugared,
            (false, true) => &mut census.explicit,
            (false, false) => &mut census.neither,
        };
        *count = count.saturating_add(1);
    }
    census
}

/// Every way `written`'s signatures, spelled by the printer, fail the
/// parity: one line each.
///
/// # Specification
/// trivial.
fn misses(
    grammar: &Pbg,
    written: Written<'_>,
    name: &CorpusName,
) -> Vec<String>
{
    let name: &str = name.as_ref();
    let signatures = signed(grammar, written.text);
    if signatures.is_empty() {
        return Vec::new();
    }
    let Some(table) = typed(grammar, written)
    else {
        return vec![format!("{name}: the source does not type")];
    };
    let excluded = |declaration: &str| {
        EXCLUDED
            .iter()
            .any(|&(source, held, _)| name.ends_with(source) && held == declaration)
    };
    let mut misses = Vec::new();
    let mut printed_whole = BTreeMap::new();
    for (declaration, pair) in printed(&table, &signatures) {
        if excluded(&declaration) {
            continue;
        }
        match pair {
            (Spelled::Faithful(sugared), Spelled::Faithful(explicit)) => {
                drop(printed_whole.insert(declaration, (sugared, explicit)));
            },
            (Spelled::Unfaithful(text), _) | (_, Spelled::Unfaithful(text)) => misses.push(format!(
                "{name}: `{declaration}`: the printer does not spell its type faithfully: {text}"
            )),
            (Spelled::Untyped, _) | (_, Spelled::Untyped) => {},
        }
    }
    let printed = printed_whole;
    let forms = [
        (
            Form::Explicit,
            gandr_surface_format::Form::Sugared,
            Form::Sugared,
        ),
        (
            Form::Sugared,
            gandr_surface_format::Form::Explicit,
            Form::Explicit,
        ),
        (
            Form::Sugared,
            gandr_surface_format::Form::Sugared,
            Form::Sugared,
        ),
        (
            Form::Explicit,
            gandr_surface_format::Form::Explicit,
            Form::Explicit,
        ),
    ];
    for (from, into, expected) in forms {
        let pick = |pair: &(String, String), form: Form| match form {
            Form::Sugared => pair.0.clone(),
            Form::Explicit => pair.1.clone(),
        };
        let variant = respelled(written.text, &signatures, |declaration| {
            printed.get(declaration).map(|pair| pick(pair, from))
        });
        let out = match formatted(
            grammar,
            Written {
                path: written.path,
                text: SourceText::from(variant.as_str()),
            },
            into,
        ) {
            Ok(out) => out.into_text(),
            Err(error) => {
                misses.push(format!("{name}: from {from:?} into {into}: {error}"));
                continue;
            },
        };
        let mut wrote: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for signed in signed(grammar, SourceText::from(out.as_str())) {
            if let Some(ty) =
                out.get(usize::from(signed.ty.start()) .. usize::from(signed.ty.end()))
            {
                drop(wrote.insert(signed.name, tokens(SourceFragment::from(ty))));
            }
        }
        for (declaration, pair) in &printed {
            let want = tokens(SourceFragment::from(pick(pair, expected).as_str()));
            match wrote.get(declaration) {
                Some(got) if *got == want => {},
                got => misses.push(format!(
                    "{name}: `{declaration}` from {from:?} into {into}:\n  formatter: {}\n  printer:   {}",
                    got.map_or_else(|| String::from("(no signature)"), |got| got.join(" ")),
                    want.join(" ")
                )),
            }
        }
    }
    misses
}

/// The page the printer spells a whole declaration on: wide, so a type is
/// one line and a body few.
const BODY_PAGE: u32 = 1_000;

/// The declarations kept out of the body parity by name, each by its source,
/// its name and the issue that keeps it out; every other declaration whose
/// printing reads back is held to it. An entry whose declaration meets the
/// parity is itself a miss, so the list shrinks as each issue closes.
///
/// The formatter withdraws each rewrite of these: a declaration that reads
/// the rewritten one, and that the printer does not spell faithfully, would
/// lower to other core (#812); `thrice` and `unthrice`, written explicitly,
/// are refused (#812); `leftUnit`'s composite has its motive under the
/// declaration's binder (#803).
const EXCLUDED_BODIES: [(&str, &str, &str); 9] = [
    ("lc/subst-as-rename.gandr", "weakenedVariable", "#812"),
    ("lc/subst-rename.gandr", "renameLookWeakens", "#812"),
    ("lc/subst-rename.gandr", "weakenedSquare", "#812"),
    ("lc/subst-subst.gandr", "substLookWeakenLift", "#812"),
    ("lc/subst-subst.gandr", "weakenedComposites", "#812"),
    ("identity/path-operand.gandr", "walkTwice", "#812"),
    ("identity/path-operand.gandr", "thrice", "#812"),
    ("identity/path-operand.gandr", "unthrice", "#812"),
    ("identity/word-append.gandr", "leftUnit", "#803"),
];

/// Why the body parity cannot hold a declaration, by the issue whose symptom
/// its printing shows: a reason read off the printing, never a name list.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Held
{
    /// A `case` arm on a path constructor printed `?` (#823).
    Unnamed,
    /// A printing marked approximate that names no reason (#820).
    Unreasoned,
    /// A printing that, substituted for the declaration, does not lower back
    /// to itself (#815).
    Unread,
    /// A printing whose sugared and explicit spellings, each substituted
    /// for the declaration, lower to different core, where the sugared
    /// spelling writes no path composite (#808).
    Apart,
    /// The same, where the sugared spelling writes a path composite `then`
    /// (#803).
    ApartComposite,
}

impl fmt::Display for Held
{
    /// The issue, and the symptom in a few words.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Unnamed => "#823, a path-constructor arm printed `?`",
            Self::Unreasoned => "#820, approximate with no reason",
            Self::Unread => "#815, the printing does not lower back",
            Self::Apart => "#808, the two spellings lower apart",
            Self::ApartComposite => "#803, the two spellings of a composite lower apart",
        })
    }
}

/// One declaration the printer spells whole in both forms.
#[derive(Clone, Debug)]
struct Printed
{
    /// Its name.
    name: String,
    /// The spans, in the source, of the top-level forms that hold it.
    forms: Vec<ByteSpan>,
    /// Its type in both forms.
    ty: Spellings,
    /// Its definition's body in both forms.
    body: Spellings,
}

/// One printing in the sugared and the explicit form.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Spellings
{
    /// The sugared spelling.
    sugared: String,
    /// The explicit spelling.
    explicit: String,
}

impl Spellings
{
    /// The spelling in `form`.
    ///
    /// # Specification
    /// trivial.
    const fn of(
        &self,
        form: Form,
    ) -> &String
    {
        match form {
            Form::Sugared => &self.sugared,
            Form::Explicit => &self.explicit,
        }
    }
}

/// A declaration's type and body as the printer spells them in one form.
#[derive(Clone, Debug)]
enum Spelt
{
    /// Both, faithfully: the type and the body.
    Whole(String, String),
    /// Not faithfully, for a reason an issue holds.
    Held(Held),
    /// Not faithfully, for another reason: what the printer wrote.
    Unfaithful(String),
}

/// The type `ty` and body `body` of a declaration, lowered into `arena`, as
/// `source` spells them in `form`: a thunked body as `thunk { … }` around its
/// computation, every other as its value.
///
/// # Specification
/// trivial.
fn spelt(
    source: &CoreSource<'_>,
    arena: &CoreArena,
    (ty, body): (ValueTypeId, ValueId),
    form: Form,
) -> Spelt
{
    let style = Style {
        form,
        spelling: Spelling::Ascii,
    };
    let page = PageWidth::from(BODY_PAGE);
    let typed = present_type(source, CoreNode::ValueType(ty), page, style);
    let bodied = match arena.value(body) {
        Some(&Value::Thunk(computation)) => {
            present_computation(source, CoreNode::Computation(computation), page, style)
                .map(|printed| (format!("thunk {{ {} }}", printed.as_ref()), printed))
        },
        _ => present_value(source, CoreNode::Value(body), page, style)
            .map(|printed| (String::from(printed.as_ref()), printed)),
    };
    let (Ok(typed), Ok((text, bodied))) = (typed, bodied)
    else {
        return Spelt::Unfaithful(String::from("the printer refused it"));
    };
    let faithful = |fidelity: Fidelity, unspelled: &BTreeSet<Unspelled>| {
        fidelity == Fidelity::Faithful && unspelled.is_empty()
    };
    if faithful(typed.fidelity(), typed.unspelled())
        && faithful(bodied.fidelity(), bodied.unspelled())
    {
        return Spelt::Whole(String::from(typed.as_ref()), text);
    }
    let unspelled: BTreeSet<Unspelled> = typed
        .unspelled()
        .iter()
        .chain(bodied.unspelled())
        .copied()
        .collect();
    if unspelled.is_empty() {
        Spelt::Held(Held::Unreasoned)
    }
    else if unspelled
        .iter()
        .all(|reason| *reason == Unspelled::Unreadable(Unreadable::Unnamed))
    {
        Spelt::Held(Held::Unnamed)
    }
    else {
        Spelt::Unfaithful(format!("{unspelled:?}: {text}"))
    }
}

/// The text `written` lays out — its import closure, then the source — the
/// unit that lowers it and where the source starts in that text.
///
/// # Specification
/// trivial.
fn laid(
    grammar: &Pbg,
    written: Written<'_>,
) -> (String, Unit, ByteOffset)
{
    match lay_out(grammar, written.path, classify(written.path), written.text) {
        Maybe::Present(laid) => (laid.text.clone(), laid.unit.clone(), laid.base),
        Maybe::Absent(_) => (
            String::from(<&str>::from(written.text)),
            Unit::single(),
            0_usize.into(),
        ),
    }
}

/// What the body parity reads of a source: each declaration it spells
/// whole, each it holds and why, and each the printer spells unfaithfully
/// for a reason no issue holds.
#[derive(Clone, Debug, Default)]
struct Read
{
    /// The declarations spelled whole in both forms, in source order.
    printed: Vec<Printed>,
    /// The declarations held, by name.
    held: BTreeMap<String, Held>,
    /// One line for each declaration spelled unfaithfully otherwise.
    unfaithful: Vec<String>,
}

/// Each completed declaration `written` writes, read by the printer in both
/// forms; nothing when the source does not lower.
///
/// # Specification
/// trivial.
fn read(
    grammar: &Pbg,
    written: Written<'_>,
) -> Option<Read>
{
    let (text, unit, base) = laid(grammar, written);
    let base = usize::from(base);
    let parsed = parse(grammar, SourceText::from(text.as_str())).ok()?;
    let tree = parsed.tree();
    let mut spans = BTreeMap::new();
    for form in tree.children(tree.root()) {
        if let (Some(key), Some(node)) = (tree.key(form), tree.node(form)) {
            let _previous = spans.insert(key, node.span());
        }
    }
    let mut arena = CoreArena::new();
    let module = lower_unit(
        grammar,
        tree,
        &unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .ok()?;
    let owned = constant_names(&module);
    let names: Vec<Name<'_>> = owned.iter().map(|name| Name::from(name.as_str())).collect();
    let families = Families::of(&module);
    let constructors = families.naming(&names);
    let source = CoreSource::new(&arena, &names).naming(&constructors);
    let mut read = Read::default();
    for declaration in module.declarations() {
        if usize::from(declaration.span().start()) < base {
            continue;
        }
        let DeclarationOutcome::Completed {
            declared_type,
            body,
        } = declaration.outcome()
        else {
            continue;
        };
        let mut forms: Vec<ByteSpan> = Vec::new();
        for half in [declaration.signature(), declaration.definition()] {
            let Maybe::Present(key) = half
            else {
                continue;
            };
            let Some(span) = spans.get(&key.form())
            else {
                continue;
            };
            let (Some(start), Some(end)) = (
                usize::from(span.start()).checked_sub(base),
                usize::from(span.end()).checked_sub(base),
            )
            else {
                continue;
            };
            if let Ok(own) = ByteSpan::new(start.into(), end.into())
                && !forms.contains(&own)
            {
                forms.push(own);
            }
        }
        if forms.is_empty() {
            continue;
        }
        forms.sort_by_key(|span| span.start());
        let name = format!("{}", declaration.name());
        let node = (declared_type, body);
        match (
            spelt(&source, &arena, node, Form::Sugared),
            spelt(&source, &arena, node, Form::Explicit),
        ) {
            (Spelt::Whole(sugared_type, sugared), Spelt::Whole(explicit_type, explicit)) => {
                read.printed.push(Printed {
                    name,
                    forms,
                    ty: Spellings {
                        sugared: sugared_type,
                        explicit: explicit_type,
                    },
                    body: Spellings { sugared, explicit },
                });
            },
            (Spelt::Unfaithful(text), _) | (_, Spelt::Unfaithful(text)) => {
                read.unfaithful.push(format!(
                    "`{name}`: the printer does not spell it faithfully: {text}"
                ));
            },
            (Spelt::Held(held), _) | (_, Spelt::Held(held)) => {
                let _previous = read.held.insert(name, held);
            },
        }
    }
    Some(read)
}

/// `own` with each of `printed`'s declarations written as the printer spells
/// it in `form`: its signature and its definition in place of the forms
/// that held it.
///
/// # Specification
/// trivial.
fn substituted(
    own: SourceText<'_>,
    printed: &[&Printed],
    form: Form,
) -> String
{
    let mut edits: Vec<(ByteSpan, String)> = Vec::new();
    for declaration in printed {
        let (ty, body) = (declaration.ty.of(form), declaration.body.of(form));
        let whole = format!(
            "def {name} : {ty} ;\ndef {name} = {body} ;",
            name = declaration.name
        );
        for (index, &span) in declaration.forms.iter().enumerate() {
            edits.push((
                span,
                if index == 0 {
                    whole.clone()
                }
                else {
                    String::new()
                },
            ));
        }
    }
    edits.sort_by_key(|&(span, _)| core::cmp::Reverse(span.start()));
    let mut out = String::from(<&str>::from(own));
    for (span, replacement) in edits {
        out.replace_range(
            usize::from(span.start()) .. usize::from(span.end()),
            &replacement,
        );
    }
    out
}

/// The declarations of `variant`, a source standing at `written`'s path,
/// that the printer spells in `form` as `printed` spells them: those whose
/// printing reads back to itself.
///
/// # Specification
/// trivial.
fn reading_back(
    grammar: &Pbg,
    variant: Written<'_>,
    printed: &[&Printed],
    form: Form,
) -> BTreeSet<String>
{
    let Some(again) = read(grammar, variant)
    else {
        return BTreeSet::new();
    };
    printed
        .iter()
        .filter(|declaration| {
            again.printed.iter().any(|back| {
                back.name == declaration.name
                    && back.ty.of(form) == declaration.ty.of(form)
                    && back.body.of(form) == declaration.body.of(form)
            })
        })
        .map(|declaration| declaration.name.clone())
        .collect()
}

/// The declarations of `printed` whose sugared and explicit spellings,
/// substituted into `written` together, lower to different core: the two
/// lowerings share one arena and are compared as the formatter's meaning
/// check compares them.
///
/// # Specification
/// trivial.
fn apart(
    grammar: &Pbg,
    written: Written<'_>,
    printed: &[&Printed],
) -> BTreeSet<String>
{
    let mut parted = BTreeSet::new();
    if printed.is_empty() {
        return parted;
    }
    let laid: Vec<(String, Unit, ByteOffset)> = [Form::Sugared, Form::Explicit]
        .into_iter()
        .map(|form| {
            let variant = substituted(written.text, printed, form);
            laid(grammar, Written {
                path: written.path,
                text: SourceText::from(variant.as_str()),
            })
        })
        .collect();
    let Ok(parsed) = laid
        .iter()
        .map(|&(ref text, ..)| parse(grammar, SourceText::from(text.as_str())))
        .collect::<Result<Vec<_>, _>>()
    else {
        return parted;
    };
    let mut arena = CoreArena::new();
    let mut modules = Vec::new();
    for (parsed, &(_, ref unit, base)) in parsed.iter().zip(&laid) {
        let Ok(module) = lower_unit(
            grammar,
            parsed.tree(),
            unit,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        else {
            return parted;
        };
        let completed: BTreeMap<String, (ValueTypeId, ValueId)> = module
            .declarations()
            .iter()
            .filter(|declaration| declaration.span().start() >= base)
            .filter_map(|declaration| {
                if let DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } = declaration.outcome()
                {
                    Some((format!("{}", declaration.name()), (declared_type, body)))
                }
                else {
                    None
                }
            })
            .collect();
        modules.push(completed);
    }
    let &[ref sugared, ref explicit] = modules.as_slice()
    else {
        return parted;
    };
    for declaration in printed {
        let same = match (
            sugared.get(&declaration.name),
            explicit.get(&declaration.name),
        ) {
            (Some(&(left_type, left)), Some(&(right_type, right))) => {
                equal_type_syntax(&arena, left_type, right_type) == CertificateEquality::Equal
                    && equal_certificate_syntax(&arena, left, right) == CertificateEquality::Equal
            },
            _ => false,
        };
        if !same {
            let _inserted = parted.insert(declaration.name.clone());
        }
    }
    parted
}

/// Each top-level `def name = body ;` of `text`: the body's tokens, by name.
///
/// # Specification
/// trivial.
fn defined(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> BTreeMap<String, Vec<String>>
{
    let mut found = BTreeMap::new();
    let Ok(parsed) = parse(grammar, text)
    else {
        return found;
    };
    let text = <&str>::from(text);
    let tree = parsed.tree();
    for form in tree.children(tree.root()) {
        let Some(span) = tree.node(form).map(gandr_surface_syntax::Node::span)
        else {
            continue;
        };
        let Some(written) = text.get(usize::from(span.start()) .. usize::from(span.end()))
        else {
            continue;
        };
        if let &[ref def, ref name, ref equals, ref body @ .., ref end] =
            tokens(SourceFragment::from(written)).as_slice()
            && def == "def"
            && equals == "="
            && end == ";"
        {
            let _previous = found.insert(name.clone(), body.to_vec());
        }
    }
    found
}

/// What the body parity found in one source.
#[derive(Clone, Debug, Default)]
struct Bodies
{
    /// One line for each way the parity fails.
    misses: Vec<String>,
    /// The declarations held out, by why: each as its source and name.
    held: BTreeMap<Held, Vec<String>>,
    /// The declarations held to the parity.
    compared: usize,
}

/// The body parity over `written`: each completed declaration whose
/// printing reads back to itself in both forms, substituted for its forms in
/// one form, is formatted into the other — and into its own — exactly as
/// the printer spells it there, signature and body.
///
/// # Specification
/// trivial.
fn bodies(
    grammar: &Pbg,
    written: Written<'_>,
    name: &CorpusName,
) -> Bodies
{
    let name: &str = name.as_ref();
    let mut found = Bodies::default();
    let Some(read) = read(grammar, written)
    else {
        return found;
    };
    for line in read.unfaithful {
        found.misses.push(format!("{name}: {line}"));
    }
    let mut holding: Vec<(Held, &str)> = read
        .held
        .iter()
        .map(|(declaration, &held)| (held, declaration.as_str()))
        .collect();
    let all: Vec<&Printed> = read.printed.iter().collect();
    let mut back: Option<BTreeSet<String>> = None;
    for form in [Form::Sugared, Form::Explicit] {
        let variant = substituted(written.text, &all, form);
        let reads = reading_back(
            grammar,
            Written {
                path: written.path,
                text: SourceText::from(variant.as_str()),
            },
            &all,
            form,
        );
        back = Some(match back {
            Some(before) => before.intersection(&reads).cloned().collect(),
            None => reads,
        });
    }
    let back = back.unwrap_or_default();
    let (read_back, unread): (Vec<&Printed>, Vec<&Printed>) = all
        .into_iter()
        .partition(|declaration| back.contains(&declaration.name));
    holding.extend(
        unread
            .iter()
            .map(|declaration| (Held::Unread, declaration.name.as_str())),
    );
    let parted = apart(grammar, written, &read_back);
    let (held, parted): (Vec<&Printed>, Vec<&Printed>) = read_back
        .into_iter()
        .partition(|declaration| !parted.contains(&declaration.name));
    for declaration in parted {
        let composite = [&declaration.ty.sugared, &declaration.body.sugared]
            .into_iter()
            .any(|text| {
                tokens(SourceFragment::from(text.as_str()))
                    .iter()
                    .any(|token| token == "then")
            });
        holding.push((
            if composite {
                Held::ApartComposite
            }
            else {
                Held::Apart
            },
            declaration.name.as_str(),
        ));
    }
    for (held, declaration) in holding {
        found
            .held
            .entry(held)
            .or_default()
            .push(format!("{name} `{declaration}`"));
    }
    if held.is_empty() {
        return found;
    }
    let excluded = |declaration: &str| {
        EXCLUDED_BODIES
            .iter()
            .any(|&(source, kept, _)| name.ends_with(source) && kept == declaration)
    };
    let mut met: BTreeMap<&str, bool> = held
        .iter()
        .map(|declaration| (declaration.name.as_str(), true))
        .collect();
    let forms = [
        (
            Form::Explicit,
            gandr_surface_format::Form::Sugared,
            Form::Sugared,
        ),
        (
            Form::Sugared,
            gandr_surface_format::Form::Explicit,
            Form::Explicit,
        ),
        (
            Form::Sugared,
            gandr_surface_format::Form::Sugared,
            Form::Sugared,
        ),
        (
            Form::Explicit,
            gandr_surface_format::Form::Explicit,
            Form::Explicit,
        ),
    ];
    for (from, into, expected) in forms {
        let variant = substituted(written.text, &held, from);
        let out = match formatted(
            grammar,
            Written {
                path: written.path,
                text: SourceText::from(variant.as_str()),
            },
            into,
        ) {
            Ok(out) => out,
            Err(error) => {
                found
                    .misses
                    .push(format!("{name}: bodies from {from:?} into {into}: {error}"));
                continue;
            },
        };
        let withdrawn: BTreeMap<&str, String> = out
            .withdrawn()
            .iter()
            .map(|withdrawal| {
                (
                    withdrawal.declaration.as_str(),
                    format!("{}", withdrawal.reason),
                )
            })
            .collect();
        let out = String::from(<&str>::from(out.text()));
        let mut signatures: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for signed in signed(grammar, SourceText::from(out.as_str())) {
            if let Some(ty) =
                out.get(usize::from(signed.ty.start()) .. usize::from(signed.ty.end()))
            {
                drop(signatures.insert(signed.name, tokens(SourceFragment::from(ty))));
            }
        }
        let definitions = defined(grammar, SourceText::from(out.as_str()));
        for declaration in &held {
            let want = |spelled: &Spellings| {
                Some(tokens(SourceFragment::from(spelled.of(expected).as_str())))
            };
            let (want_type, want_body) = (want(&declaration.ty), want(&declaration.body));
            let (got_type, got_body) = (
                signatures.get(&declaration.name).cloned(),
                definitions.get(&declaration.name).cloned(),
            );
            if (got_type.clone(), got_body.clone()) == (want_type.clone(), want_body.clone()) {
                continue;
            }
            let _previous = met.insert(declaration.name.as_str(), false);
            if excluded(&declaration.name) {
                continue;
            }
            let shown = |tokens: Option<Vec<String>>| {
                tokens.map_or_else(|| String::from("(none)"), |tokens| tokens.join(" "))
            };
            found.misses.push(format!(
                "{name}: `{}` from {from:?} into {into}{}:\n  formatter: {} = {}\n  printer:   {} = {}",
                declaration.name,
                withdrawn
                    .get(declaration.name.as_str())
                    .map_or_else(String::new, |reason| format!(", withdrawn: {reason}")),
                shown(got_type),
                shown(got_body),
                shown(want_type),
                shown(want_body),
            ));
        }
    }
    found.compared = held.len();
    for &(source, kept, issue) in &EXCLUDED_BODIES {
        if name.ends_with(source) && met.get(kept) == Some(&true) {
            found.misses.push(format!(
                "{name}: `{kept}` meets the parity; drop its exclusion under {issue}"
            ));
        }
    }
    found
}

/// The parity sweeps: a sample on every pull request, every source under the
/// `sweeps` profile.
mod sweeps
{
    use std::io::Write as _;

    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::Bodies;
    use super::Census;
    use super::Written;
    use super::bodies;
    use super::census;
    use super::laid;
    use super::misses;

    /// The sample: sixty-four sources, ranked by their BLAKE3 digest under
    /// this name, at least one of each corpus class, and every source the
    /// change adds or modifies (`gandr-workflow-sweep`).
    const SAMPLE: Sample = Sample {
        name: SampleName("the_formatter_spells_each_form_as_the_printer_does_755"),
        size: SampleSize(64),
    };

    #[test]
    fn the_formatter_spells_each_form_as_the_printer_does_755()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let sources = sweep.visit(SAMPLE, &corpus::sources().expect("the corpus reads"));
        let mut all = Vec::new();
        for source in sources {
            let text = std::fs::read_to_string(&source.path).expect("a corpus source is readable");
            all.extend(misses(
                &grammar,
                Written {
                    path: &source.path,
                    text: SourceText::from(text.as_str()),
                },
                &source.name,
            ));
        }
        assert!(all.is_empty(), "{} misses:\n{}", all.len(), all.join("\n"));
    }

    /// The body parity's sample: sixty-four sources no longer than
    /// [`BODIES_CEILING`], drawn as [`SAMPLE`] is.
    const BODIES: Sample = Sample {
        name: SampleName("the_formatter_spells_each_declaration_as_the_printer_does_755"),
        size: SampleSize(64),
    };

    /// The most bytes of text a source of the body parity's sample lays out,
    /// its import closure then itself: 16 KiB. The parity lowers that text
    /// seven times and formats it four, so its cost grows with the closure,
    /// not the source: the λ-calculus model's lemmas, 19 to 42 KB laid out,
    /// take a quarter to four fifths of a second each in a test build, as
    /// `univalence.gandr` does at 19 KB, and most of the corpus under 16 KB
    /// takes under a tenth. The whole corpus, those included, runs in about
    /// ten seconds under the `sweeps` profile.
    const BODIES_CEILING: usize = 0x4000;

    #[test]
    fn the_formatter_spells_each_declaration_as_the_printer_does_755()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let whole = sweep.coverage() == Coverage::Full;
        let read = |source: &corpus::Source| {
            std::fs::read_to_string(&source.path).expect("a corpus source is readable")
        };
        let candidates: Vec<_> = corpus::sources()
            .expect("the corpus reads")
            .into_iter()
            .filter(|source| {
                whole || {
                    let text = read(source);
                    // A source's own bytes bound its closure's below, so
                    // only a short one is laid out.
                    text.len() <= BODIES_CEILING && {
                        let written = Written {
                            path: &source.path,
                            text: SourceText::from(text.as_str()),
                        };
                        laid(&grammar, written).0.len() <= BODIES_CEILING
                    }
                }
            })
            .collect();
        let sources = sweep.visit(BODIES, &candidates);
        assert!(
            whole || sources.len() >= BODIES.size.0,
            "the sample is drawn: {}",
            sources.len()
        );
        let mut total = Bodies::default();
        let mut counted = Census::default();
        for source in sources {
            let text = read(&source);
            let written = Written {
                path: &source.path,
                text: SourceText::from(text.as_str()),
            };
            let found = bodies(&grammar, written, &source.name);
            total.misses.extend(found.misses);
            total.compared = total.compared.saturating_add(found.compared);
            for (why, names) in found.held {
                total.held.entry(why).or_default().extend(names);
            }
            if whole {
                counted = counted.add(census(&grammar, written));
            }
        }
        if whole {
            report(&total, counted);
        }
        let all = total.misses;
        assert!(all.is_empty(), "{} misses:\n{}", all.len(), all.join("\n"));
    }

    /// The whole corpus's report: the declarations the body parity holds,
    /// those it holds out by issue, and the census of the signatures as
    /// written; on standard error, and in the job's summary under CI.
    ///
    /// # Specification
    /// trivial.
    fn report(
        total: &Bodies,
        counted: Census,
    )
    {
        let mut rows = vec![format!("| held to the body parity | {} |", total.compared)];
        rows.extend(
            total
                .held
                .iter()
                .map(|(why, names)| format!("| held out: {why} | {} |", names.len())),
        );
        let out = format!(
            "### The formatter at parity with the printer (#755)\n\n| declarations | count |\n| --- | --- |\n{}\n\n| signatures as written | count |\n| --- | --- |\n| as the printer spells them sugared | {} |\n| as the printer spells them explicitly | {} |\n| alike in both forms | {} |\n| as the printer spells them in neither | {} |\n",
            rows.join("\n"),
            counted.sugared,
            counted.explicit,
            counted.either,
            counted.neither
        );
        std::eprintln!("{out}");
        for (why, names) in &total.held {
            std::eprintln!("held out, {why}:\n  {}", names.join("\n  "));
        }
        if let Some(path) = std::env::var_os("GITHUB_STEP_SUMMARY") {
            let mut summary = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(path)
                .expect("the job summary opens");
            summary
                .write_all(out.as_bytes())
                .expect("the job summary takes the report");
        }
    }
}
