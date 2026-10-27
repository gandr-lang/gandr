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
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Crossing;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::equal_type_syntax;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_diagnostics::model_slots;
use gandr_surface_diagnostics::telescopes;
use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_format::Beside;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::Formatted;
use gandr_surface_format::RewriteName;
use gandr_surface_format::Selection;
use gandr_surface_format::format_beside;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::ScopeAnswer;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::WrittenModel;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_pretty::Answered;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Elided;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::ForgetMap;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Modelled;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::Notation;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::Unspelled;
use gandr_surface_pretty::present_definition;
use gandr_surface_pretty::present_type;
use gandr_surface_pretty::present_whole;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_workflow_sweep::CorpusName;
use quenchant_shape::shape::Maybe;

/// The page the printer spells a signature on: wide, so a type is one line.
const PAGE: u32 = 1_000;

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

/// One top-level form of a parsed text: its key, when it has one, the span
/// it covers and the `=` it writes among its own tiles, when it writes one.
#[derive(Clone, Copy, Debug)]
struct TopLevel
{
    /// The form's key.
    key: Option<NodeKey>,
    /// The span of the form.
    span: ByteSpan,
    /// The span of the form's own `=`: a definition's, or a joined
    /// signature's before its value.
    equals: Option<ByteSpan>,
}

/// The top-level forms of `text`, parsed once for every reading of them;
/// none when it does not parse.
///
/// # Specification
/// trivial.
fn top_level(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> Vec<TopLevel>
{
    let Ok(parsed) = parse(grammar, text)
    else {
        return Vec::new();
    };
    let tree = parsed.tree();
    tree.children(tree.root())
        .filter_map(|form| {
            tree.node(form).map(|node| TopLevel {
                key: tree.key(form),
                span: node.span(),
                equals: equals(tree, form),
            })
        })
        .collect()
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

/// The span of the `=` the top-level form `form` of `tree` writes among its
/// own tiles: a definition's, or a joined signature's before its value.
///
/// # Specification
/// trivial.
fn equals(
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

/// The signatures `def name : T ;` among `forms`, the top-level forms of
/// `text`, and the signature half `def name : T` of each joined
/// `def name : T = e ;`.
///
/// # Specification
/// trivial.
fn signed(
    text: SourceText<'_>,
    forms: &[TopLevel],
) -> Vec<Signed>
{
    let text = <&str>::from(text);
    let mut found = Vec::new();
    let mut read: Vec<(usize, usize)> = Vec::new();
    for &TopLevel { key, span, equals } in forms {
        let Some(key) = key
        else {
            continue;
        };
        let Some(written) = text.get(usize::from(span.start()) .. usize::from(span.end()))
        else {
            continue;
        };
        read.clear();
        read.extend(
            label(SourceFragment::from(written))
                .into_iter()
                .filter(|token| token.lexeme != Lexeme::Space)
                .filter_map(|token| {
                    Some((
                        usize::try_from(token.start).ok()?,
                        usize::try_from(token.end).ok()?,
                    ))
                }),
        );
        let at = |index: usize| {
            let &(start, end) = read.get(index)?;
            written.get(start .. end)
        };
        // A joined form's type stops before its own `=`; the tokens stand in
        // offset order.
        let stop = equals
            .and_then(|equals| {
                let offset = usize::from(equals.start()).checked_sub(usize::from(span.start()))?;
                read.binary_search_by_key(&offset, |&(start, _)| start).ok()
            })
            .unwrap_or_else(|| read.len().saturating_sub(1));
        let (Some("def"), Some(name), Some(":"), Some(&(first, _)), Some(&(_, last)), Some(";")) = (
            at(0),
            at(1),
            at(2),
            read.get(3),
            stop.checked_sub(1).and_then(|index| read.get(index)),
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

/// The type table of `written`, typed beside the prelude and the siblings it
/// imports.
///
/// # Specification
/// trivial.
fn typed(
    grammar: &Pbg,
    written: Written<'_>,
) -> Option<TypeTable>
{
    let laid = lay_out(grammar, written.path, classify(written.path), written.text);
    TypeTable::of_unit(
        grammar,
        SourceText::from(laid.text.as_str()),
        &laid.unit,
        laid.base,
    )
    .ok()
}

/// `written` formatted into `form` through the rewrites `rewrites` selects,
/// beside the siblings it imports: the text and the rewrites withdrawn from
/// it.
///
/// # Specification
/// trivial.
fn formatted(
    grammar: &Pbg,
    written: Written<'_>,
    (form, rewrites): (gandr_surface_format::Form, Selection),
) -> Result<Formatted, String>
{
    let text = written.text;
    let parsed = parse(grammar, text).map_err(|error| format!("does not parse: {error}"))?;
    let laid = lay_out(grammar, written.path, classify(written.path), text);
    let beside = Beside::Imports {
        before: SourceText::from(laid.text.get(.. usize::from(laid.base)).unwrap_or_default()),
        unit: &laid.unit,
    };
    let options = FormatOptions {
        form,
        rewrites,
        ..FormatOptions::default()
    };
    format_beside(
        grammar,
        &parsed,
        options,
        (beside, Some(&gandr_surface_dispatcher::Elaborating)),
    )
    .map_err(|error| format!("does not format: {error}"))
}

/// Every rewrite but the merge of a signature with the definition after it:
/// the signature parity reads each signature the formatter writes, which
/// that merge writes into its function form.
const SIGNED: &[RewriteName] = &[
    RewriteName::Product,
    RewriteName::Sum,
    RewriteName::LazyProduct,
    RewriteName::Tuple,
    RewriteName::ValueFunction,
    RewriteName::DefaultGrade,
    RewriteName::PathComposite,
    RewriteName::PathInverse,
    RewriteName::PathAction,
    RewriteName::TailReturn,
    RewriteName::ShortAlias,
    RewriteName::LinearRun,
    RewriteName::InsertedThunk,
    RewriteName::InsertedReduct,
    RewriteName::InsertedForget,
];

/// The printer's form the source `text` declares at its head, which the
/// formatter writes it in whatever form it is asked for.
///
/// # Specification
/// trivial.
fn pinned(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> Option<Form>
{
    let parsed = parse(grammar, text).ok()?;
    match gandr_surface_format::declared_form(grammar, &parsed)? {
        gandr_surface_format::Form::Explicit => Some(Form::Explicit),
        gandr_surface_format::Form::Sugared => Some(Form::Sugared),
        gandr_surface_format::Form::Source => None,
    }
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
    let signatures = signed(written.text, &top_level(grammar, written.text));
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
    let signatures = signed(written.text, &top_level(grammar, written.text));
    if signatures.is_empty() {
        return Vec::new();
    }
    let Some(table) = typed(grammar, written)
    else {
        return vec![format!("{name}: the source does not type")];
    };
    let mut misses = Vec::new();
    let mut printed_whole = BTreeMap::new();
    for (declaration, pair) in printed(&table, &signatures) {
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
    let pinned = pinned(grammar, written.text);
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
        let expected = pinned.unwrap_or(expected);
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
            (into, Selection::Only(SIGNED)),
        ) {
            Ok(out) => out.into_text(),
            Err(error) => {
                misses.push(format!("{name}: from {from:?} into {into}: {error}"));
                continue;
            },
        };
        let mut wrote: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let reformatted = SourceText::from(out.as_str());
        for signed in signed(reformatted, &top_level(grammar, reformatted)) {
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

/// Why the body parity cannot hold a declaration, by the issue whose symptom
/// its printing shows: a reason read off the printing, never a name list.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Held
{
    /// A printing in the printer's own notation, which the grammar does not
    /// read back (#941).
    Notation,
    /// A printing whose sugared and explicit spellings, each substituted
    /// for the declaration, lower to different core (#808).
    Apart,
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
            Self::Notation => "#941, written in the printer's own notation",
            Self::Apart => "#808, the two spellings lower apart",
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
    /// How the printer writes it back.
    shape: Shape,
}

/// How the printer writes a declaration back.
#[derive(Clone, Debug)]
enum Shape
{
    /// A signature and a definition: its type and its body in both forms.
    Halves
    {
        /// Its type.
        ty: Spellings,
        /// Its definition's body.
        body: Spellings,
    },
    /// One form that declares it whole, as a function definition does.
    Whole(Spellings),
}

impl Printed
{
    /// The declaration as the printer writes it in `form`.
    ///
    /// # Specification
    /// trivial.
    fn written(
        &self,
        form: Form,
    ) -> String
    {
        match self.shape {
            Shape::Halves { ref ty, ref body } => format!(
                "def {name} : {ty} ;\ndef {name} = {body} ;",
                name = self.name,
                ty = ty.of(form),
                body = body.of(form),
            ),
            Shape::Whole(ref whole) => whole.of(form).clone(),
        }
    }
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
    /// The one form that declares it, faithfully.
    Declared(String),
    /// Not faithfully, for a reason an issue holds.
    Held(Held),
    /// Not faithfully, for another reason: what the printer wrote.
    Unfaithful(String),
}

/// The declaration `name`, its type `ty` and body `body` lowered into
/// `arena`, as `typed` spells its type and `bodied` its body in `form`: a
/// function definition whole as its `def name(…)` or `def rec name(…)`,
/// otherwise a thunked body as `thunk { … }` around its computation and
/// every other as its value.
///
/// # Specification
/// trivial.
fn spelt(
    (typed, bodied): (&CoreSource<'_>, &CoreSource<'_>),
    whole: (Name<'_>, ConstantIndex),
    (ty, body): (ValueTypeId, ValueId),
    form: Form,
) -> Spelt
{
    let style = Style {
        form,
        spelling: Spelling::Ascii,
    };
    let page = PageWidth::from(BODY_PAGE);
    let faithful = |printed: &Presentation| {
        printed.fidelity() == Fidelity::Faithful && printed.unspelled().is_empty()
    };
    if let Ok(Maybe::Present(whole)) = present_whole(bodied, whole, (ty, body), page, style) {
        if faithful(&whole) {
            return Spelt::Declared(String::from(whole.as_ref()));
        }
        return unfaithful(whole.unspelled(), SourceFragment::from(whole.as_ref()));
    }
    let typed = present_type(typed, CoreNode::ValueType(ty), page, style);
    let bodied = present_definition(bodied, CoreNode::Value(body), page, style)
        .map(|printed| (String::from(printed.as_ref()), printed));
    let (Ok(typed), Ok((text, bodied))) = (typed, bodied)
    else {
        return Spelt::Unfaithful(String::from("the printer refused it"));
    };
    if faithful(&typed) && faithful(&bodied) {
        return Spelt::Whole(String::from(typed.as_ref()), text);
    }
    let unspelled: BTreeSet<Unspelled> = typed
        .unspelled()
        .iter()
        .chain(bodied.unspelled())
        .copied()
        .collect();
    unfaithful(&unspelled, SourceFragment::from(text.as_str()))
}

/// A printing `text` the printer wrote approximately for the reasons
/// `unspelled`: held when an issue holds every reason, otherwise unfaithful.
///
/// # Specification
/// trivial.
fn unfaithful(
    unspelled: &BTreeSet<Unspelled>,
    text: SourceFragment<'_>,
) -> Spelt
{
    let text = <&str>::from(text);
    if unspelled.is_empty() {
        Spelt::Unfaithful(format!("approximate, naming no reason (#820): {text}"))
    }
    // A handler written as `reset` and `shift` leaves the scope of each
    // capability it delimits unnamed, so its region is elided with it.
    else if unspelled.iter().all(|reason| match *reason {
        Unspelled::Notation(_) => true,
        Unspelled::Elided(Elided::Region) => {
            unspelled.contains(&Unspelled::Notation(Notation::Reset))
        },
        Unspelled::Elided(_)
        | Unspelled::Unreadable(_)
        | Unspelled::Misplaced
        | Unspelled::Missing
        | Unspelled::Unbound
        | Unspelled::Exhausted
        | Unspelled::Unprintable
        | Unspelled::Primed
        | Unspelled::Universe
        | Unspelled::Protocol
        | Unspelled::OverBudget => false,
    }) {
        Spelt::Held(Held::Notation)
    }
    else {
        Spelt::Unfaithful(format!("{unspelled:?}: {text}"))
    }
}

/// The text `written` lays out — the prelude, its import closure, then the
/// source — the unit that lowers it and where the source starts in that
/// text.
///
/// # Specification
/// trivial.
fn laid(
    grammar: &Pbg,
    written: Written<'_>,
) -> (String, Unit, ByteOffset)
{
    let laid = lay_out(grammar, written.path, classify(written.path), written.text);
    (laid.text, laid.unit, laid.base)
}

/// The model type, or the capability scope's theory, `model` records, as the
/// printer spells it: the theory and each sort beside its type.
///
/// # Specification
/// trivial.
fn modelled(model: &WrittenModel) -> Modelled<'_>
{
    Modelled {
        theory: Name::from(model.theory.as_ref()),
        sorts: model
            .sorts
            .iter()
            .map(|&(ref sort, carrier)| (Name::from(sort.as_ref()), CoreNode::ValueType(carrier)))
            .collect(),
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

/// Each completed declaration `written` writes as a `def`, read by the
/// printer in both forms; nothing when the source does not lower. A
/// `theory` block is left out: the parity writes a declaration back as a
/// `def`, a form its name cannot take.
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
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .ok()?;
    // Where the checker carries a model across by a reduct or a forgetting
    // map, and by which: read off its elaboration, which the lowered core the
    // printer reads does not hold.
    let crossed: BTreeMap<ValueId, Crossing> =
        if module.reducts().is_empty() && module.forgets().is_empty() {
            BTreeMap::new()
        }
        else {
            gandr_surface_format::Elaborate::elaborate(
                &gandr_surface_dispatcher::Elaborating,
                &mut arena,
                &module,
            )
            .crossings
        };
    let crossings: Vec<(ValueId, ConstantIndex)> = crossed
        .iter()
        .map(|(&value, crossing)| (value, crossing.by))
        .filter(|&(_, reduct)| module.reducts().binary_search(&reduct).is_ok())
        .collect();
    let forgettings = gandr_surface_format::forgettings(&module, &arena, &crossed);
    let owned = constant_names(&module);
    let names: Vec<Name<'_>> = owned.iter().map(|name| Name::from(name.as_str())).collect();
    let families = Families::of(&module);
    let constructors = families.naming();
    // Each model type, and each capability scope over a theory and the model
    // answering it, as the source writes it, which the record or the signature
    // it lowers to does not hold.
    let mut models: Vec<(ValueTypeId, Modelled<'_>)> = module
        .origins()
        .models()
        .iter()
        .map(|&(ty, ref model)| (ty, modelled(model)))
        .collect();
    models.sort_by_key(|&(ty, _)| ty);
    let mut scopes: Vec<(ComputationId, Modelled<'_>)> = module
        .origins()
        .scope_theories()
        .iter()
        .map(|&(scope, ref model)| (scope, modelled(model)))
        .collect();
    scopes.sort_by_key(|&(scope, _)| scope);
    let mut answers: Vec<(ComputationId, Answered<'_>)> = module
        .origins()
        .scope_answers()
        .iter()
        .map(|&(scope, ref answer)| {
            (scope, match *answer {
                ScopeAnswer::Named(ref model) => Answered::Named(Name::from(model.as_ref())),
                ScopeAnswer::InScope => Answered::InScope,
            })
        })
        .collect();
    answers.sort_by_key(|&(scope, _)| scope);
    // Each forgetting map onto its own theory, whose written call the explicit
    // form writes as the map's form, as the formatter keeps it.
    let mut maps: Vec<(ConstantIndex, ForgetMap<'_>)> = module
        .forgettings()
        .iter()
        .filter(|forgetting| forgetting.onto == forgetting.theory)
        .map(|forgetting| {
            (forgetting.map, ForgetMap {
                theory: forgetting.theory,
                sorts: forgetting
                    .sorts
                    .iter()
                    .map(|sort| Name::from(sort.as_ref()))
                    .collect(),
            })
        })
        .collect();
    maps.sort_by_key(|&(map, _)| map);
    let implicits = telescopes(&module);
    let slots = model_slots(&module);
    let source = CoreSource::new(&arena, &names)
        .naming(&constructors)
        .crossing(&crossings)
        .forgetting(&forgettings)
        .forgetting_maps(&maps)
        .modeling(&models)
        .scoping(&scopes)
        .answering(&answers)
        .naming_implicits(&implicits)
        .flattening(&slots);
    // A body leaves each written reduct's or forgetting map's call to the
    // checker, which applies the map where the call stands; a type, read by
    // its value, keeps it.
    let mut implied: Vec<ConstantIndex> = module
        .reducts()
        .iter()
        .chain(module.forgets())
        .copied()
        .collect();
    implied.sort_unstable();
    let bodied = source.implying(&implied);
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
            let defined = text
                .get(usize::from(span.start()) .. usize::from(span.end()))
                .is_some_and(|own| {
                    tokens(SourceFragment::from(own))
                        .first()
                        .is_some_and(|first| first == "def")
                });
            if !defined {
                forms.clear();
                break;
            }
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
            spelt(
                (&source, &bodied),
                (Name::from(name.as_str()), declaration.constant()),
                node,
                Form::Sugared,
            ),
            spelt(
                (&source, &bodied),
                (Name::from(name.as_str()), declaration.constant()),
                node,
                Form::Explicit,
            ),
        ) {
            (Spelt::Whole(sugared_type, sugared), Spelt::Whole(explicit_type, explicit)) => {
                read.printed.push(Printed {
                    name,
                    forms,
                    shape: Shape::Halves {
                        ty: Spellings {
                            sugared: sugared_type,
                            explicit: explicit_type,
                        },
                        body: Spellings { sugared, explicit },
                    },
                });
            },
            (Spelt::Declared(sugared), Spelt::Declared(explicit)) => {
                read.printed.push(Printed {
                    name,
                    forms,
                    shape: Shape::Whole(Spellings { sugared, explicit }),
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
            (Spelt::Whole(..), Spelt::Declared(_)) | (Spelt::Declared(_), Spelt::Whole(..)) => {
                read.unfaithful.push(format!(
                    "`{name}`: the printer writes it whole in one form and in halves in the other"
                ));
            },
        }
    }
    Some(read)
}

/// `own` with each of `printed`'s declarations written as the printer spells
/// it in `form` in place of the forms that held it.
///
/// # Specification
/// trivial.
fn substituted(
    own: SourceText<'_>,
    printed: &[&Printed],
    form: Form,
) -> String
{
    // Each form a declaration held, with the declaration whose spelling
    // replaces it: the first form takes the whole, the rest are emptied.
    let mut edits: Vec<(ByteSpan, Option<&Printed>)> = Vec::new();
    for &declaration in printed {
        for (index, &span) in declaration.forms.iter().enumerate() {
            edits.push((span, (index == 0).then_some(declaration)));
        }
    }
    edits.sort_by_key(|&(span, _)| core::cmp::Reverse(span.start()));
    let mut out = String::from(<&str>::from(own));
    for (span, declaration) in edits {
        let whole = declaration
            .map(|declaration| declaration.written(form))
            .unwrap_or_default();
        out.replace_range(usize::from(span.start()) .. usize::from(span.end()), &whole);
    }
    out
}

/// The declarations of `variant`, a source standing at `written`'s path,
/// that the printer spells in `form` as `printed` spells them: those whose
/// printing reads back to itself, beside them each of `printed` the reading
/// of `variant` holds out, by why — a printing the parity cannot hold as
/// written — and every declaration the printer spells whole in `variant`.
///
/// # Specification
/// trivial.
fn reading_back(
    grammar: &Pbg,
    variant: Written<'_>,
    printed: &[&Printed],
    form: Form,
) -> (BTreeSet<String>, BTreeMap<String, Held>, Vec<Printed>)
{
    let Some(again) = read(grammar, variant)
    else {
        return (BTreeSet::new(), BTreeMap::new(), Vec::new());
    };
    let reads = printed
        .iter()
        .filter(|declaration| {
            again.printed.iter().any(|back| {
                back.name == declaration.name && back.written(form) == declaration.written(form)
            })
        })
        .map(|declaration| declaration.name.clone())
        .collect();
    let held = printed
        .iter()
        .filter_map(|declaration| {
            again
                .held
                .get(&declaration.name)
                .map(|&held| (declaration.name.clone(), held))
        })
        .collect();
    (reads, held, again.printed)
}

/// The declarations of `printed` whose sugared and explicit spellings,
/// substituted into `written` together, mean different programs: the two
/// lowerings share one arena and are compared as the formatter's meaning
/// check compares them, by the lowered core and, where that parts, by the
/// bodies the checker elaborates — a call written at its read and the `run`
/// statement binding it lower apart and elaborate alike (#1416).
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
    let mut lowerings = Vec::new();
    for (parsed, &(_, ref unit, base)) in parsed.iter().zip(&laid) {
        let Ok(module) = lower_unit(
            grammar,
            parsed.tree(),
            unit,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
            &mut gandr_surface_lowering::coincide::Decisions::none(),
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
        lowerings.push((module, base));
    }
    let &[ref sugared, ref explicit] = modules.as_slice()
    else {
        return parted;
    };
    // The bodies the checker elaborates for each spelling's declarations, by
    // name, read once a lowering parts.
    let mut elaborated: Option<Vec<BTreeMap<String, ValueId>>> = None;
    for declaration in printed {
        let same = match (
            sugared.get(&declaration.name),
            explicit.get(&declaration.name),
        ) {
            (Some(&(left_type, left)), Some(&(right_type, right))) => {
                equal_type_syntax(&arena, left_type, right_type) == CertificateEquality::Equal
                    && (equal_certificate_syntax(&arena, left, right) == CertificateEquality::Equal
                        || {
                            let bodies = elaborated.get_or_insert_with(|| {
                                lowerings
                                    .iter()
                                    .map(|&(ref module, base)| {
                                        let bodies = gandr_surface_format::Elaborate::elaborate(
                                            &gandr_surface_dispatcher::Elaborating,
                                            &mut arena,
                                            module,
                                        )
                                        .definitions;
                                        module
                                            .declarations()
                                            .iter()
                                            .zip(bodies)
                                            .filter(|&(declaration, _)| {
                                                declaration.span().start() >= base
                                            })
                                            .filter_map(|(declaration, body)| {
                                                Some((format!("{}", declaration.name()), body?))
                                            })
                                            .collect()
                                    })
                                    .collect()
                            });
                            match (
                                bodies
                                    .first()
                                    .and_then(|bodies| bodies.get(&declaration.name)),
                                bodies
                                    .get(1)
                                    .and_then(|bodies| bodies.get(&declaration.name)),
                            ) {
                                (Some(&left), Some(&right)) => {
                                    equal_certificate_syntax(&arena, left, right)
                                        == CertificateEquality::Equal
                                },
                                _ => false,
                            }
                        })
            },
            _ => false,
        };
        if !same {
            let _inserted = parted.insert(declaration.name.clone());
        }
    }
    parted
}

/// Each `def name = body ;` among `forms`, the top-level forms of `text`,
/// and each joined `def name : T = body ;`: the body's tokens, by name.
///
/// # Specification
/// trivial.
fn defined(
    text: SourceText<'_>,
    forms: &[TopLevel],
) -> BTreeMap<String, Vec<String>>
{
    let mut found = BTreeMap::new();
    let text = <&str>::from(text);
    for &TopLevel { span, equals, .. } in forms {
        let Some(written) = text.get(usize::from(span.start()) .. usize::from(span.end()))
        else {
            continue;
        };
        let whole = tokens(SourceFragment::from(written));
        let (&[ref def, ref name, ..], Some(own)) = (whole.as_slice(), equals)
        else {
            continue;
        };
        let Some(after) = text.get(usize::from(own.end()) .. usize::from(span.end()))
        else {
            continue;
        };
        if let &[ref body @ .., ref end] = tokens(SourceFragment::from(after)).as_slice()
            && def == "def"
            && end == ";"
        {
            let _previous = found.insert(name.clone(), body.to_vec());
        }
    }
    found
}

/// Each `def name(…) …`, `def name @[…] (…) …` or `def rec name(…) …` among
/// `forms`, the top-level forms of `text`: the whole form's tokens, by name.
///
/// # Specification
/// trivial.
fn recursed(
    text: SourceText<'_>,
    forms: &[TopLevel],
) -> BTreeMap<String, Vec<String>>
{
    let mut found = BTreeMap::new();
    let text = <&str>::from(text);
    for &TopLevel { span, .. } in forms {
        let Some(written) = text.get(usize::from(span.start()) .. usize::from(span.end()))
        else {
            continue;
        };
        let whole = tokens(SourceFragment::from(written));
        let named = match *whole.as_slice() {
            [ref def, ref rec, ref name, ..] if def == "def" && rec == "rec" => Some(name),
            [ref def, ref name, ref open, ..] if def == "def" && (open == "(" || open == "@[") => {
                Some(name)
            },
            _ => None,
        };
        if let Some(name) = named {
            let _previous = found.insert(name.clone(), whole.clone());
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

/// The body parity over `written`: each completed declaration's printing,
/// substituted for its forms in one form, reads back to itself in both forms
/// — a printing that does not is a miss — and is formatted into the other,
/// and into its own, exactly as the printer spells it there, signature and
/// body.
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
    let mut held_again: BTreeMap<String, Held> = BTreeMap::new();
    // Each variant's own printings, by the form substituted into it.
    let mut reprinted: Vec<(Form, Vec<Printed>)> = Vec::new();
    for form in [Form::Sugared, Form::Explicit] {
        let variant = substituted(written.text, &all, form);
        let (reads, held, again) = reading_back(
            grammar,
            Written {
                path: written.path,
                text: SourceText::from(variant.as_str()),
            },
            &all,
            form,
        );
        for (declaration, why) in held {
            let _first = held_again.entry(declaration).or_insert(why);
        }
        reprinted.push((form, again));
        back = Some(match back {
            Some(before) => before.intersection(&reads).cloned().collect(),
            None => reads,
        });
    }
    let back = back.unwrap_or_default();
    let (read_back, unread): (Vec<&Printed>, Vec<&Printed>) = all
        .into_iter()
        .partition(|declaration| back.contains(&declaration.name));
    // A printing the reading of the variant holds out is held as that
    // reading holds it: the parity cannot read it back as written.
    for declaration in unread {
        match held_again.get(&declaration.name) {
            Some(&why) => holding.push((why, declaration.name.as_str())),
            None => found.misses.push(format!(
                "{name}: `{}` does not lower back to itself",
                declaration.name
            )),
        }
    }
    let parted = apart(grammar, written, &read_back);
    let (held, parted): (Vec<&Printed>, Vec<&Printed>) = read_back
        .into_iter()
        .partition(|declaration| !parted.contains(&declaration.name));
    for declaration in parted {
        holding.push((Held::Apart, declaration.name.as_str()));
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
    let pinned = pinned(grammar, written.text);
    // Each variant's printings by name, by the form substituted into it.
    let again_in = |form: Form| -> BTreeMap<&str, &Printed> {
        reprinted
            .iter()
            .filter(|&&(substituted, _)| substituted == form)
            .flat_map(|&(_, ref again)| again.iter())
            .map(|back| (back.name.as_str(), back))
            .collect()
    };
    let (sugared_again, explicit_again) = (again_in(Form::Sugared), again_in(Form::Explicit));
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
        let expected = pinned.unwrap_or(expected);
        let variant = substituted(written.text, &held, from);
        let out = match formatted(
            grammar,
            Written {
                path: written.path,
                text: SourceText::from(variant.as_str()),
            },
            (into, Selection::Every),
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
        let reformatted = SourceText::from(out.as_str());
        let top = top_level(grammar, reformatted);
        for signed in signed(reformatted, &top) {
            if let Some(ty) =
                out.get(usize::from(signed.ty.start()) .. usize::from(signed.ty.end()))
            {
                drop(signatures.insert(signed.name, tokens(SourceFragment::from(ty))));
            }
        }
        let definitions = defined(reformatted, &top);
        let recursions = recursed(reformatted, &top);
        for declaration in &held {
            // The printer's spelling of the core the variant lowers to: a
            // call the sugared form writes at its read lowers to a nested
            // call, not the bind it elaborates to, and the explicit form
            // keeps it so (#1416).
            let reread = match from {
                Form::Sugared => &sugared_again,
                Form::Explicit => &explicit_again,
            }
            .get(declaration.name.as_str())
            .copied()
            .unwrap_or(declaration);
            let want = |spelled: &Spellings| {
                Some(tokens(SourceFragment::from(spelled.of(expected).as_str())))
            };
            let shown = |tokens: Option<Vec<String>>| {
                tokens.map_or_else(|| String::from("(none)"), |tokens| tokens.join(" "))
            };
            let compared = match reread.shape {
                Shape::Halves { ref ty, ref body } => {
                    let (want_type, want_body) = (want(ty), want(body));
                    let (got_type, got_body) = (
                        signatures.get(&declaration.name).cloned(),
                        definitions.get(&declaration.name).cloned(),
                    );
                    ((got_type.clone(), got_body.clone()) != (want_type.clone(), want_body.clone()))
                        .then(|| {
                            format!(
                                "formatter: {} = {}\n  printer:   {} = {}",
                                shown(got_type),
                                shown(got_body),
                                shown(want_type),
                                shown(want_body),
                            )
                        })
                },
                Shape::Whole(ref whole) => {
                    let (wanted, got) = (want(whole), recursions.get(&declaration.name).cloned());
                    (got != wanted).then(|| {
                        format!("formatter: {}\n  printer:   {}", shown(got), shown(wanted))
                    })
                },
            };
            let Some(compared) = compared
            else {
                continue;
            };
            let mut miss = format!("{name}: `{}` from {from:?} into {into}", declaration.name);
            if let Some(reason) = withdrawn.get(declaration.name.as_str()) {
                core::fmt::Write::write_fmt(&mut miss, format_args!(", withdrawn: {reason}"))
                    .expect("a string accepts every write");
            }
            core::fmt::Write::write_fmt(&mut miss, format_args!(":\n  {compared}"))
                .expect("a string accepts every write");
            found.misses.push(miss);
        }
    }
    found.compared = held.len();
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
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Rotation;
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

    /// The nights the nightly profile takes to compare every source's
    /// declarations: a quarter a night. The whole corpus took 80 s to 147 s on
    /// the nightly runner, the slowest of its sweeps.
    const BODIES_NIGHTS: Nights = Nights(4);

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
        let sources = sweep.visit_rotating(BODIES, BODIES_NIGHTS, &candidates);
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
            report(&total, counted, sweep.rotation());
        }
        let all = total.misses;
        assert!(all.is_empty(), "{} misses:\n{}", all.len(), all.join("\n"));
    }

    /// The report over the sources visited, the whole corpus or the night's
    /// slice of it: the declarations the body parity holds, those it holds
    /// out by issue, and the census of the signatures as written; on standard
    /// error, and in the job's summary under CI.
    ///
    /// # Specification
    /// trivial.
    fn report(
        total: &Bodies,
        counted: Census,
        rotation: Rotation,
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
            "### The formatter at parity with the printer (#755)\n\nOver {}.\n\n| declarations | count |\n| --- | --- |\n{}\n\n| signatures as written | count |\n| --- | --- |\n| as the printer spells them sugared | {} |\n| as the printer spells them explicitly | {} |\n| alike in both forms | {} |\n| as the printer spells them in neither | {} |\n",
            match rotation {
                Rotation::Whole => String::from("the whole corpus"),
                Rotation::Night(_) => format!("the night's quarter of the corpus: {rotation}"),
            },
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
