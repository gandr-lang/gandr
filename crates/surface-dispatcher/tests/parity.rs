//! The formatter at token parity with the printer (#755): for each
//! declaration a corpus source signs `def name : T ;`, the printer spells
//! its type in the sugared and the explicit form, and the formatter, given
//! the source with that signature written in one form, writes it in the
//! other exactly as the printer does, and keeps it in its own. Tokens are
//! compared, never bytes: the two lay out apart.

use alloc::collections::BTreeMap;
use std::path::Path;

use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_format::Beside;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::format_beside;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
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

/// `written` formatted into `form` beside the siblings it imports.
///
/// # Specification
/// trivial.
fn formatted(
    grammar: &Pbg,
    written: Written<'_>,
    form: gandr_surface_format::Form,
) -> Result<String, String>
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
        .map(gandr_surface_format::Formatted::into_text)
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
            Ok(out) => out,
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

/// The parity sweep: a sample on every pull request, every source under the
/// `sweeps` profile.
mod sweeps
{
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::Written;
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
}
