//! The exemplar harvester: for every rule of the built-in grammar, the
//! smallest top-level corpus form whose tree holds one of the rule's molds,
//! and for every registered attribute the smallest attribute block naming it
//! with the form it decorates.
//!
//! Run with `cargo run -p gandr-surface-dispatcher --example
//! harvest_exemplars -- <corpus directory> <seed directory>`. Each seed is
//! written to `<seed directory>/syntax/<rule>.gandr` or
//! `<seed directory>/attributes/<name>.gandr`, opening with a comment naming
//! the source it was cut from; the rules and attributes no corpus source
//! exercises are printed, one per line. A seed is where an exemplar starts:
//! the exemplar under `ledger/exemplars/` is the seed cut down by hand to the
//! smallest item that still shows its rule, which `gandr ledger exemplars`
//! verifies.
//!
//! Only sources that parse with no obligation are read, so a seed never
//! carries grout.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::AttributeRegistry;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

/// Why a harvest stopped; `main` prints it through `Debug`.
enum Failure
{
    /// The invocation names no corpus or no seed directory.
    Usage,
    /// The built-in grammar did not build.
    Grammar(PbgError),
    /// A file or directory could not be read or written.
    Io(PathBuf, std::io::Error),
    /// Standard output could not be written.
    Output(std::io::Error),
}

impl core::fmt::Debug for Failure
{
    /// Writes the failure as a sentence.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Usage => {
                f.write_str("usage: harvest_exemplars <corpus directory> <seed directory>")
            },
            Self::Grammar(ref error) => write!(f, "the built-in grammar: {error}"),
            Self::Io(ref path, ref error) => write!(f, "{}: {error}", path.display()),
            Self::Output(ref error) => write!(f, "standard output: {error}"),
        }
    }
}

/// The smallest corpus text found so far for one rule or attribute.
#[derive(Clone, Debug)]
struct Seed
{
    /// Where it was cut from, as `path:line`.
    origin: String,
    /// The text.
    text: String,
}

impl Seed
{
    /// Keep `candidate` in `slot` when it is shorter than what the slot
    /// holds, or the slot is empty.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        slot: &mut BTreeMap<String, Self>,
        key: String,
        candidate: Self,
    )
    {
        let shorter = slot
            .get(&key)
            .is_none_or(|held| candidate.text.len() < held.text.len());
        if shorter {
            let _previous = slot.insert(key, candidate);
        }
    }
}

/// Every `.gandr` file under `root`, in byte order of their paths.
///
/// # Specification
/// trivial.
fn sources(root: &Path) -> Result<Vec<PathBuf>, Failure>
{
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let entries =
            std::fs::read_dir(&directory).map_err(|error| Failure::Io(directory.clone(), error))?;
        for entry in entries {
            let path = entry
                .map_err(|error| Failure::Io(directory.clone(), error))?
                .path();
            if path.is_dir() {
                pending.push(path);
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                found.push(path);
            }
        }
    }
    found.sort();
    Ok(found)
}

/// The rules whose molds the tiles under `form` carry.
///
/// # Specification
/// trivial.
fn rules_under(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    form: NodeIndex,
) -> Vec<RuleName>
{
    let mut rules = Vec::new();
    let mut seen = BTreeSet::new();
    let mut pending = vec![form];
    while let Some(position) = pending.pop() {
        if let Some(node) = tree.node(position)
            && let NodeLabel::Tile(mold) | NodeLabel::Meld(mold) = node.label()
            && let Ok(rule) = pbg.rule_of(mold)
        {
            let name = RuleName(rule.name);
            if seen.insert(name) {
                rules.push(name);
            }
        }
        pending.extend(tree.children(position));
    }
    rules
}

/// Write each seed of `seeds` under `directory`, one file per key.
///
/// # Specification
/// trivial.
fn written(
    directory: &Path,
    seeds: &BTreeMap<String, Seed>,
) -> Result<(), Failure>
{
    std::fs::create_dir_all(directory)
        .map_err(|error| Failure::Io(directory.to_path_buf(), error))?;
    for (key, seed) in seeds {
        let path = directory.join(format!("{key}.gandr"));
        let text = format!("// seed: {}\n{}\n", seed.origin, seed.text);
        std::fs::write(&path, text).map_err(|error| Failure::Io(path, error))?;
    }
    Ok(())
}

/// Harvest the corpus named by the first argument into the directory the
/// second names.
///
/// # Specification
/// trivial.
fn main() -> Result<(), Failure>
{
    let mut arguments = std::env::args_os().skip(1);
    let (Some(corpus), Some(out)) = (arguments.next(), arguments.next())
    else {
        return Err(Failure::Usage);
    };
    let (corpus, out) = (PathBuf::from(corpus), PathBuf::from(out));
    let pbg = built_in().map_err(Failure::Grammar)?;
    let attribute_names: Vec<String> = AttributeRegistry::names()
        .into_iter()
        .map(|name| name.to_string())
        .collect();
    let mut syntax: BTreeMap<String, Seed> = BTreeMap::new();
    let mut attributes: BTreeMap<String, Seed> = BTreeMap::new();
    let mut skipped = 0_usize;
    let mut origin = String::new();
    for path in sources(&corpus)? {
        let text =
            std::fs::read_to_string(&path).map_err(|error| Failure::Io(path.clone(), error))?;
        let Ok(parsed) = parse(&pbg, SourceText::from(text.as_str()))
        else {
            skipped = skipped.saturating_add(1);
            continue;
        };
        if !parsed.obligations().is_empty() {
            skipped = skipped.saturating_add(1);
            continue;
        }
        let tree = parsed.tree();
        let forms = tree.forms();
        for (slot, &form) in forms.iter().enumerate() {
            let (Some(fragment), Some(node)) = (tree.fragment(form), tree.node(form))
            else {
                continue;
            };
            let start = usize::from(node.span().start());
            let line = text
                .get(.. start)
                .map_or(0, |before| before.matches('\n').count())
                .saturating_add(1);
            origin.clear();
            // Formatting into a `String` cannot fail.
            let _written =
                core::fmt::Write::write_fmt(&mut origin, format_args!("{}:{line}", path.display()));
            let form_text = <&str>::from(fragment).to_owned();
            for rule in rules_under(&pbg, tree, form) {
                Seed::keep(&mut syntax, rule.0.to_owned(), Seed {
                    origin: origin.clone(),
                    text: form_text.clone(),
                });
            }
            if let Some(block) = form_text.strip_prefix("@[") {
                let decorated = forms
                    .get(slot.saturating_add(1))
                    .and_then(|&next| tree.fragment(next))
                    .map_or("", <&str>::from);
                for name in &attribute_names {
                    let named = block
                        .split(|character: char| !(character.is_alphanumeric() || character == '_'))
                        .any(|word| word == name);
                    if named {
                        Seed::keep(&mut attributes, name.clone(), Seed {
                            origin: origin.clone(),
                            text: format!("{form_text}\n{decorated}"),
                        });
                    }
                }
            }
        }
    }
    written(&out.join("syntax"), &syntax)?;
    written(&out.join("attributes"), &attributes)?;
    let mut stdout = std::io::stdout().lock();
    writeln!(
        stdout,
        "skipped {skipped} sources with obligations or a parse fault"
    )
    .map_err(Failure::Output)?;
    for rule in pbg.rules() {
        if !syntax.contains_key(rule.name) {
            writeln!(stdout, "unexercised rule: {}", rule.name).map_err(Failure::Output)?;
        }
    }
    for name in &attribute_names {
        if !attributes.contains_key(name) {
            writeln!(stdout, "unexercised attribute: {name}").map_err(Failure::Output)?;
        }
    }
    Ok(())
}
