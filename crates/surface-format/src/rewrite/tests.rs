//! A rewrite's output checked by meaning, from inside the crate, where a
//! rule's output can be mutated before the check reads it.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_grammar::Pbg;
use gandr_surface_layout::PhysicalLineEnding;
use gandr_surface_lowering::Unit;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

use super::Chosen;
use super::Respelled;
use super::Rewrites;
use super::Selection;
use super::respell;
use crate::Form;
use crate::LayoutOptions;
use crate::PageWidth;
use crate::Withdrawal;
use crate::Withdrawn;
use crate::composite::Motives;
use crate::layout;
use crate::leaf;
use crate::leaf::Material;
use crate::leaf::Owner;
use crate::linear::Runs;
use crate::meaning;
use crate::meaning::Agreement;
use crate::meaning::Differing;
use crate::tail::Tails;
use crate::verify_rewritten;

/// A source whose product's operands differ, so swapping them changes what
/// it means.
const SOURCE: &str = "def pair : #{Integer, String} ;\n";

/// The bundled grammar.
///
/// # Specification
/// trivial.
fn grammar() -> Pbg
{
    gandr_surface_grammar::built_in().expect("the built-in grammar builds")
}

/// The product rewrite's output for [`SOURCE`], with its two operands
/// swapped, lowers otherwise, so the check names its declaration for the
/// rewrite's withdrawal; the output as the rule writes it agrees.
#[test]
fn a_rewrite_that_changes_what_a_source_means_is_withdrawn()
{
    let grammar = grammar();
    let parsed = parse(&grammar, SourceText::from(SOURCE))
        .unwrap_or_else(|error| panic!("the source parses: {error}"));
    let tree = parsed.tree();
    let flat = leaf::flatten(&grammar, tree, parsed.obligations());
    let Some(Owner::Form(form)) = flat.leaves.first().map(|leaf| leaf.owner)
    else {
        panic!("the source is one form");
    };
    let chosen = Chosen::of(Form::Sugared, Selection::Every)
        .unwrap_or_else(|| panic!("the sugared form runs rewrites"));
    let motives = Motives::default();
    let tails = Tails::default();
    let runs = Runs::default();
    let rewrites = Rewrites {
        chosen,
        withdrawn: &[],
        motives: &motives,
        tails: &tails,
        runs: &runs,
    };
    let (Respelled::Changed(sugared), _) = respell(&grammar, tree, form, &flat.leaves, rewrites)
    else {
        panic!("the product rewrite applies");
    };
    let mut swapped = sugared.clone();
    let names: Vec<usize> = swapped
        .iter()
        .enumerate()
        .filter(|&(_, leaf)| {
            leaf.material == Material::Token
                && matches!(<&str>::from(leaf.text), "Integer" | "String")
        })
        .map(|(at, _)| at)
        .collect();
    let &[first, second] = names.as_slice()
    else {
        panic!("two operands: {names:?}");
    };
    swapped.swap(first, second);
    let options = LayoutOptions::try_new(
        PageWidth::from(100_u32),
        gandr_surface_layout::ComputationWidth::from(200_u32),
        PhysicalLineEnding::Lf,
    )
    .unwrap_or_else(|error| panic!("the layout options: {error}"));
    let check = |leaves: &[leaf::Leaf<'_>]| {
        let mut text = layout::lay_out(leaves, &options, SourceFragment::from("\n"))
            .unwrap_or_else(|error| panic!("the layout: {error}"));
        text.push('\n');
        let mut arena = CoreArena::new();
        let alone = Unit::single();
        let lowered = meaning::lowered(&grammar, tree, &alone, &mut arena)
            .unwrap_or_else(|| panic!("the source lowers"));
        let verdict = verify_rewritten(
            &grammar,
            (&parsed, leaves, SourceText::from(text.as_str())),
            (SourceText::from(""), &alone),
            (&mut arena, &lowered),
            None,
        );
        (String::from(text.as_str()), verdict)
    };
    let (text, verdict) = check(&sugared);
    assert_eq!(
        (text.as_str(), verdict),
        ("def pair : Integer * String ;\n", Ok(Agreement::Same))
    );
    let (text, verdict) = check(&swapped);
    let (key, span) = tree
        .key(form)
        .zip(tree.node(form).map(gandr_surface_syntax::Node::span))
        .unwrap_or_else(|| panic!("the declaration's form has a key and a span"));
    assert_eq!(
        (text.as_str(), verdict),
        (
            "def pair : String * Integer ;\n",
            Ok(Agreement::Declarations(Vec::from([Differing {
                keys: Vec::from([key]),
                withdrawal: Withdrawal {
                    declaration: String::from("pair"),
                    span,
                    reason: Withdrawn::Lowered,
                },
            }])))
        )
    );
}
