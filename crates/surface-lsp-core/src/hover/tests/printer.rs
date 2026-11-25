//! The hover at a declaration writes the printer's spelling of its type. The
//! editor's session types the text, and the hover reads each declaration at
//! its name. A fresh type table over the same text spells each declaration at
//! the hover's width and style. The hover's first code block equals the name,
//! ` : ` and that spelling. What follows the block is not compared.

use alloc::collections::BTreeMap;
use core::fmt::Write as _;
use std::path::Path;

use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_pretty::PageWidth;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::super::HOVER_WIDTH;
use super::super::hover;
use super::super::hovering;
use super::PLAIN;
use super::checked;
use crate::protocol::SymbolKind;
use crate::reading::Reading;
use crate::toolkit::grammar;

/// The declarations of one source whose hover and printer disagree: each name
/// with the printer's block and the hover's text.
///
/// # Specification
/// - provides: what a test asserts and the sweep reports.
#[repr(transparent)]
#[derive(Debug, Default, Eq, PartialEq)]
struct Departures(BTreeMap<String, String>);

/// The departures of `text`, the source at `path`.
///
/// # Specification
/// - requires: `path` is absolute.
/// - ensures: one entry for each declaration with a key that the printer spells
///   a type for and whose hover does not open on the printer's block, followed
///   by the end of the hover or a blank line; in the outline's order.
/// - provides: the comparison a test and the sweep assert empty.
/// - fails: never.
/// - panics: when the grammar does not build, or a declaration's name starts
///   off a character boundary.
/// - executable: none — the outcome is what the session, the hover and the
///   printer answer, which only a second run of them could restate.
///
/// # Adequacy
/// - hypothesis: L3 — the owner's example and each declaration of the sampled
///   corpus open on the printer's block; a hover that spells the type another
///   way, or adds text before the blank line, is a departure.
/// - witness: `hover::tests::printer::the_owner_s_example_hovers_the_printer_s_block_6263`
/// - witness: `hover::tests::printer::sweeps::every_corpus_declaration_hovers_the_printer_s_spelling`
///
/// # Cost
/// - allocation: the session, the tables and the block's buffer, setup
/// - allocation: each departure's name and text, diagnostic
fn departures(
    text: SourceText<'_>,
    path: &Path,
) -> Departures
{
    let printer = TypeTable::of(grammar().expect("the grammar builds"), text);
    let session = checked(text);
    let reading = Reading::of(text);
    let hovering = hovering(text, path, &session, &gandr_surface_dispatcher::Unshadowed);
    let mut found = Departures::default();
    let (Ok(printer), Maybe::Present(declarations)) = (printer, reading.declarations())
    else {
        return found;
    };
    let mut block = String::new();
    for declaration in declarations {
        // The hover writes a theory and a module as the source writes them.
        let Some(key) = declaration.key.filter(|_| {
            !matches!(
                declaration.symbol.kind,
                SymbolKind::INTERFACE | SymbolKind::MODULE
            )
        })
        else {
            continue;
        };
        let Maybe::Present(Declared::Typed(spelled)) =
            printer.declared(key, PageWidth::from(HOVER_WIDTH), PLAIN.printed())
        else {
            continue;
        };
        let name = declaration.symbol.name.as_str();
        block.clear();
        let _written = write!(block, "```gandr\n{name} : {}\n```", spelled.as_ref());
        let at = declaration.symbol.selection_range.start;
        let shown = hover(text, &session, &reading, &hovering, at, PLAIN);
        let agrees = match shown {
            Maybe::Present(ref shown) => shown
                .contents
                .value
                .strip_prefix(block.as_str())
                .is_some_and(|rest| rest.is_empty() || rest.starts_with("\n\n")),
            Maybe::Absent(_) => false,
        };
        if !agrees {
            let _first = found.0.insert(
                String::from(name),
                format!("the printer writes\n{block}\nthe hover writes\n{shown:?}"),
            );
        }
    }
    found
}

/// The owner's example: `sum` applies `twice` in the call form, and its
/// hover opens on the printer's block, the call form among it.
#[test]
fn the_owner_s_example_hovers_the_printer_s_block_6263()
{
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/classifier/static-beta.gandr");
    let written = std::fs::read_to_string(&path).expect("the example is read");
    assert_eq!(
        departures(SourceText::from(written.as_str()), &path),
        Departures::default()
    );
}

/// The sweep over the declarations of the corpus. Under a pull-request
/// profile it visits the sample below and each source the change adds or
/// modifies. Under `nightly` it visits the night's slice, and under `sweeps`
/// each source.
mod sweeps
{
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Rotation;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::SourceText;
    use super::departures;

    /// The sample: seven sources, as the tile sweep draws, within the suite's
    /// bound of a second for each test.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_corpus_declaration_hovers_the_printer_s_spelling"),
        size: SampleSize(7),
    };

    /// The nights the nightly profile takes to visit each source, as the tile
    /// sweep takes.
    const NIGHTS: Nights = Nights(7);

    /// The departures the corpus owes, each as its source and its declaration.
    /// The hover renames a parameter of a declaration that the checker
    /// refuses, owed by gandr #8310.
    const OWED: [(&str, &str); 1] = [("fixture/model/basics/literal-identity.gandr", "held")];

    /// Whether a run judges an owed departure that departs no more.
    ///
    /// # Specification
    /// - provides: the half of the verdict that a whole run alone can give.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Settled
    {
        /// The run visits each source, so an owed site that agrees is settled.
        Judged,
        /// The run visits a part, so an owed site may stand outside it.
        Unjudged,
    }

    /// No declaration of the corpus hovers a type that the printer does not
    /// write, but the owed ones.
    #[test]
    fn every_corpus_declaration_hovers_the_printer_s_spelling()
    {
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let settled = if sweep.coverage() == Coverage::Full && sweep.rotation() == Rotation::Whole {
            Settled::Judged
        }
        else {
            Settled::Unjudged
        };
        hovers_the_printer(&sweep, settled);
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn every_corpus_declaration_hovers_the_printer_s_spelling_changed()
    {
        hovers_the_printer(
            &Sweep::asked().expect("the run's sweep resolves").changed(),
            Settled::Unjudged,
        );
    }

    /// Each declaration of each source `sweep` visits hovers the printer's
    /// block, or [`OWED`] holds it. When `settled` is judged, each owed
    /// declaration still departs.
    ///
    /// # Specification
    /// trivial.
    fn hovers_the_printer(
        sweep: &Sweep,
        settled: Settled,
    )
    {
        eprintln!("{}", sweep.rotation());
        let sources = sweep.visit_rotating(
            SAMPLE,
            NIGHTS,
            &corpus::sources().expect("the corpus reads"),
        );
        let mut refused = Vec::new();
        let mut departing = Vec::new();
        for source in &sources {
            let written = std::fs::read_to_string(&source.path).expect("a corpus source is read");
            for (name, departure) in departures(SourceText::from(written.as_str()), &source.path).0
            {
                let site = (source.name.as_ref(), name.as_str());
                if OWED.contains(&site) {
                    departing.push((source.name.as_ref().to_owned(), name));
                }
                else {
                    refused.push(format!("{}: `{name}`: {departure}", source.name));
                }
            }
        }
        if settled == Settled::Judged {
            refused.extend(
                OWED.iter()
                    .filter(|&&(source, name)| {
                        !departing
                            .iter()
                            .any(|&(ref at, ref held)| at == source && held == name)
                    })
                    .map(|&(source, name)| {
                        format!(
                            "{source}: `{name}` hovers the printer's block; take it out of OWED"
                        )
                    }),
            );
        }
        assert!(
            refused.is_empty(),
            "{} declarations disagree with the printer and with OWED:\n{}",
            refused.len(),
            refused.join("\n\n")
        );
    }
}
