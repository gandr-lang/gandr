//! The syntax exemplars and their verification.
//!
//! # One exemplar per committed rule and per attribute
//!
//! An exemplar is one small source showing one form: `syntax/<rule>.gandr`
//! for every committed rule of the syntax ledger, `attributes/<name>.gandr`
//! for every registered attribute. A file is named for what it shows, so the
//! set of files and the set of rules are compared by name, and a failure
//! names its file. [`verify`] reads the exemplar directory and reports, per
//! file, the first thing that does not hold:
//!
//! - the file exists for its rule or attribute, and names one;
//! - it opens with a `///` comment naming its rule or attribute in backticks;
//! - it parses with no obligation left;
//! - a rule's exemplar holds one item of its rule: one top-level form, besides
//!   attribute blocks, holding a tile the rule molds or the head a glyph of it
//!   is spelled with in ASCII; a rule holding a glyph tile holds two, one per
//!   spelling;
//! - its tree holds a tile molded by its rule, or, for an attribute, the source
//!   lowers, no declaration is refused and the attribute is filed on one. The
//!   `doc` attribute is filed as documentation, so its exemplar's declaration
//!   must carry documentation beyond the opening comment's lines;
//! - a glyph rule's exemplar writes each spelling the spelling table gives: a
//!   tile of the rule written as the glyph, and one written as its ASCII token,
//!   or, for a glyph the table pairs with a head, a call of the head. The table
//!   is the one the labeler reads, so an ASCII spelling added to it fails here
//!   until its exemplar writes it.
//!
//! An exemplar may hold, besides the items it shows, the declarations those
//! items name: an attribute's payload names a world (`entry`) or a law
//! (`respects`), and a rule's item may name a world, an effect, a theory or a
//! module. The lowering refuses a name nothing declares, and the exemplar must
//! settle. A world is no module member, so wrapping both in one module is not
//! an option. Only the items holding the rule's tiles are counted.
//!
//! - Choice: count the forms holding a tile of the rule, so context is free and
//!   a second showing of the form is still a finding.
//! - Alternatives: one top-level form in all, which leaves an item naming a
//!   world unable to settle; a refusal stated for the missing name, which
//!   describes the exemplar, not the form.
//! - Reversal: none needed while context cannot mold the rule; a context
//!   declaration that does is a second item and fails.
//!
//! An internal rule has no exemplar: no source molds it.
//!
//! - Choice: the mold check reads the committed tree, so an exemplar holding
//!   another rule's form that happens to share a spelling fails.
//! - Alternatives: comparing each exemplar with a stored tree digest, which
//!   pins incidental layout; checking only that a file parses, which a file
//!   showing the wrong rule passes.
//! - Reversal: a rule that can only be shown inside a larger form still passes,
//!   since the check asks for a mold of the rule, not for the rule at the root.
//!
//! The exemplars are seeded by the `harvest_exemplars` example, which finds
//! the smallest corpus form whose tree holds each rule's molds; each is then
//! cut down by hand.
//!
//! # Every exemplar settles
//!
//! The `ledger` directory is a fixture root (the `root` module), so `mise run
//! check:exemplars` settles every exemplar under `gandr test`: each declaration
//! states what the checker makes of it, `checks`, `runs` or `normalizes` where
//! it holds and `refuses` naming the refusal where the checker does not reach
//! the form yet. Such an expectation breaks when the checker grows, and the
//! exemplar's comment names the issue that would settle it.
//!
//! # Features exemplars exhibit
//!
//! The `features` directory holds programs, one for each row of the features
//! ledger no corpus fixture shows; the features ledger's own gate pairs files
//! with rows. A features exemplar shows what holds, so [`verify`] holds each
//! expectation it states to the strict root's admission, though the directory
//! sits under the fixture root: `owes` and `refuses` are findings there.
//!
//! # Diagnostics exemplars refuse
//!
//! The `diagnostics` directory holds one source per refusal name, each
//! stating `refuses` with its name, or the name's row in a table of what is
//! owed and why; the `diagnostics` module states the pairing.

mod diagnostics;

use alloc::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::ExpectationSchema;
use gandr_surface_grammar::Ascii;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::SPELLED;
use gandr_surface_grammar::Spelled;
use gandr_surface_lowering::AttributeRegistry;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::RegisteredAttribute;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use super::LedgerFault;

/// The directory of rule exemplars under the exemplar directory.
const SYNTAX: &str = "syntax";

/// The directory of attribute exemplars under the exemplar directory.
const ATTRIBUTES: &str = "attributes";

/// The directory of features exemplars under the exemplar directory.
const FEATURES: &str = "features";

/// The extension every exemplar carries.
const EXTENSION: &str = "gandr";

/// The rule an attribute block is a form of: an exemplar's item is the one form
/// besides its attribute blocks.
const ATTRIBUTE_BLOCK: RuleName = RuleName("attribute_block");

/// What an exemplar shows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Subject
{
    /// A committed rule of the grammar.
    Rule(RuleName),
    /// A registered attribute.
    Attribute(RegisteredAttribute),
}

impl core::fmt::Display for Subject
{
    /// Writes `rule `name`` or `attribute `name``.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Rule(rule) => write!(f, "rule `{rule}`"),
            Self::Attribute(name) => write!(f, "attribute `{name}`"),
        }
    }
}

impl Subject
{
    /// The name the subject's file and comment carry.
    ///
    /// # Specification
    /// trivial.
    fn name(self) -> String
    {
        match self {
            Self::Rule(rule) => rule.to_string(),
            Self::Attribute(name) => name.to_string(),
        }
    }
}

/// Why one exemplar does not show what its name says.
#[derive(Debug)]
pub enum ExemplarFault
{
    /// No file exists for the rule or attribute.
    Missing
    {
        /// What has no exemplar.
        subject: String,
    },
    /// The file names nothing the ledger lists: no committed rule, registered
    /// attribute or refusal; or it is not an exemplar source.
    Stray,
    /// The file could not be read.
    Unreadable(std::io::Error),
    /// The parser could not commit the source.
    Unparsed
    {
        /// The parser's account.
        error: String,
    },
    /// The file does not open with a `///` comment naming what it shows.
    Uncommented
    {
        /// What the comment should name.
        subject: String,
    },
    /// The parse left obligations.
    Obligations
    {
        /// How many.
        count: usize,
    },
    /// A rule's exemplar holds another number of items of its rule than it
    /// shows spellings.
    Items
    {
        /// How many top-level forms besides attribute blocks hold a tile of
        /// the rule.
        count: usize,
        /// How many it should hold: one per spelling.
        expected: usize,
    },
    /// A glyph rule's exemplar does not write one of its spellings.
    Unwritten
    {
        /// The rule.
        rule: String,
        /// The text no tile of the rule is written with.
        spelling: &'static str,
    },
    /// The tree holds no tile its rule molds.
    Unmolded
    {
        /// The rule.
        rule: String,
    },
    /// The lowering refused the source or one of its declarations.
    Refused
    {
        /// The lowering's account.
        refusal: String,
    },
    /// The attribute was filed on no declaration.
    Unfiled
    {
        /// The attribute.
        attribute: String,
    },
    /// A features exemplar states an expectation the strict root refuses.
    Unexhibited
    {
        /// The expectation.
        schema: ExpectationSchema,
    },
    /// A diagnostics exemplar holds no declaration refused with its subject.
    Unrefused
    {
        /// The refusal or boundary.
        subject: String,
    },
    /// The owed table lists a subject that has an exemplar.
    Owed
    {
        /// The refusal or boundary.
        subject: String,
    },
    /// The owed table lists a name no refusal or boundary carries.
    Unowed,
}

impl core::fmt::Display for ExemplarFault
{
    /// Writes the fault as a sentence fragment.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fragment per fault, naming what it carries: the subject,
    ///   the rule, the spelling, the attribute, the expectation, the count.
    /// - fails: a failed write.
    /// - panics: none.
    /// - executable: none — the fragment is written into a formatter no
    ///   predicate reads back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each fault a witness provokes is printed beside its
    ///   file and compared whole. The wording is the report's, not pinned
    ///   beyond those findings.
    /// - witness: `ledger::exemplars::tests::each_check_names_its_file`
    /// - witness: `ledger::exemplars::tests::a_features_exemplar_states_only_what_holds`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Missing { ref subject } => write!(f, "no exemplar for {subject}"),
            Self::Stray => f.write_str("names nothing the ledger lists"),
            Self::Unreadable(ref error) => write!(f, "cannot read: {error}"),
            Self::Unparsed { ref error } => write!(f, "does not parse: {error}"),
            Self::Uncommented { ref subject } => {
                write!(f, "does not open with a `///` comment naming {subject}")
            },
            Self::Obligations { count } => write!(f, "parses with {} left", super::Counted {
                count,
                noun: "obligation"
            }),
            Self::Items { count, expected } => {
                write!(
                    f,
                    "holds {} of its rule where it shows {expected}",
                    super::Counted {
                        count,
                        noun: "item"
                    }
                )
            },
            Self::Unwritten { ref rule, spelling } => {
                write!(f, "writes no tile of rule `{rule}` as `{spelling}`")
            },
            Self::Unmolded { ref rule } => {
                write!(f, "its tree holds no tile molded by rule `{rule}`")
            },
            Self::Refused { ref refusal } => write!(f, "the lowering refuses it: {refusal}"),
            Self::Unfiled { ref attribute } => {
                write!(f, "the attribute `{attribute}` is filed on no declaration")
            },
            Self::Unexhibited { schema } => {
                write!(
                    f,
                    "states `{schema}`, but a features exemplar shows what holds"
                )
            },
            Self::Unrefused { ref subject } => {
                write!(f, "no declaration is refused with {subject}")
            },
            Self::Owed { ref subject } => {
                write!(f, "the owed table lists {subject}, which has an exemplar")
            },
            Self::Unowed => f.write_str("the owed table lists a name no refusal carries"),
        }
    }
}

/// One exemplar that does not hold, by its path.
#[derive(Debug)]
pub struct ExemplarFinding
{
    /// The file, or where the missing file belongs.
    path: PathBuf,
    /// What does not hold.
    fault: ExemplarFault,
}

impl ExemplarFinding
{
    /// The file the finding names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn path(&self) -> &Path
    {
        &self.path
    }

    /// What does not hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fault(&self) -> &ExemplarFault
    {
        &self.fault
    }
}

impl core::fmt::Display for ExemplarFinding
{
    /// Writes `<path>: <fault>`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "{}: {}", self.path.display(), self.fault)
    }
}

/// What a verification of the exemplar directory found.
#[derive(Debug)]
pub struct ExemplarReport
{
    /// How many syntax and attribute exemplars held.
    verified: usize,
    /// How many features exemplars stated only what the strict root admits.
    exhibited: usize,
    /// How many diagnostics exemplars refused with their subject.
    diagnosed: usize,
    /// How many refusals the owed table lists without an exemplar.
    owed: usize,
    /// Every exemplar that did not, in the order verified: rules in grammar
    /// order, then attributes in registry order, then stray files; then the
    /// diagnostics exemplars in subject order, the table's stray rows and the
    /// stray files.
    findings: Vec<ExemplarFinding>,
}

impl ExemplarReport
{
    /// Every exemplar that did not hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn findings(&self) -> &[ExemplarFinding]
    {
        &self.findings
    }
}

impl core::fmt::Display for ExemplarReport
{
    /// Writes `N exemplars verified, K features exemplars exhibiting, D
    /// diagnostics exemplars refusing, O owed, M findings`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the five counts, in that order.
    /// - fails: a failed write.
    /// - panics: none.
    /// - executable: none — the counts are written into a formatter no
    ///   predicate reads back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run with every count nonzero is printed whole.
    /// - witness: `ledger::exemplars::tests::a_features_exemplar_states_only_what_holds`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{} verified, {} exhibiting, {} refusing, {} owed, {}",
            super::Counted {
                count: self.verified,
                noun: "exemplar"
            },
            super::Counted {
                count: self.exhibited,
                noun: "features exemplar"
            },
            super::Counted {
                count: self.diagnosed,
                noun: "diagnostics exemplar"
            },
            self.owed,
            super::Counted {
                count: self.findings.len(),
                noun: "finding"
            }
        )
    }
}

/// Verify the exemplars under `directory` against the committed rules
/// `rules` of `pbg`, the attribute registry and the refusal vocabulary.
///
/// # Specification
/// - requires: `rules` are the committed rules of `pbg`, in grammar order.
/// - ensures: a finding for every rule and attribute without a file, for every
///   file naming neither, and for every exemplar whose first failing check is
///   named; every other exemplar counts as verified. Every features exemplar
///   stating only what the strict root admits counts as exhibiting, and every
///   other is a finding, as is a file there that is no source. The diagnostics
///   exemplars and the owed table are verified as the `diagnostics` module
///   states. A missing `syntax`, `attributes`, `features` or `diagnostics`
///   directory reads as empty.
/// - provides: `gandr ledger exemplars <directory>`.
/// - fails: a directory that exists and cannot be listed.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Unreadable`] naming the directory.
///
/// # Adequacy
/// - hypothesis: L3 — the committed exemplars verify with no finding; a renamed
///   exemplar is two findings, its rule missing and its file stray; an exemplar
///   replaced by another rule's form fails the mold check; an uncommented,
///   two-item or grouted exemplar fails by name; a features exemplar stating
///   `owes` or `refuses` is a finding.
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
/// - witness: `ledger::exemplars::tests::a_renamed_exemplar_breaks_the_bijection`
/// - witness: `ledger::exemplars::tests::an_exemplar_of_another_form_lacks_the_mold`
/// - witness: `ledger::exemplars::tests::each_check_names_its_file`
/// - witness: `ledger::exemplars::tests::a_features_exemplar_states_only_what_holds`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |report| report.verified <= rules.len().saturating_add(AttributeRegistry::names().len())))]
pub(super) fn verify(
    pbg: &Pbg,
    rules: &[RuleName],
    directory: &Path,
) -> Result<ExemplarReport, LedgerFault>
{
    let mut report = ExemplarReport {
        verified: 0,
        exhibited: 0,
        diagnosed: 0,
        owed: 0,
        findings: Vec::new(),
    };
    let subjects = [
        (
            directory.join(SYNTAX),
            rules
                .iter()
                .map(|&rule| Subject::Rule(rule))
                .collect::<Vec<_>>(),
        ),
        (
            directory.join(ATTRIBUTES),
            AttributeRegistry::names()
                .into_iter()
                .map(Subject::Attribute)
                .collect(),
        ),
    ];
    for (folder, expected) in subjects {
        let mut present = listed(&folder)?;
        for subject in expected {
            let path = folder.join(format!("{}.{EXTENSION}", subject.name()));
            if !present.remove(&path) {
                report.findings.push(ExemplarFinding {
                    path,
                    fault: ExemplarFault::Missing {
                        subject: subject.to_string(),
                    },
                });
                continue;
            }
            match exemplar(pbg, &path, subject) {
                Ok(()) => report.verified = report.verified.saturating_add(1),
                Err(fault) => report.findings.push(ExemplarFinding { path, fault }),
            }
        }
        report
            .findings
            .extend(present.into_iter().map(|path| ExemplarFinding {
                path,
                fault: ExemplarFault::Stray,
            }));
    }
    for path in listed(&directory.join(FEATURES))? {
        let source = path
            .extension()
            .is_some_and(|extension| extension == EXTENSION);
        let exhibited = if source {
            exhibits(pbg, &path)
        }
        else {
            Err(ExemplarFault::Stray)
        };
        match exhibited {
            Ok(()) => report.exhibited = report.exhibited.saturating_add(1),
            Err(fault) => report.findings.push(ExemplarFinding { path, fault }),
        }
    }
    diagnostics::verify(pbg, &directory.join(diagnostics::DIAGNOSTICS), &mut report)?;
    Ok(report)
}

/// Every entry of `folder`, by path; nothing when the folder does not exist.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one path per entry of `folder`.
/// - fails: a folder that exists and cannot be listed, or an entry that cannot
///   be read.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Unreadable`] naming the folder.
///
/// # Adequacy
/// - hypothesis: L3 — the committed folders list every exemplar, and a stray
///   file is listed.
/// - witness: `ledger::exemplars::tests::a_renamed_exemplar_breaks_the_bijection`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |paths| paths.iter().all(|path| path.starts_with(folder))))]
pub(super) fn listed(folder: &Path) -> Result<BTreeSet<PathBuf>, LedgerFault>
{
    let unreadable = |error| LedgerFault::Unreadable {
        path: folder.to_path_buf(),
        error,
    };
    if !folder.try_exists().map_err(unreadable)? {
        return Ok(BTreeSet::new());
    }
    let entries = std::fs::read_dir(folder).map_err(unreadable)?;
    let mut paths = BTreeSet::new();
    for entry in entries {
        let _new = paths.insert(entry.map_err(unreadable)?.path());
    }
    Ok(paths)
}

/// Verify the one exemplar at `path` shows `subject`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when the file reads, opens with a comment naming the
///   subject, parses with no obligation, holds one item of its rule per
///   spelling (context declarations beside them are free), holds a tile of the
///   subject's rule or files the subject's attribute, and writes each spelling
///   of a glyph rule.
/// - fails: the first check that does not hold.
/// - panics: none.
///
/// # Errors
/// The [`ExemplarFault`] of the first check that does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — each check is broken alone by a witness and named.
/// - witness: `ledger::exemplars::tests::each_check_names_its_file`
/// - witness: `ledger::exemplars::tests::an_exemplar_of_another_form_lacks_the_mold`
/// - witness: `ledger::exemplars::tests::a_glyph_exemplar_writes_both_spellings`
#[spec(ensures: |ref ret| ret.is_ok() || !matches!(*ret, Err(ExemplarFault::Missing { .. } | ExemplarFault::Stray)))]
fn exemplar(
    pbg: &Pbg,
    path: &Path,
    subject: Subject,
) -> Result<(), ExemplarFault>
{
    let text = std::fs::read_to_string(path).map_err(ExemplarFault::Unreadable)?;
    let named = format!("`{}`", subject.name());
    let commented = text
        .lines()
        .next()
        .is_some_and(|first| first.starts_with("///") && first.contains(&named));
    if !commented {
        return Err(ExemplarFault::Uncommented {
            subject: subject.to_string(),
        });
    }
    let parsed =
        parse(pbg, SourceText::from(text.as_str())).map_err(|error| ExemplarFault::Unparsed {
            error: error.to_string(),
        })?;
    let count = parsed.obligations().len();
    if count != 0 {
        return Err(ExemplarFault::Obligations { count });
    }
    let tree = parsed.tree();
    let glyphs = match subject {
        Subject::Rule(rule) => glyphs_of(pbg, rule),
        Subject::Attribute(_) => Vec::new(),
    };
    if let Subject::Rule(rule) = subject {
        molded(pbg, tree, rule)?;
        // A form shows the rule when a tile inside it is molded by the rule or
        // written as the head one of its glyphs is spelled with in ASCII; any
        // other form is context the items name.
        let shows = |form| {
            tree.node(form)
                .map(gandr_surface_syntax::Node::span)
                .is_some_and(|outer| {
                    tree.positions().any(|position| {
                        tree.node(position).is_some_and(|node| {
                            matches!(node.label(), NodeLabel::Tile(_))
                                && node.span().start() >= outer.start()
                                && node.span().end() <= outer.end()
                        }) && (rule_of(pbg, tree, position) == Maybe::Present(rule)
                            || tree.fragment(position).is_some_and(|fragment| {
                                glyphs.iter().any(|entry| {
                                    matches!(entry.ascii, Ascii::Head(head) if head.0 == <&str>::from(fragment))
                                })
                            }))
                    })
                })
        };
        let items = tree
            .forms()
            .iter()
            .filter(|&&form| {
                rule_of(pbg, tree, form) != Maybe::Present(ATTRIBUTE_BLOCK)
                    && (rule == ATTRIBUTE_BLOCK || shows(form))
            })
            .count();
        let expected = if glyphs.is_empty() { 1 } else { 2 };
        if items != expected {
            return Err(ExemplarFault::Items {
                count: items,
                expected,
            });
        }
    }
    let header = Header {
        lines: text
            .lines()
            .take_while(|line| line.starts_with("///"))
            .count(),
    };
    match subject {
        Subject::Rule(rule) => written(pbg, tree, rule, &glyphs),
        Subject::Attribute(attribute) => filed(pbg, tree, attribute, header),
    }
}

/// Verify the features exemplar at `path` states only what the strict root
/// admits.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when the file reads, parses, lowers, and no
///   attribute filed on its declarations states an expectation the strict root
///   refuses.
/// - fails: the first check that does not hold.
/// - panics: none.
///
/// # Errors
/// [`ExemplarFault::Unreadable`], [`ExemplarFault::Unparsed`],
/// [`ExemplarFault::Refused`] or [`ExemplarFault::Unexhibited`].
///
/// # Adequacy
/// - hypothesis: L3 — the committed features exemplars hold; one stating
///   `refuses` and one stating `owes` are findings naming the expectation.
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
/// - witness: `ledger::exemplars::tests::a_features_exemplar_states_only_what_holds`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(ExemplarFault::Unreadable(_) | ExemplarFault::Unparsed { .. } | ExemplarFault::Refused { .. } | ExemplarFault::Unexhibited { .. })))]
fn exhibits(
    pbg: &Pbg,
    path: &Path,
) -> Result<(), ExemplarFault>
{
    let text = std::fs::read_to_string(path).map_err(ExemplarFault::Unreadable)?;
    let parsed =
        parse(pbg, SourceText::from(text.as_str())).map_err(|error| ExemplarFault::Unparsed {
            error: error.to_string(),
        })?;
    let mut arena = CoreArena::new();
    let module = lower_module(
        pbg,
        parsed.tree(),
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .map_err(|refusal| ExemplarFault::Refused {
        refusal: refusal.to_string(),
    })?;
    for declaration in module.declarations() {
        for key in [declaration.signature(), declaration.definition()] {
            let Maybe::Present(key) = key
            else {
                continue;
            };
            for entry in module.attributes().entries(key) {
                if let Maybe::Present(schema) = ExpectationSchema::of(entry.name())
                    && CorpusRoot::Strict.admit(schema, entry.span()).is_err()
                {
                    return Err(ExemplarFault::Unexhibited { schema });
                }
            }
        }
    }
    Ok(())
}

/// The rule whose mold labels the node at `position`, when a mold does.
///
/// # Specification
/// trivial.
fn rule_of(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    position: gandr_surface_syntax::NodeIndex,
) -> Maybe<RuleName, ()>
{
    let Some(node) = tree.node(position)
    else {
        return Maybe::Absent(());
    };
    match node.label() {
        NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
            pbg.rule_of(mold).map_or(Maybe::Absent(()), |rule| {
                Maybe::Present(RuleName(rule.name))
            })
        },
        NodeLabel::Wald
        | NodeLabel::Grout { .. }
        | NodeLabel::GhostClose { .. }
        | NodeLabel::Space
        | NodeLabel::Doc => Maybe::Absent(()),
    }
}

/// The spelling table's entries for the glyph tiles `rule` molds, in table
/// order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each [`SPELLED`] entry whose tile labels a mold of `rule`, once.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the glyph rules' exemplars are held to two items and a
///   rule with no glyph to one.
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
/// - witness: `ledger::exemplars::tests::a_glyph_exemplar_writes_both_spellings`
#[spec(ensures: |ret| ret.iter().all(|entry| SPELLED.contains(entry)))]
fn glyphs_of(
    pbg: &Pbg,
    rule: RuleName,
) -> Vec<Spelled>
{
    SPELLED
        .iter()
        .copied()
        .filter(|entry| {
            pbg.iter_molds().any(|(mold, def)| {
                def.label == entry.tile.0
                    && pbg
                        .rule_of(mold)
                        .is_ok_and(|owner| RuleName(owner.name) == rule)
            })
        })
        .collect()
}

/// Whether `tree` writes each spelling of `glyphs`: a tile of `rule`
/// written as the glyph, and one written as the ASCII token or, for a head,
/// a tile written as the head.
///
/// # Specification
/// - requires: `glyphs` are [`glyphs_of`] `rule`.
/// - ensures: `Ok` exactly when every spelling of every entry is written.
/// - fails: the first spelling no tile is written with, glyph before ASCII.
/// - panics: none.
///
/// # Errors
/// [`ExemplarFault::Unwritten`] naming the rule and the spelling.
///
/// # Adequacy
/// - hypothesis: L3 — the committed glyph exemplars write both; one with its
///   ASCII item respelled as the glyph lacks the token, and the isomorphism's
///   without its call lacks the head.
/// - witness: `ledger::exemplars::tests::a_glyph_exemplar_writes_both_spellings`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(ExemplarFault::Unwritten { .. })))]
fn written(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    rule: RuleName,
    glyphs: &[Spelled],
) -> Result<(), ExemplarFault>
{
    let tile_written = |label: &str, text: &str, of_rule: bool| {
        tree.positions().any(|position| {
            let Some(node) = tree.node(position)
            else {
                return false;
            };
            let NodeLabel::Tile(mold) = node.label()
            else {
                return false;
            };
            pbg.mold(mold).is_ok_and(|def| def.label == label)
                && (!of_rule || rule_of(pbg, tree, position) == Maybe::Present(rule))
                && tree
                    .fragment(position)
                    .is_some_and(|fragment| <&str>::from(fragment) == text)
        })
    };
    for entry in glyphs {
        let glyph = entry.tile.0;
        if !tile_written(glyph, glyph, true) {
            return Err(ExemplarFault::Unwritten {
                rule: rule.to_string(),
                spelling: glyph,
            });
        }
        let ascii_written = match entry.ascii {
            Ascii::Token(token) => tile_written(glyph, token.0, true),
            Ascii::Head(head) => tree.positions().any(|position| {
                tree.node(position)
                    .is_some_and(|node| matches!(node.label(), NodeLabel::Tile(_)))
                    && tree
                        .fragment(position)
                        .is_some_and(|fragment| <&str>::from(fragment) == head.0)
            }),
        };
        if !ascii_written {
            let (Ascii::Token(spelling) | Ascii::Head(spelling)) = entry.ascii;
            return Err(ExemplarFault::Unwritten {
                rule: rule.to_string(),
                spelling: spelling.0,
            });
        }
    }
    Ok(())
}

/// Whether some tile of `tree` is molded by `rule`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when a tile of the tree carries a mold of `rule`.
/// - fails: no tile does.
/// - panics: none.
///
/// # Errors
/// [`ExemplarFault::Unmolded`] naming the rule.
///
/// # Adequacy
/// - hypothesis: L3 — every committed exemplar holds its mold; another rule's
///   form in its place does not.
/// - witness: `ledger::exemplars::tests::an_exemplar_of_another_form_lacks_the_mold`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(ExemplarFault::Unmolded { .. })))]
fn molded(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    rule: RuleName,
) -> Result<(), ExemplarFault>
{
    let holds = tree.positions().any(|position| {
        tree.node(position)
            .is_some_and(|node| matches!(node.label(), NodeLabel::Tile(_)))
            && rule_of(pbg, tree, position) == Maybe::Present(rule)
    });
    if holds {
        Ok(())
    }
    else {
        Err(ExemplarFault::Unmolded {
            rule: rule.to_string(),
        })
    }
}

/// The opening `///` lines of an exemplar.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Header
{
    /// How many lines it holds.
    lines: usize,
}

/// Whether `tree` lowers with `attribute` filed on a declaration and no
/// declaration refused.
///
/// # Specification
/// - requires: `tree` parsed with no obligation, from a source opening with
///   `header`.
/// - ensures: `Ok` exactly when the lowering accepts the source, refuses none
///   of its declarations, and files `attribute` on one of them: in the
///   attribute table, or, for `doc`, as documentation holding more lines than
///   `header`.
/// - fails: the lowering refuses, or the attribute is filed nowhere.
/// - panics: none.
///
/// # Errors
/// [`ExemplarFault::Refused`] with the lowering's account, or
/// [`ExemplarFault::Unfiled`] naming the attribute.
///
/// # Adequacy
/// - hypothesis: L3 — every committed attribute exemplar files its attribute;
///   an exemplar naming an unregistered attribute is refused, and a `doc`
///   exemplar documented by its header alone is unfiled.
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
/// - witness: `ledger::exemplars::tests::each_check_names_its_file`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(ExemplarFault::Refused { .. } | ExemplarFault::Unfiled { .. })))]
fn filed(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    attribute: RegisteredAttribute,
    header: Header,
) -> Result<(), ExemplarFault>
{
    let mut arena = CoreArena::new();
    let module = lower_module(
        pbg,
        tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .map_err(|refusal| ExemplarFault::Refused {
        refusal: refusal.to_string(),
    })?;
    let mut filed = false;
    for declaration in module.declarations() {
        if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
            return Err(ExemplarFault::Refused {
                refusal: refusal.to_string(),
            });
        }
        for key in [declaration.signature(), declaration.definition()] {
            let Maybe::Present(key) = key
            else {
                continue;
            };
            filed |= if attribute == RegisteredAttribute::DOC {
                match module.documentation(key) {
                    Maybe::Present(documentation) => {
                        documentation.text().as_ref().lines().count() > header.lines
                    },
                    Maybe::Absent(_) => false,
                }
            }
            else {
                module
                    .attributes()
                    .entries(key)
                    .iter()
                    .any(|entry| entry.name() == attribute)
            };
        }
    }
    if filed {
        Ok(())
    }
    else {
        Err(ExemplarFault::Unfiled {
            attribute: attribute.to_string(),
        })
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use super::ExemplarFault;
    use super::ExemplarReport;
    use crate::ledger::LedgerRun;
    use crate::ledger::LedgerTask;

    /// The committed exemplar directory.
    ///
    /// # Specification
    /// trivial.
    fn committed() -> PathBuf
    {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../ledger/exemplars")
    }

    /// A copy of the committed exemplars in a directory of this test's own.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn copied(name: &Path) -> PathBuf
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-exemplars-{}-{}",
            std::process::id(),
            name.display()
        ));
        let _cleared = std::fs::remove_dir_all(&directory);
        for folder in ["syntax", "attributes", "diagnostics"] {
            let target = directory.join(folder);
            std::fs::create_dir_all(&target).expect("the copy's folder is created");
            for entry in std::fs::read_dir(committed().join(folder)).expect("the folder lists") {
                let source = entry.expect("the entry reads").path();
                let _bytes =
                    std::fs::copy(&source, target.join(source.file_name().expect("a file")))
                        .expect("the exemplar copies");
            }
        }
        directory
    }

    /// The report of verifying `directory`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn verified(directory: &Path) -> ExemplarReport
    {
        let task = LedgerTask::Exemplars {
            directory: directory.to_path_buf(),
        };
        match task.run() {
            Ok(LedgerRun::Verified(report)) => report,
            Ok(
                LedgerRun::Written(_)
                | LedgerRun::Swept(_)
                | LedgerRun::Listed(_)
                | LedgerRun::Shown(_),
            ) => {
                panic!("verifying writes, sweeps and reads nothing else")
            },
            Err(fault) => panic!("the directory verifies: {fault}"),
        }
    }

    /// Every finding of `report` as `<file name>: <fault>`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn named(report: &ExemplarReport) -> Vec<String>
    {
        report
            .findings()
            .iter()
            .map(|finding| {
                let file = finding.path.file_name().expect("a file").display();
                format!("{file}: {}", finding.fault)
            })
            .collect()
    }

    #[test]
    fn the_committed_exemplars_verify()
    {
        let report = verified(&committed());
        assert_eq!(named(&report), Vec::<String>::new());
        let ledger = crate::ledger::SyntaxLedger::build().expect("the ledger builds");
        let committed_rules = ledger
            .rules
            .iter()
            .filter(|row| row.standing == crate::ledger::Standing::Committed)
            .count();
        assert_eq!(
            report.verified,
            committed_rules + ledger.attributes.len(),
            "one verified exemplar per committed rule and per attribute"
        );
        let features = std::fs::read_dir(committed().join("features"))
            .expect("the features folder lists")
            .count();
        assert_eq!(
            report.exhibited, features,
            "every committed features exemplar exhibits"
        );
    }

    #[test]
    fn a_renamed_exemplar_breaks_the_bijection()
    {
        let directory = copied(Path::new("renamed"));
        let syntax = directory.join("syntax");
        std::fs::rename(
            syntax.join("def_value.gandr"),
            syntax.join("def_values.gandr"),
        )
        .expect("the exemplar renames");
        let report = verified(&directory);
        assert_eq!(named(&report), [
            "def_value.gandr: no exemplar for rule `def_value`",
            "def_values.gandr: names nothing the ledger lists",
        ]);
        assert!(matches!(
            report.findings.first().map(|finding| &finding.fault),
            Some(ExemplarFault::Missing { .. })
        ));
    }

    #[test]
    fn an_exemplar_of_another_form_lacks_the_mold()
    {
        let directory = copied(Path::new("another"));
        std::fs::write(
            directory.join("syntax/return_expression.gandr"),
            "/// `return_expression`: a return.\ndef answer = pure 42 ;\n",
        )
        .expect("the exemplar is replaced");
        let report = verified(&directory);
        assert_eq!(named(&report), [
            "return_expression.gandr: its tree holds no tile molded by rule `return_expression`"
        ]);
    }

    #[test]
    fn each_check_names_its_file()
    {
        let directory = copied(Path::new("checks"));
        for (file, text) in [
            (
                "syntax/case_expression.gandr",
                "// `case_expression`\ndef a = case x { y => y } ;\n",
            ),
            (
                "syntax/block.gandr",
                "/// `block`: a block.\ndef answer = { return 42 ;\n",
            ),
            (
                "syntax/number.expression.gandr",
                "/// `number.expression`: two.\ndef a = 1 ;\ndef b = 2 ;\n",
            ),
            (
                "attributes/doc.gandr",
                "/// `doc`: documented by the header alone.\ndef answer = 42 ;\n",
            ),
            (
                "attributes/entry.gandr",
                "/// `entry`: no world.\n@[ entry(seat) ]\ndef opened() -> -F Unit {\n  pure unit\n}\n",
            ),
        ] {
            std::fs::write(directory.join(file), text).expect("the exemplar is replaced");
        }
        let report = verified(&directory);
        assert_eq!(named(&report), [
            "block.gandr: parses with 2 obligations left",
            "case_expression.gandr: does not open with a `///` comment naming rule `case_expression`",
            "number.expression.gandr: holds 2 items of its rule where it shows 1",
            "doc.gandr: the attribute `doc` is filed on no declaration",
            "entry.gandr: the lowering refuses it: no declaration or binder answers `seat`",
        ]);
    }

    #[test]
    fn a_glyph_exemplar_writes_both_spellings()
    {
        let directory = copied(Path::new("glyphs"));
        for (file, text) in [
            (
                "syntax/equivalence_type.gandr",
                "/// `equivalence_type`: the glyph twice.\ndef a : Type ≃ Type ;\ndef b : Type ≃ Type ;\n",
            ),
            (
                "syntax/isomorphism_type.gandr",
                "/// `isomorphism_type`: no call.\ndef a : Type ≅ Type ;\ndef b : Type ≅ Type ;\n",
            ),
            (
                "syntax/universe_flow_type.gandr",
                "/// `universe_flow_type`: one spelling.\ndef a : Type ⇝ Type ;\n",
            ),
        ] {
            std::fs::write(directory.join(file), text).expect("the exemplar is replaced");
        }
        let report = verified(&directory);
        assert_eq!(named(&report), [
            "equivalence_type.gandr: writes no tile of rule `equivalence_type` as `<~>`",
            "isomorphism_type.gandr: writes no tile of rule `isomorphism_type` as `Iso`",
            "universe_flow_type.gandr: holds 1 item of its rule where it shows 2",
        ]);
    }

    #[test]
    fn a_features_exemplar_states_only_what_holds()
    {
        let directory = copied(Path::new("features"));
        let features = directory.join("features");
        std::fs::create_dir_all(&features).expect("the features folder is created");
        for (file, text) in [
            (
                "shown.gandr",
                "/// `shown`: what holds.\n@[ checks ]\ndef answer : Integer ;\ndef answer = 42 ;\n",
            ),
            (
                "refused.gandr",
                "/// `refused`: a refusal.\n@[ refuses(\"TypeMismatch\") ]\ndef wrong : Integer ;\ndef wrong = \"text\" ;\n",
            ),
            (
                "owed.gandr",
                "/// `owed`: an owed hole.\n@[ owes(1) ]\ndef code : Type ;\n",
            ),
            ("notes.txt", "no source"),
        ] {
            std::fs::write(features.join(file), text).expect("the exemplar is written");
        }
        let report = verified(&directory);
        let mut findings = named(&report);
        findings.sort();
        assert_eq!(findings, [
            "notes.txt: names nothing the ledger lists",
            "owed.gandr: states `owes`, but a features exemplar shows what holds",
            "refused.gandr: states `refuses`, but a features exemplar shows what holds",
        ]);
        assert_eq!(
            report.exhibited, 1,
            "the one exemplar stating `checks` exhibits"
        );
        assert_eq!(
            report.to_string(),
            format!(
                "{} exemplars verified, 1 features exemplar exhibiting, {} diagnostics exemplars refusing, {} owed, 3 findings",
                report.verified, report.diagnosed, report.owed
            ),
            "the summary counts each kind once"
        );
    }
}
