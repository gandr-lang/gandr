//! The ledgers: the language surface enumerated from the grammar itself.
//!
//! # The syntax ledger is generated, never written
//!
//! [`SyntaxLedger::build`] reads every rule of the built-in grammar
//! (`gandr-surface-grammar`'s `built_in`) and every attribute of the lowering's
//! registry (`gandr-surface-lowering`'s `AttributeRegistry`), and renders them
//! twice: [`SyntaxLedger::markdown`] for reading, grouped by sort, one row per
//! rule, and [`SyntaxLedger::json`] for machines, the same rows with each
//! form's full tree. Nothing is listed by hand, so the ledger is exhaustive by
//! construction, and both files open with the grammar's fingerprint: a ledger
//! whose fingerprint is not the built grammar's is stale by definition.
//! `gandr ledger syntax --write <directory>` writes `syntax.md` and
//! `syntax.json` there; `mise run check:syntax-ledger` writes them into a
//! temporary directory and compares both with the committed files byte for
//! byte. Each committed rule and each attribute also has an exemplar, a
//! hand-cut source the `exemplars` module verifies against the ledger:
//! `gandr ledger exemplars <directory>`, gated by
//! `mise run check:syntax-exemplars`.
//!
//! - Choice: a driver verb over this module. The dispatcher already holds the
//!   grammar, the parser and the lowering a row reads.
//! - Alternatives: a binary in the grammar crate's tools, which cannot see the
//!   lowering's registry without a dependency cycle, since the lowering depends
//!   on the grammar; a golden test rewriting the files under `UPDATE_EXPECT=1`,
//!   which makes the staleness check a whole test target and hides the
//!   generator behind a test harness.
//! - Reversal: a ledger that needs a crate the dispatcher does not depend on
//!   moves the generator into a crate of its own.
//!
//! # A row reads the grammar, the parser and the highlighter
//!
//! A rule's row carries its name, its sort, its precedence group, the named
//! kind it realises (its provenance, marked where the surface's tree-sitter
//! grammar has no such kind), its form and the highlight roles of its tiles.
//! The machine form adds, per tile, the [`MoldId`] the grammar's build assigned
//! it, its [`TileKind`] and its role: the rule's molds are numbered left to
//! right through its form, and the generator pairs each tile of the form with
//! the next mold of the rule, refusing a pairing whose labels disagree
//! ([`LedgerFault::Molds`]). An attribute's row carries its name and the
//! payload its schema admits.
//!
//! # How a form is spelled
//!
//! A form is its rule's tiles and holes in order. A tile written as text is
//! that text; a tile of a lexical class, an identifier or a number, is the
//! class's name in `‹ ›`, which is how the parser's `tile_spelling` tells the
//! two apart; a hole is its sort's name in capitals. Alternatives are
//! `⦅ a ‖ b ⦆`, an optional part `⦅ a ⦆?` and a repetition `⦅ a ⦆*`, written
//! with characters no tile uses, so a bracket or a bar of the language is never
//! read as notation. A top-level alternative drops its brackets.
//!
//! A part of a form equal to another rule's whole form is written `⟨rule⟩`. A
//! precedence-bounded grammar recurs through sorts, never through rule names,
//! so a statement block or a string is written out in full in every form that
//! holds one; abbreviating it keeps a row readable. The abbreviation names the
//! form, not a nesting: the tiles it stands for are the abbreviating rule's
//! own, molded as its own, and the machine form spells them out. Only a rule
//! whose form is composite abbreviates, and the earliest such rule in grammar
//! order is named.
//!
//! - Alternatives: every form in full, which writes the statement block out
//!   twenty times and puts several kilobytes in the definition's cell; an EBNF
//!   with quoted tiles, which quotes every keyword and still needs the quote
//!   tile escaped.
//! - Reversal: a reader who must see a form whole reads it in the machine form.
//!
//! # Internal rules
//!
//! A rule no source can mold is listed in a table of its own with the reason
//! and what the reason is read from — the grammar, the labeler or a parser
//! probe — and never dropped. The reasons are derived, never listed by hand;
//! the `standing` module states each and the order they are tried in. A tile
//! spelled by a word stays committed where nothing else reads the word: the
//! labeler offers a word's own text as a label, so the word molds the rule's
//! tile where it is admissible.
//!
//! - Alternatives: a list of internal rules beside the grammar, which is a hand
//!   list; reading the parity table's `unproduced` reasons, which describe the
//!   printer, not the parser.
//! - Reversal: a rule the exemplar gate cannot show although no reason fires
//!   widens a reason.
//!
//! # The machine form is one rule per line
//!
//! `syntax.json` is one object: the ledger's name, the fingerprint, the counts,
//! then `rules` and `attributes`, each element compact on a line of its own, so
//! a change to one rule is a change to one line. A form's tree is nested: a
//! tile `{"node":"tile",…}`, a hole `{"node":"hole","sort":…}`, and `seq`,
//! `alt`, `optional` and `repeat` nodes holding their children in order. Keys
//! are written in byte order.
//!
//! [`TileKind`]: gandr_surface_grammar::TileKind

mod exemplars;
mod standing;

use alloc::collections::BTreeMap;
use core::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RegexShape;
use gandr_surface_grammar::RegexView;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::Sym;
use gandr_surface_grammar::TREE_SITTER_NAMED_KINDS;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::AttributeRegistry;
use gandr_surface_lowering::AttributeSchema;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_parser::CandidateLabel;
use gandr_surface_parser::TileSpelling;
use gandr_surface_parser::tile_spelling;
use gandr_surface_syntax::MoldId;
use quenchant_shape::shape::Maybe;
use serde_json::Value;
use serde_json::json;

pub use self::exemplars::ExemplarFault;
pub use self::exemplars::ExemplarFinding;
pub use self::exemplars::ExemplarReport;

/// The file the reading form is written to.
const MARKDOWN: &str = "syntax.md";

/// The file the machine form is written to.
const JSON: &str = "syntax.json";

/// The invocation that regenerates the committed ledger, as its header names
/// it.
const REGENERATE: &str = "gandr ledger syntax --write ledger";

/// Which ledger a `gandr ledger` invocation writes or verifies, and where.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LedgerTask
{
    /// The syntax ledger, written into `directory`.
    Syntax
    {
        /// The directory `syntax.md` and `syntax.json` are written into.
        directory: PathBuf,
    },
    /// The syntax exemplars under `directory`, verified.
    Exemplars
    {
        /// The directory holding `syntax/` and `attributes/`.
        directory: PathBuf,
    },
}

/// What a ledger task did.
#[derive(Debug)]
pub enum LedgerRun
{
    /// The files a writing task wrote, in the order it wrote them.
    Written(Vec<PathBuf>),
    /// What a verification found.
    Verified(ExemplarReport),
}

/// Why a ledger could not be generated or written.
#[derive(Debug)]
pub enum LedgerFault
{
    /// The built-in grammar did not build, or refused a lookup a row makes.
    Grammar(PbgError),
    /// A rule's tiles and its molds disagree, so a row would misname a mold.
    Molds
    {
        /// The rule whose molds disagree with its form.
        rule: &'static str,
    },
    /// A rule's precedence group has no name in the grammar's table.
    Group
    {
        /// The rule whose group is unnamed.
        rule: &'static str,
    },
    /// The registry lists a name its own lookup does not answer.
    Attribute
    {
        /// The name the registry lists.
        name: String,
    },
    /// A lexical class a probe spells has no sample in the `standing`
    /// module's table.
    Sample
    {
        /// The class.
        class: &'static str,
    },
    /// A ledger file could not be written.
    Unwritable
    {
        /// The file.
        path: PathBuf,
        /// Why.
        error: std::io::Error,
    },
    /// An exemplar directory could not be listed.
    Unreadable
    {
        /// The directory.
        path: PathBuf,
        /// Why.
        error: std::io::Error,
    },
}

impl core::fmt::Display for LedgerFault
{
    /// Writes the fault and what it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Grammar(ref error) => write!(f, "the built-in grammar: {error}"),
            Self::Molds { rule } => {
                write!(f, "the molds of rule `{rule}` disagree with its form")
            },
            Self::Group { rule } => write!(f, "the group of rule `{rule}` has no name"),
            Self::Attribute { ref name } => {
                write!(f, "the registry lists `{name}` but gives it no schema")
            },
            Self::Sample { class } => {
                write!(f, "the lexical class `{class}` has no probe sample")
            },
            Self::Unwritable {
                ref path,
                ref error,
            } => write!(f, "{}: cannot write: {error}", path.display()),
            Self::Unreadable {
                ref path,
                ref error,
            } => write!(f, "{}: cannot list: {error}", path.display()),
        }
    }
}

impl LedgerTask
{
    /// Generate the task's ledger and write its files, or verify its
    /// exemplars.
    ///
    /// # Specification
    /// - requires: nothing; a syntax ledger's directory is created when it is
    ///   missing.
    /// - ensures: under [`LedgerTask::Syntax`], `syntax.md` and `syntax.json`
    ///   in the directory hold exactly [`SyntaxLedger::markdown`] and
    ///   [`SyntaxLedger::json`] of a freshly built ledger, and the paths are
    ///   returned in that order. Under [`LedgerTask::Exemplars`], the report of
    ///   the exemplars under the directory against the committed rules and the
    ///   registered attributes (the `exemplars` module).
    /// - provides: `gandr ledger syntax --write <directory>` and `gandr ledger
    ///   exemplars <directory>`.
    /// - fails: the ledger cannot be built, a file cannot be written, or an
    ///   exemplar directory cannot be listed.
    /// - panics: none.
    ///
    /// # Errors
    /// What [`SyntaxLedger::build`] reports, [`LedgerFault::Unwritable`]
    /// naming the file, or [`LedgerFault::Unreadable`] naming the directory.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run into an empty directory writes both files with
    ///   the rendered bytes, a second run writes the same bytes, and a
    ///   directory under a file is refused naming the path; the committed
    ///   exemplars verify with no finding. Arbitrary filesystem failures are
    ///   outside these observations.
    /// - witness: `ledger::tests::a_run_writes_both_files_and_repeats_them_exactly`
    /// - witness: `ledger::tests::an_unwritable_directory_is_refused_by_path`
    /// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |run| match (self, run) {
        (&Self::Syntax { .. }, &LedgerRun::Written(ref paths)) => paths.len() == 2,
        (&Self::Exemplars { .. }, &LedgerRun::Verified(_)) => true,
        (&Self::Syntax { .. } | &Self::Exemplars { .. }, &LedgerRun::Written(_) | &LedgerRun::Verified(_)) => false,
    }))]
    #[inline]
    pub fn run(&self) -> Result<LedgerRun, LedgerFault>
    {
        let ledger = SyntaxLedger::build()?;
        match *self {
            Self::Syntax { ref directory } => {
                std::fs::create_dir_all(directory).map_err(|error| LedgerFault::Unwritable {
                    path: directory.clone(),
                    error,
                })?;
                let markdown = written(directory, Path::new(MARKDOWN), ledger.markdown())?;
                let json = written(directory, Path::new(JSON), ledger.json())?;
                Ok(LedgerRun::Written(vec![markdown, json]))
            },
            Self::Exemplars { ref directory } => {
                let pbg = built_in().map_err(LedgerFault::Grammar)?;
                let rules: Vec<RuleName> = ledger
                    .rules
                    .iter()
                    .filter(|row| row.standing == Standing::Committed)
                    .map(|row| RuleName(row.name))
                    .collect();
                exemplars::verify(&pbg, &rules, directory).map(LedgerRun::Verified)
            },
        }
    }
}

/// Write `text` to the file `name` under `directory`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the file holds exactly `text`, and its path is returned.
/// - fails: the file cannot be written.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Unwritable`] naming the file.
///
/// # Adequacy
/// - hypothesis: L3 — a written file reads back as the text, and a path under a
///   file is refused naming that path.
/// - witness: `ledger::tests::a_run_writes_both_files_and_repeats_them_exactly`
/// - witness: `ledger::tests::an_unwritable_directory_is_refused_by_path`
#[spec(ensures: |ref ret| ret.as_ref().map_or_else(
    |fault| matches!(*fault, LedgerFault::Unwritable { ref path, .. } if path.starts_with(directory)),
    |path| path.ends_with(name),
))]
fn written(
    directory: &Path,
    name: &Path,
    text: String,
) -> Result<PathBuf, LedgerFault>
{
    let path = directory.join(name);
    match std::fs::write(&path, text) {
        Ok(()) => Ok(path),
        Err(error) => Err(LedgerFault::Unwritable { path, error }),
    }
}

/// Where a rule stands: a source can mold it, or no source can.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// No reason of the `standing` module fires.
    Committed,
    /// No source molds the rule, for this reason.
    Internal(standing::Internal),
}

/// Whether the surface's tree-sitter grammar has a rule's named kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TreeSitterKind
{
    /// The tree-sitter grammar names the kind too.
    Shared,
    /// Only this grammar has the kind.
    GrammarOnly,
}

/// One rule of the grammar, as the ledger reads it.
#[derive(Clone, Debug)]
struct RuleRow
{
    /// The rule's name.
    name: &'static str,
    /// The sort its form produces.
    sort: Sort,
    /// Its precedence group's name.
    group: String,
    /// The named kind it realises.
    kind: &'static str,
    /// Whether the tree-sitter grammar has that kind.
    tree_sitter: TreeSitterKind,
    /// The form, spelled for reading.
    form: String,
    /// The form as a tree, every tile with its mold.
    tree: Value,
    /// The highlight roles of its tiles, each once, first use first.
    roles: Vec<String>,
    /// Whether a source can mold it.
    standing: Standing,
}

/// One attribute of the lowering's registry, as the ledger reads it.
#[derive(Clone, Debug)]
struct AttributeRow
{
    /// The attribute's name.
    name: String,
    /// The payload its schema admits.
    schema: AttributeSchema,
}

/// The syntax ledger: every rule of the built-in grammar and every attribute
/// of the lowering's registry, under the grammar's fingerprint.
#[derive(Clone, Debug)]
pub struct SyntaxLedger
{
    /// The grammar's fingerprint, sixteen hexadecimal digits after `0x`.
    fingerprint: String,
    /// How many molds the grammar numbers.
    molds: usize,
    /// One row per rule, in grammar order.
    rules: Vec<RuleRow>,
    /// One row per attribute, in registry order.
    attributes: Vec<AttributeRow>,
}

impl SyntaxLedger
{
    /// Read the ledger off the built-in grammar and the attribute registry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one rule row per rule of the built-in grammar, in grammar
    ///   order, and one attribute row per registered attribute, in registry
    ///   order; every mold of the grammar is the mold of exactly one tile of
    ///   one row, paired with the tile of its own label.
    /// - provides: the rows both renderings read.
    /// - fails: the grammar does not build, a lookup into it is refused, a
    ///   rule's molds disagree with its form, a group is unnamed, or the
    ///   registry lists a name it does not answer.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LedgerFault::Grammar`], [`LedgerFault::Molds`],
    /// [`LedgerFault::Group`] or [`LedgerFault::Attribute`].
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the built-in grammar is a finite census: the rows'
    ///   count equals the rules', the molds the rows name are every mold once,
    ///   and the attribute rows are the registry's names. A grammar other than
    ///   the built-in one is outside the domain.
    /// - witness: `ledger::tests::every_rule_mold_and_attribute_has_one_row`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ledger| ledger.attributes.len() == AttributeRegistry::names().len()))]
    #[inline]
    pub fn build() -> Result<Self, LedgerFault>
    {
        let pbg = built_in().map_err(LedgerFault::Grammar)?;
        let roles = RoleTable::build(&pbg).map_err(LedgerFault::Grammar)?;
        let molds = molds_by_rule(&pbg)?;
        let abbreviations = abbreviations(&pbg);
        let mut rules = Vec::with_capacity(pbg.rules().len());
        for (index, rule) in pbg.rules().iter().enumerate() {
            let rule_molds = molds.get(index).map_or(&[][..], Vec::as_slice);
            let tree = tree(
                &pbg,
                &roles,
                RuleName(rule.name),
                rule.regex().view(),
                rule_molds,
            )?;
            let group = pbg
                .dag()
                .name(rule.prec)
                .map(|name| name.to_string())
                .ok_or(LedgerFault::Group { rule: rule.name })?;
            rules.push(RuleRow {
                name: rule.name,
                sort: rule.sort,
                group,
                kind: rule.provenance,
                tree_sitter: if TREE_SITTER_NAMED_KINDS.contains(&rule.provenance) {
                    TreeSitterKind::Shared
                }
                else {
                    TreeSitterKind::GrammarOnly
                },
                form: spelled(rule.regex().view(), &abbreviations, RuleName(rule.name)),
                tree: tree.value,
                roles: tree.roles,
                standing: standing::standing(&pbg, rule)?,
            });
        }
        let attributes = AttributeRegistry::names()
            .into_iter()
            .map(|registered| {
                let name = registered.as_ref();
                match AttributeRegistry::lookup(SurfaceName::from(name)) {
                    Maybe::Present((_, schema)) => Ok(AttributeRow {
                        name: name.to_owned(),
                        schema,
                    }),
                    Maybe::Absent(_) => Err(LedgerFault::Attribute {
                        name: name.to_owned(),
                    }),
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            fingerprint: format!("{:#018x}", u64::from(pbg.fingerprint())),
            molds: pbg.iter_molds().count(),
            rules,
            attributes,
        })
    }

    /// The ledger for reading: a header naming the fingerprint and the
    /// counts, how to read a form, a table per sort, the internal rules and
    /// the attributes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the header names the fingerprint; every committed rule is one
    ///   table row under its sort's heading, the sorts in their declared order
    ///   and the rules in grammar order, and every internal rule one row of the
    ///   internal table; every attribute is one row of the attribute table. A
    ///   `|` inside a cell is escaped. The text ends with one newline.
    /// - provides: `syntax.md`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the built ledger's text holds its fingerprint once in
    ///   the header, a row per rule and attribute naming it, and a form holding
    ///   a bar escapes it. Markdown rendering itself is the format gate's to
    ///   check.
    /// - witness: `ledger::tests::both_files_carry_the_fingerprint_and_every_row`
    #[spec(ensures: |ret| ret.ends_with('\n') && !ret.ends_with("\n\n") && ret.contains(&self.fingerprint))]
    #[inline]
    #[must_use]
    pub fn markdown(&self) -> String
    {
        let mut out = String::new();
        match self.write_markdown(&mut out) {
            // Writing into a `String` never fails.
            Ok(()) | Err(core::fmt::Error) => out,
        }
    }

    /// Write [`markdown`](Self::markdown)'s text into `out`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends exactly the text [`markdown`](Self::markdown) states.
    /// - fails: what `out` fails with; a `String` never does.
    /// - panics: none.
    ///
    /// # Errors
    /// The formatter's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`markdown`](Self::markdown).
    /// - witness: `ledger::tests::both_files_carry_the_fingerprint_and_every_row`
    #[spec(ensures: |ref ret| ret.is_err() || out.ends_with('\n'))]
    fn write_markdown(
        &self,
        out: &mut String,
    ) -> core::fmt::Result
    {
        let committed = self
            .rules
            .iter()
            .filter(|row| row.standing == Standing::Committed)
            .count();
        let mut by_sort: BTreeMap<Sort, Vec<&RuleRow>> = BTreeMap::new();
        for row in self
            .rules
            .iter()
            .filter(|row| row.standing == Standing::Committed)
        {
            by_sort.entry(row.sort).or_default().push(row);
        }
        out.push_str("# Syntax ledger\n\n");
        writeln!(
            out,
            "Generated from the built-in grammar by `{REGENERATE}`; never edited by hand. `mise run check:syntax-ledger` regenerates it and fails while this file differs. `syntax.json` holds the same rows for machines, each form as a tree with every tile's mold.\n"
        )?;
        writeln!(out, "- Grammar fingerprint: `{}`", self.fingerprint)?;
        writeln!(
            out,
            "- Rules: {} — {committed} committed, {} internal",
            self.rules.len(),
            self.rules.len().saturating_sub(committed)
        )?;
        writeln!(out, "- Molds: {}", self.molds)?;
        writeln!(out, "- Attributes: {}\n", self.attributes.len())?;
        out.push_str("## Reading a form\n\n");
        out.push_str("A form spells its rule's tiles and holes in order.\n\n");
        out.push_str("| Notation | Reads |\n| -------- | ----- |\n");
        out.push_str("| `def` | a tile written as this text |\n");
        out.push_str("| `‹identifier›` | a tile of a lexical class: any identifier |\n");
        out.push_str("| `EXPRESSION` | a hole holding a form of that sort |\n");
        out.push_str("| `⦅ a ‖ b ⦆` | one of the alternatives |\n");
        out.push_str("| `⦅ a ⦆?` | the part, or nothing |\n");
        out.push_str("| `⦅ a ⦆*` | the part, any number of times |\n");
        out.push_str(
            "| `⟨block⟩` | the whole form of rule `block`, written out in place: its tiles are this rule's own |\n\n",
        );
        out.push_str("Each committed rule links its exemplar, a small source the exemplar gate parses and checks for a tile of the rule. The group is the rule's precedence group. The kind is the named node kind the rule realises; `*` marks a kind the surface's tree-sitter grammar does not have. The roles are the highlight roles of the rule's tiles, each once, first use first.\n");
        for (sort, rows) in &by_sort {
            write!(out, "\n## `{}` — {}\n\n", sort.name(), Counted {
                count: rows.len(),
                noun: "rule"
            })?;
            out.push_str("| Rule | Form | Group | Kind | Roles |\n");
            out.push_str("| ---- | ---- | ----- | ---- | ----- |\n");
            for row in rows {
                let marker = match row.tree_sitter {
                    TreeSitterKind::Shared => "",
                    TreeSitterKind::GrammarOnly => " *",
                };
                let roles = if row.roles.is_empty() {
                    "—".to_owned()
                }
                else {
                    row.roles.join(", ")
                };
                writeln!(
                    out,
                    "| [`{name}`](exemplars/syntax/{name}.gandr) | {} | `{}` | `{}`{marker} | {roles} |",
                    Code(&row.form),
                    row.group,
                    row.kind,
                    name = row.name,
                )?;
            }
        }
        let internal: Vec<(&RuleRow, standing::Internal)> = self
            .rules
            .iter()
            .filter_map(|row| match row.standing {
                Standing::Internal(reason) => Some((row, reason)),
                Standing::Committed => None,
            })
            .collect();
        write!(out, "\n## Internal — {}\n\n", Counted {
            count: internal.len(),
            noun: "rule"
        })?;
        out.push_str("A rule no source can mold, with the reason and what the reason is read from: the grammar's forms, the labeler over a tile's own text, or a parser probe. These rules have no exemplar.\n\n");
        out.push_str("| Rule | Sort | Form | Reason | Read from |\n");
        out.push_str("| ---- | ---- | ---- | ------ | --------- |\n");
        for (row, reason) in internal {
            writeln!(
                out,
                "| `{}` | {} | {} | {reason} | {} |",
                row.name,
                row.sort.name(),
                Code(&row.form),
                reason.evidence()
            )?;
        }
        write!(out, "\n## Attributes — {}\n\n", Counted {
            count: self.attributes.len(),
            noun: "attribute"
        })?;
        out.push_str("Every attribute the lowering's registry admits in an `@[ … ]` block, with the payload its schema takes, linking its exemplar, which the exemplar gate lowers and checks the attribute is filed.\n\n");
        out.push_str("| Attribute | Payload |\n");
        out.push_str("| --------- | ------- |\n");
        for row in &self.attributes {
            writeln!(
                out,
                "| [`{name}`](exemplars/attributes/{name}.gandr) | {} |",
                row.schema,
                name = row.name
            )?;
        }
        Ok(())
    }

    /// The ledger for machines: the same rows as [`markdown`](Self::markdown),
    /// each form as its tree.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one JSON object whose `fingerprint` is the grammar's, whose
    ///   `rules` hold one compact object per rule in grammar order and whose
    ///   `attributes` one per attribute in registry order, each element on a
    ///   line of its own. The text ends with one newline.
    /// - provides: `syntax.json`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the built ledger's text parses back as JSON whose
    ///   fingerprint, rule names and attribute names are the ledger's, and
    ///   whose lines hold one element each.
    /// - witness: `ledger::tests::both_files_carry_the_fingerprint_and_every_row`
    #[spec(ensures: |ret| ret.ends_with("}\n") && ret.lines().count() == self.rules.len().saturating_add(self.attributes.len()).saturating_add(10))]
    #[inline]
    #[must_use]
    pub fn json(&self) -> String
    {
        let rules: Vec<String> = self
            .rules
            .iter()
            .map(|row| rule_json(row).to_string())
            .collect();
        let attributes: Vec<String> = self
            .attributes
            .iter()
            .map(|row| attribute_json(row).to_string())
            .collect();
        let mut out = String::new();
        out.push_str("{\n  \"ledger\": \"syntax\",\n  \"generator\": \"");
        out.push_str(REGENERATE);
        out.push_str("\",\n  \"fingerprint\": \"");
        out.push_str(&self.fingerprint);
        out.push_str("\",\n  \"molds\": ");
        out.push_str(&self.molds.to_string());
        out.push_str(",\n  \"rules\": [\n");
        out.push_str(&elements(&rules));
        out.push_str("  ],\n  \"attributes\": [\n");
        out.push_str(&elements(&attributes));
        out.push_str("  ]\n}\n");
        out
    }
}

/// A count and its noun, the noun plural unless the count is one.
#[derive(Clone, Copy, Debug)]
struct Counted
{
    /// How many.
    count: usize,
    /// Of what, singular; its plural takes a trailing `s`.
    noun: &'static str,
}

impl core::fmt::Display for Counted
{
    /// Writes `1 rule`, `0 rules`, `2 rules`.
    ///
    /// # Specification
    /// - requires: the noun takes its plural by a trailing `s`.
    /// - ensures: the count, a space and the noun, plural unless the count is
    ///   one.
    /// - fails: what the formatter fails with.
    /// - panics: none.
    /// - executable: none — the text goes to the formatter, which the contract
    ///   cannot read back; the witness reads the written text.
    ///
    /// # Errors
    /// The formatter's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one and several are pinned.
    /// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let plural = if self.count == 1 { "" } else { "s" };
        write!(f, "{} {}{plural}", self.count, self.noun)
    }
}

/// `items` as the lines of a JSON array's body: each indented four spaces,
/// every one but the last followed by a comma.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one line per item, in order, each ending in a newline.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the ledger's arrays parse back with every element.
/// - witness: `ledger::tests::both_files_carry_the_fingerprint_and_every_row`
#[spec(ensures: |ret| ret.lines().count() == items.len())]
fn elements(items: &[String]) -> String
{
    let mut out = String::new();
    let last = items.len().saturating_sub(1);
    for (index, item) in items.iter().enumerate() {
        out.push_str("    ");
        out.push_str(item);
        if index != last {
            out.push(',');
        }
        out.push('\n');
    }
    out
}

/// A rule row as a JSON object.
///
/// # Specification
/// trivial.
fn rule_json(row: &RuleRow) -> Value
{
    let mut fields = serde_json::Map::new();
    fields.insert("name".to_owned(), Value::from(row.name));
    fields.insert("sort".to_owned(), Value::from(row.sort.name().to_string()));
    fields.insert("group".to_owned(), Value::from(row.group.clone()));
    fields.insert("kind".to_owned(), Value::from(row.kind));
    fields.insert(
        "tree_sitter".to_owned(),
        Value::from(row.tree_sitter == TreeSitterKind::Shared),
    );
    fields.insert("form".to_owned(), Value::from(row.form.clone()));
    fields.insert("roles".to_owned(), json!(row.roles));
    fields.insert("tree".to_owned(), row.tree.clone());
    match row.standing {
        Standing::Committed => {
            fields.insert("standing".to_owned(), Value::from("committed"));
            fields.insert(
                "exemplar".to_owned(),
                Value::from(format!("exemplars/syntax/{}.gandr", row.name)),
            );
        },
        Standing::Internal(reason) => {
            fields.insert("standing".to_owned(), Value::from("internal"));
            fields.insert("reason".to_owned(), Value::from(reason.name().to_string()));
            fields.insert(
                "evidence".to_owned(),
                Value::from(reason.evidence().to_string()),
            );
            fields.insert("because".to_owned(), Value::from(reason.to_string()));
        },
    }
    Value::Object(fields)
}

/// An attribute row as a JSON object.
///
/// # Specification
/// trivial.
fn attribute_json(row: &AttributeRow) -> Value
{
    let payload = match row.schema {
        AttributeSchema::Marker => json!({ "schema": "marker" }),
        AttributeSchema::Integer => json!({ "schema": "integer" }),
        AttributeSchema::Text => json!({ "schema": "text" }),
        AttributeSchema::MarkerOr(option) => json!({ "schema": "marker_or", "option": option }),
        AttributeSchema::Names => json!({ "schema": "names" }),
        AttributeSchema::Word(words) => json!({ "schema": "word", "words": words }),
    };
    json!({
        "name": row.name,
        "payload": payload,
        "reads": row.schema.to_string(),
        "exemplar": format!("exemplars/attributes/{}.gandr", row.name),
    })
}

/// Text as a markdown code span inside a table cell: every `|` escaped, and
/// the fence widened past any backtick run the text holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Code<'text>(&'text str);

impl core::fmt::Display for Code<'_>
{
    /// Writes the span.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span holds every character of the text, `|` as `\|`,
    ///   between fences one backtick longer than its longest backtick run,
    ///   padded by a space where the text touches a fence with a backtick.
    /// - fails: what the formatter fails with.
    /// - panics: none.
    /// - executable: none — the span goes to the formatter, which the contract
    ///   cannot read back; the witness reads the written text.
    ///
    /// # Errors
    /// The formatter's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a form holding a bar is escaped, and a plain form is
    ///   fenced by one backtick.
    /// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let Self(text) = *self;
        let mut longest = 0_usize;
        let mut run = 0_usize;
        for character in text.chars() {
            if character == '`' {
                run = run.saturating_add(1);
                longest = longest.max(run);
            }
            else {
                run = 0;
            }
        }
        let fence = "`".repeat(longest.saturating_add(1));
        let pad = if text.starts_with('`') || text.ends_with('`') {
            " "
        }
        else {
            ""
        };
        write!(f, "{fence}{pad}{}{pad}{fence}", text.replace('|', "\\|"))
    }
}

/// The molds of every rule, indexed by the rule's position in the grammar,
/// each list in mold order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one list per rule; every mold of `pbg` stands in the list of the
///   rule [`Pbg::rule_of`] names, once, the lists ascending.
/// - fails: a mold the grammar does not resolve to a rule, or to a rule it does
///   not list.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Grammar`] for a refused lookup, [`LedgerFault::Molds`] for
/// a rule the grammar does not list.
///
/// # Adequacy
/// - hypothesis: L2 — the built-in grammar's molds are a finite census whose
///   lists cover every mold once.
/// - witness: `ledger::tests::every_rule_mold_and_attribute_has_one_row`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |lists| lists.len() == pbg.rules().len() && lists.iter().map(Vec::len).sum::<usize>() == pbg.iter_molds().count()))]
fn molds_by_rule(pbg: &Pbg) -> Result<Vec<Vec<MoldId>>, LedgerFault>
{
    let positions: BTreeMap<&str, usize> = pbg
        .rules()
        .iter()
        .enumerate()
        .map(|(index, rule)| (rule.name, index))
        .collect();
    let mut lists: Vec<Vec<MoldId>> = vec![Vec::new(); pbg.rules().len()];
    for (mold, _) in pbg.iter_molds() {
        let rule = pbg.rule_of(mold).map_err(LedgerFault::Grammar)?;
        let list = positions
            .get(rule.name)
            .and_then(|&index| lists.get_mut(index))
            .ok_or(LedgerFault::Molds { rule: rule.name })?;
        list.push(mold);
    }
    Ok(lists)
}

/// What a fold over a form meets at one node.
#[derive(Clone, Copy, Debug)]
enum Node
{
    /// The empty sequence.
    Empty,
    /// A hole of a sort.
    Hole(Sort),
    /// A tile, by its label.
    Tile(&'static str),
    /// A concatenation of the children.
    Seq,
    /// An alternation of the children.
    Alt,
    /// The one child, or nothing.
    Optional,
    /// Any number of the one child.
    Repeat,
}

/// What a fold's visitor answers for a subtree before it is opened.
enum Visited<T>
{
    /// The subtree's answer, without opening it.
    Answer(T),
    /// Open the subtree and combine its children's answers.
    Open,
}

/// One step of a fold's work list.
enum Work<'regex>
{
    /// Visit this subtree.
    Enter(RegexView<'regex>),
    /// Combine the last `children` answers under `node`.
    Leave(Node, usize),
}

/// Fold `root` bottom-up: `visit` sees each subtree before it is opened and
/// may answer it whole; `combine` answers an opened node from its children's
/// answers, in order. Leaves are opened and combined in left-to-right order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the answer `combine` gives the root, or `visit`'s; every opened
///   node is combined once, after all its children, and the leaves are combined
///   in the order the form writes them.
/// - provides: every walk over a form, as an explicit work list.
/// - fails: what `combine` fails with.
/// - panics: none.
/// - executable: none — the answer's type is the caller's, so what holds of it
///   is the visitor's and the combiner's to state; the order is observed
///   through the spellings it produces.
///
/// # Errors
/// The first error `combine` returns.
///
/// # Adequacy
/// - hypothesis: L3 — the spelled forms, trees and standings of the built-in
///   rules exercise every node kind, nesting and the visitor's early answer; a
///   reordered child or a lost answer changes a pinned spelling.
/// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
/// - witness: `ledger::tests::every_rule_mold_and_attribute_has_one_row`
fn fold<'regex, T, E>(
    root: RegexView<'regex>,
    mut visit: impl FnMut(RegexView<'regex>) -> Visited<T>,
    mut combine: impl FnMut(Node, Vec<T>) -> Result<T, E>,
    leftover: E,
) -> Result<T, E>
{
    let mut work = vec![Work::Enter(root)];
    let mut answers: Vec<T> = Vec::new();
    while let Some(step) = work.pop() {
        match step {
            Work::Enter(view) => match visit(view) {
                Visited::Answer(answer) => answers.push(answer),
                Visited::Open => {
                    let (node, children) = match view.shape() {
                        RegexShape::Empty => (Node::Empty, Vec::new()),
                        RegexShape::Sym(Sym::Sort(sort)) => (Node::Hole(sort), Vec::new()),
                        RegexShape::Sym(Sym::Tile(tile)) => (Node::Tile(tile.label), Vec::new()),
                        RegexShape::Seq(children) => (Node::Seq, children),
                        RegexShape::Alt(children) => (Node::Alt, children),
                        RegexShape::Optional(child) => (Node::Optional, vec![child]),
                        RegexShape::Repeat(child) => (Node::Repeat, vec![child]),
                    };
                    work.push(Work::Leave(node, children.len()));
                    work.extend(children.into_iter().rev().map(Work::Enter));
                },
            },
            Work::Leave(node, count) => {
                let start = answers.len().saturating_sub(count);
                let children = answers.split_off(start);
                let answer = combine(node, children)?;
                answers.push(answer);
            },
        }
    }
    match (answers.pop(), answers.is_empty()) {
        (Some(answer), true) => Ok(answer),
        (Some(_) | None, _) => Err(leftover),
    }
}

/// A rule whose whole form a part of another form is written as.
#[derive(Clone, Copy)]
struct Abbreviation<'grammar>
{
    /// The rule.
    name: RuleName,
    /// Its whole form.
    form: RegexView<'grammar>,
}

/// The rules whose whole form a part of another form is written as: every
/// rule whose form is composite, in grammar order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per rule whose form's root is a sequence, an
///   alternation, an option or a repetition, in grammar order, each with the
///   rule's form.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the lambda's body abbreviates to the block, and a
///   one-tile rule abbreviates nothing.
/// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
#[spec(ensures: |ret| ret.len() <= pbg.rules().len())]
fn abbreviations(pbg: &Pbg) -> Vec<Abbreviation<'_>>
{
    pbg.rules()
        .iter()
        .filter(|rule| {
            matches!(
                rule.regex().view().shape(),
                RegexShape::Seq(_)
                    | RegexShape::Alt(_)
                    | RegexShape::Optional(_)
                    | RegexShape::Repeat(_)
            )
        })
        .map(|rule| Abbreviation {
            name: RuleName(rule.name),
            form: rule.regex().view(),
        })
        .collect()
}

/// The form `root` of `rule`, spelled for reading.
///
/// # Specification
/// - requires: `abbreviations` is [`abbreviations`] of the grammar the rule
///   belongs to.
/// - ensures: a top-level alternation is its branches joined by `‖`, each
///   spelled; any other form is spelled whole. A part equal to the whole form
///   of another rule of `abbreviations` is that rule's name in `⟨ ⟩`; a branch
///   or form spelled whole never is.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — pinned spellings of a keyword form, a form with a class
///   tile, an option and a repetition, a top-level alternation and an
///   abbreviated block distinguish each notation.
/// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
#[spec(ensures: |ret| !ret.is_empty())]
fn spelled(
    root: RegexView<'_>,
    abbreviations: &[Abbreviation<'_>],
    rule: RuleName,
) -> String
{
    match root.shape() {
        RegexShape::Alt(branches) if !branches.is_empty() => branches
            .into_iter()
            .map(|branch| spelled_whole(branch, abbreviations, rule))
            .collect::<Vec<_>>()
            .join(" ‖ "),
        RegexShape::Empty
        | RegexShape::Sym(_)
        | RegexShape::Seq(_)
        | RegexShape::Alt(_)
        | RegexShape::Optional(_)
        | RegexShape::Repeat(_) => spelled_whole(root, abbreviations, rule),
    }
}

/// `root` spelled whole, its parts abbreviated as [`spelled`] states. An
/// option or a repetition of an alternation takes the alternation's brackets
/// rather than a pair of its own.
///
/// # Specification
/// - requires: as [`spelled`].
/// - ensures: `root` itself is never abbreviated; each part is.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`spelled`].
/// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
#[spec(ensures: |ret| !ret.is_empty())]
fn spelled_whole(
    root: RegexView<'_>,
    abbreviations: &[Abbreviation<'_>],
    rule: RuleName,
) -> String
{
    let mut first = true;
    let answer: Result<Spelling, ()> = fold(
        root,
        |view| {
            if core::mem::take(&mut first) {
                return Visited::Open;
            }
            abbreviations
                .iter()
                .find(|abbreviation| abbreviation.name != rule && abbreviation.form == view)
                .map_or(Visited::Open, |abbreviation| {
                    Visited::Answer(Spelling::plain(format!("⟨{}⟩", abbreviation.name)))
                })
        },
        |node, children| {
            let joined = || {
                children
                    .iter()
                    .map(|child| child.text.as_str())
                    .collect::<Vec<_>>()
            };
            Ok(match node {
                Node::Empty => Spelling::plain("ε".to_owned()),
                Node::Hole(sort) => Spelling::plain(sort.name().to_string().to_uppercase()),
                Node::Tile(tile) => {
                    Spelling::plain(match tile_spelling(CandidateLabel::from(tile)) {
                        TileSpelling::Literal(text) => text.to_owned(),
                        TileSpelling::Class(class) => format!("‹{class}›"),
                    })
                },
                Node::Seq => Spelling::plain(joined().join(" ")),
                Node::Alt => Spelling {
                    text: format!("⦅ {} ⦆", joined().join(" ‖ ")),
                    group: Group::Bracketed,
                },
                Node::Optional => Spelling::suffixed(&children, Suffix::Optional),
                Node::Repeat => Spelling::suffixed(&children, Suffix::Repeat),
            })
        },
        (),
    );
    answer.map_or_else(|()| "ε".to_owned(), |spelling| spelling.text)
}

/// Whether a spelled part already stands in brackets of its own.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Group
{
    /// The part is an alternation, `⦅ … ⦆`, with nothing after it.
    Bracketed,
    /// Anything else.
    Open,
}

/// A part of a form, spelled.
#[derive(Clone, Debug)]
struct Spelling
{
    /// The text.
    text: String,
    /// Whether the text stands in brackets of its own.
    group: Group,
}

impl Spelling
{
    /// `text`, not bracketed.
    ///
    /// # Specification
    /// trivial.
    const fn plain(text: String) -> Self
    {
        Self {
            text,
            group: Group::Open,
        }
    }

    /// The one part of `children` followed by `suffix`, bracketed unless it
    /// already is.
    ///
    /// # Specification
    /// - requires: nothing; an option and a repetition hold one part.
    /// - ensures: a bracketed alternation takes `suffix` after its own closing
    ///   bracket; anything else is wrapped in `⦅ ⦆` first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an optional tile and a repeated alternation are
    ///   pinned spellings.
    /// - witness: `ledger::tests::a_form_spells_its_tiles_holes_and_parts`
    #[spec(ensures: |ret| ret.text.ends_with(&suffix.to_string()) && ret.group == Group::Open)]
    fn suffixed(
        children: &[Self],
        suffix: Suffix,
    ) -> Self
    {
        let text = match children {
            &[ref only] if only.group == Group::Bracketed => format!("{}{suffix}", only.text),
            _ => {
                let inner: Vec<&str> = children.iter().map(|child| child.text.as_str()).collect();
                format!("⦅ {} ⦆{suffix}", inner.join(" "))
            },
        };
        Self::plain(text)
    }
}

/// The mark an option or a repetition is written with.
#[derive(Clone, Copy, Debug)]
enum Suffix
{
    /// `?`: the part, or nothing.
    Optional,
    /// `*`: the part, any number of times.
    Repeat,
}

impl core::fmt::Display for Suffix
{
    /// Writes the mark.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Optional => "?",
            Self::Repeat => "*",
        })
    }
}

/// A form's tree and its tiles' roles, read together.
struct Tree
{
    /// The form as nested JSON nodes.
    value: Value,
    /// The roles of its tiles, each once, first use first.
    roles: Vec<String>,
}

/// The tree of `rule`'s form `root`, each tile paired with the next of
/// `molds`.
///
/// # Specification
/// - requires: `molds` are the rule's molds in mold order.
/// - ensures: every tile node names the mold paired with it, its spelling, its
///   tile kind and its role; the molds are paired in order and all used.
/// - fails: a tile whose paired mold has another label, a tile left without a
///   mold or a mold left without a tile, or a refused lookup.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Molds`] naming the rule, or [`LedgerFault::Grammar`].
///
/// # Adequacy
/// - hypothesis: L2 — every built-in rule pairs; a truncated mold list is
///   refused naming the rule.
/// - witness: `ledger::tests::every_rule_mold_and_attribute_has_one_row`
/// - witness: `ledger::tests::a_form_short_of_molds_is_refused`
#[spec(ensures: |ref ret| ret.as_ref().map_or_else(|fault| matches!(*fault, LedgerFault::Molds { rule: named } if named == rule.0) || matches!(*fault, LedgerFault::Grammar(_)), |tree| tree.value.is_object()))]
fn tree(
    pbg: &Pbg,
    roles: &RoleTable,
    rule: RuleName,
    root: RegexView<'_>,
    molds: &[MoldId],
) -> Result<Tree, LedgerFault>
{
    let RuleName(rule) = rule;
    let mut next = molds.iter();
    let mut seen: Vec<String> = Vec::new();
    let value = fold(
        root,
        |_| Visited::Open,
        |node, children| {
            Ok(match node {
                Node::Empty => json!({ "node": "empty" }),
                Node::Hole(sort) => json!({ "node": "hole", "sort": sort.name().to_string() }),
                Node::Tile(tile) => {
                    let &mold = next.next().ok_or(LedgerFault::Molds { rule })?;
                    let defined = pbg.mold(mold).map_err(LedgerFault::Grammar)?;
                    if defined.label != tile {
                        return Err(LedgerFault::Molds { rule });
                    }
                    let kind = pbg.tile_kind(mold).map_err(LedgerFault::Grammar)?;
                    let role = format!("{:?}", roles.role_of(mold).map_err(LedgerFault::Grammar)?);
                    if !seen.contains(&role) {
                        seen.push(role.clone());
                    }
                    let mut object = json!({
                        "node": "tile",
                        "label": tile,
                        "mold": u32::from(mold),
                        "kind": format!("{kind:?}"),
                        "role": role,
                    });
                    let spelling = match tile_spelling(CandidateLabel::from(tile)) {
                        TileSpelling::Literal(text) => ("literal", text),
                        TileSpelling::Class(class) => ("class", class),
                    };
                    if let Value::Object(ref mut fields) = object {
                        fields.insert(spelling.0.to_owned(), Value::from(spelling.1));
                    }
                    object
                },
                Node::Seq => json!({ "node": "seq", "items": children }),
                Node::Alt => json!({ "node": "alt", "items": children }),
                Node::Optional => json!({ "node": "optional", "items": children }),
                Node::Repeat => json!({ "node": "repeat", "items": children }),
            })
        },
        LedgerFault::Molds { rule },
    )?;
    if next.next().is_some() {
        return Err(LedgerFault::Molds { rule });
    }
    Ok(Tree { value, roles: seen })
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::RuleName;
    use gandr_surface_grammar::built_in;

    use super::Code;
    use super::Counted;
    use super::LedgerFault;
    use super::LedgerRun;
    use super::LedgerTask;
    use super::RuleRow;
    use super::Standing;
    use super::SyntaxLedger;
    use super::molds_by_rule;
    use super::standing::Internal;
    use super::tree;

    /// A directory of this test's own under the system's temporary directory,
    /// emptied first.
    ///
    /// # Specification
    /// trivial.
    fn scratch(name: &Path) -> PathBuf
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-ledger-{}-{}",
            std::process::id(),
            name.display()
        ));
        let _cleared = std::fs::remove_dir_all(&directory);
        directory
    }

    /// The row of the rule `name`.
    ///
    /// # Specification
    /// trivial.
    fn row(
        ledger: &SyntaxLedger,
        name: RuleName,
    ) -> &RuleRow
    {
        ledger
            .rules
            .iter()
            .find(|row| row.name == name.0)
            .unwrap_or_else(|| panic!("the ledger has a row for `{name}`"))
    }

    #[test]
    fn every_rule_mold_and_attribute_has_one_row()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let ledger = SyntaxLedger::build().expect("the ledger builds");
        let names: Vec<&str> = ledger.rules.iter().map(|row| row.name).collect();
        let expected: Vec<&str> = pbg.rules().iter().map(|rule| rule.name).collect();
        assert_eq!(names, expected, "one row per rule, in grammar order");
        let mut molds: Vec<u64> = Vec::new();
        let mut pending = ledger.rules.iter().map(|row| &row.tree).collect::<Vec<_>>();
        while let Some(node) = pending.pop() {
            if let Some(mold) = node.get("mold").and_then(serde_json::Value::as_u64) {
                molds.push(mold);
            }
            if let Some(items) = node.get("items").and_then(serde_json::Value::as_array) {
                pending.extend(items);
            }
        }
        molds.sort_unstable();
        let count = u64::try_from(pbg.iter_molds().count()).expect("the mold count fits");
        let every: Vec<u64> = (0 .. count).collect();
        assert_eq!(molds, every, "every mold names exactly one tile");
        assert_eq!(ledger.molds, every.len());
        let attributes: Vec<&str> = ledger
            .attributes
            .iter()
            .map(|row| row.name.as_str())
            .collect();
        assert_eq!(
            attributes,
            [
                "checks",
                "owes",
                "refuses",
                "runs",
                "normalizes",
                "doc",
                "explicit_exits",
                "explicit_runs",
                "respects",
                "entry",
                "form"
            ],
            "one row per registered attribute, in registry order"
        );
    }

    #[test]
    fn a_form_short_of_molds_is_refused()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let roles = gandr_surface_grammar::RoleTable::build(&pbg).expect("the role table builds");
        let molds = molds_by_rule(&pbg).expect("every mold has its rule");
        let rule = pbg.rules().first().expect("the grammar has rules");
        let all = molds.first().expect("the first rule has molds");
        let short = all.get(.. all.len().saturating_sub(1)).unwrap_or_default();
        let refused = tree(
            &pbg,
            &roles,
            RuleName(rule.name),
            rule.regex().view(),
            short,
        );
        assert!(
            matches!(refused, Err(LedgerFault::Molds { rule: named }) if named == rule.name),
            "a tile left without a mold is refused naming the rule"
        );
        let shifted = all.get(1 ..).unwrap_or_default();
        let refused = tree(
            &pbg,
            &roles,
            RuleName(rule.name),
            rule.regex().view(),
            shifted,
        );
        assert!(
            matches!(refused, Err(LedgerFault::Molds { .. })),
            "a mold paired with a tile of another label is refused"
        );
    }

    #[test]
    fn a_form_spells_its_tiles_holes_and_parts()
    {
        let ledger = SyntaxLedger::build().expect("the ledger builds");
        let form = |name| row(&ledger, RuleName(name)).form.as_str();
        assert_eq!(form("world_declaration"), "world ‹identifier› ;");
        assert_eq!(
            form("import_declaration"),
            "import ⟨string.pattern⟩ ⦅ as ‹identifier› ⦆? ;"
        );
        assert_eq!(form("binary_expression.or"), "EXPRESSION || EXPRESSION");
        assert_eq!(form("boolean.pattern"), "true ‖ false");
        assert_eq!(form("hole"), "? ⦅ ‹hole_name› ⦆?");
        assert_eq!(
            form("string.pattern"),
            "\" ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* \""
        );
        assert!(
            form("lambda_expression").contains("⟨block⟩"),
            "a part equal to the block's whole form is written as the block"
        );
        assert!(
            !form("block").contains("⟨block⟩"),
            "a form is never written as itself"
        );
        assert_eq!(Code("a | b").to_string(), "`a \\| b`");
        assert_eq!(Code("x").to_string(), "`x`");
        assert_eq!(
            Counted {
                count: 1,
                noun: "rule"
            }
            .to_string(),
            "1 rule"
        );
        assert_eq!(
            Counted {
                count: 2,
                noun: "rule"
            }
            .to_string(),
            "2 rules"
        );
    }

    #[test]
    fn every_internal_rule_has_its_derived_reason()
    {
        let ledger = SyntaxLedger::build().expect("the ledger builds");
        let internal: Vec<(&str, Internal)> = ledger
            .rules
            .iter()
            .filter_map(|row| match row.standing {
                Standing::Internal(reason) => Some((row.name, reason)),
                Standing::Committed => None,
            })
            .collect();
        let shadowed = |by| Internal::Shadowed { by };
        let captured = |tile, by| Internal::Captured { tile, by };
        assert_eq!(internal, [
            ("instantiation.type", Internal::Tileless),
            ("constructor.pattern", shadowed("constructor_pattern")),
            ("boolean.pattern", shadowed("literal_pattern")),
            ("number.pattern", shadowed("literal_pattern")),
            ("typed_number.pattern", shadowed("literal_pattern")),
            ("string.pattern", shadowed("literal_pattern")),
            ("escape_sequence", Internal::Enclosed {
                class: "escape_sequence"
            }),
            ("block_comment", Internal::Layout { tile: "/*" }),
            ("shell_list", captured("shell_or", "identifier.expression")),
            (
                "or_expression",
                captured("shell_and", "identifier.expression")
            ),
            (
                "and_expression",
                captured("pipeline_operand", "identifier.expression")
            ),
            ("negation", captured("negation", "identifier.expression")),
        ]);
    }

    #[test]
    fn both_files_carry_the_fingerprint_and_every_row()
    {
        let ledger = SyntaxLedger::build().expect("the ledger builds");
        let markdown = ledger.markdown();
        assert_eq!(
            markdown.matches(&ledger.fingerprint).count(),
            1,
            "the header names the fingerprint"
        );
        for row in &ledger.rules {
            let cell = match row.standing {
                Standing::Committed => {
                    format!("| [`{0}`](exemplars/syntax/{0}.gandr) |", row.name)
                },
                Standing::Internal(_) => format!("| `{}` |", row.name),
            };
            assert!(markdown.contains(&cell), "`{}` has a row", row.name);
        }
        for row in &ledger.attributes {
            assert!(markdown.contains(&format!(
                "| [`{0}`](exemplars/attributes/{0}.gandr) |",
                row.name
            )));
        }
        assert!(
            markdown.contains("`EXPRESSION \\|\\| EXPRESSION`"),
            "a bar in a form is escaped"
        );
        let json = ledger.json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("the machine form is JSON");
        assert_eq!(parsed["fingerprint"], ledger.fingerprint.as_str());
        let rules = parsed["rules"].as_array().expect("rules are an array");
        assert_eq!(rules.len(), ledger.rules.len());
        assert_eq!(rules[0]["name"], ledger.rules[0].name);
        let attributes = parsed["attributes"]
            .as_array()
            .expect("attributes are an array");
        assert_eq!(attributes.len(), ledger.attributes.len());
        assert_eq!(
            json.lines()
                .filter(|line| line.starts_with("    {"))
                .count(),
            ledger.rules.len() + ledger.attributes.len(),
            "each element is a line of its own"
        );
    }

    #[test]
    fn a_run_writes_both_files_and_repeats_them_exactly()
    {
        let directory = scratch(Path::new("run"));
        let task = LedgerTask::Syntax {
            directory: directory.clone(),
        };
        let Ok(LedgerRun::Written(paths)) = task.run()
        else {
            panic!("the ledger is written");
        };
        assert_eq!(paths, [
            directory.join("syntax.md"),
            directory.join("syntax.json")
        ]);
        let ledger = SyntaxLedger::build().expect("the ledger builds");
        let first = (
            std::fs::read_to_string(directory.join("syntax.md")).expect("the reading form"),
            std::fs::read_to_string(directory.join("syntax.json")).expect("the machine form"),
        );
        assert_eq!(first, (ledger.markdown(), ledger.json()));
        task.run().expect("the ledger is written again");
        let second = (
            std::fs::read_to_string(directory.join("syntax.md")).expect("the reading form"),
            std::fs::read_to_string(directory.join("syntax.json")).expect("the machine form"),
        );
        assert_eq!(first, second, "a second run writes the same bytes");
        std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    }

    #[test]
    fn an_unwritable_directory_is_refused_by_path()
    {
        let directory = scratch(Path::new("unwritable"));
        std::fs::create_dir_all(&directory).expect("the scratch directory");
        let file = directory.join("file");
        std::fs::write(&file, "").expect("a file in the way");
        let under = file.join("ledger");
        let refused = LedgerTask::Syntax {
            directory: under.clone(),
        }
        .run();
        assert!(
            matches!(refused, Err(LedgerFault::Unwritable { ref path, .. }) if *path == under),
            "a directory under a file is refused naming it"
        );
        std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    }
}
