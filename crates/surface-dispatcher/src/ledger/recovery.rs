//! The recovery sweep: every syntax exemplar, one tile at a time, written
//! wrong.
//!
//! # A mistake is reported where it was made
//!
//! [`sweep`] reads each exemplar under `syntax/`, labels it, and makes two
//! mutants of every token that is a literal tile of the grammar (a keyword, a
//! punctuation tile, a string's quote): the tile written as its near miss, and
//! the tile deleted. Each mutant is checked as `gandr check` checks it, and the
//! first error it reports must mark the mutation: its primary span must touch
//! the mutation's site. A near miss's site is the bytes written in the tile's
//! place. A deletion's is the layout between the tokens either side, since a
//! tile found missing can only be reported at the end of what came before it
//! or the start of what comes after. A mutant whose first error marks other
//! bytes, or marks none, is a finding. A mutant the checker accepts is counted
//! and not a finding: a deleted optional tile, or a near miss that spells
//! another form, is no mistake. Nor is a mutant that leaves a well-formed
//! source, one the lowering reads with no refusal but for a name no
//! declaration answers, though the check refuses it (#2340): `-> -F
//! +{Integer}` less `Integer` is the empty sum, a type the corpus writes on
//! purpose, and the first ill-typed term is then the body's injection; `def
//! rec f` less `rec` is a definition that cannot call itself, and its own
//! call is unresolved. So is a source whose lowering refuses a form only for
//! what it means where it stands (#3332): `loop` deleted leaves its `break`
//! outside any loop, `break` deleted leaves the statement after an endless
//! loop unreached, and `rec` deleted leaves a descent claim outside a
//! recursive group. With no mistake of form left, the first refusal is
//! where the source goes wrong by construction, so it is counted well formed
//! beside the accepted, not filed.
//!
//! A tile's near miss is derived, never listed: the first of its text with the
//! last character dropped, its last two characters swapped, and its last
//! character doubled that spells no literal tile of the grammar. A tile none of
//! those miss is swept by deletion alone. The table of near misses leads the
//! report, so a reader sees what each tile was mistaken for.
//!
//! - Choice: the mutants are written under a scratch `ledger` directory and
//!   walked as `check` walks, so the report is what a user who made the mistake
//!   reads, the exemplars' expectations included.
//! - Alternatives: parsing each mutant alone and reading the parser's
//!   obligations, which misses every report the lowering and the checker make;
//!   a hand-written table of near misses, which drifts from the grammar. The
//!   parser's own drop sweep (`gandr-surface-parser`'s
//!   `sweeps::dropped_tokens_recover_no_worse_than_the_record`) holds every
//!   dropped token's obligation and node counts to a record; it says how much
//!   the parse recovers, and this sweep where the user is told.
//! - Reversal: a sweep that must run on every pull request checks its mutants
//!   in memory, without the scratch directory.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_corpus::Refusal;
use gandr_surface_diagnostics::Severity;
use gandr_surface_grammar::Ascii;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::SPELLED;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_parser::CandidateLabel;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::TileSpelling;
use gandr_surface_parser::Token;
use gandr_surface_parser::label;
use gandr_surface_parser::tile_spelling;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::LedgerFault;
use super::exemplars::listed;
use crate::compose::Composed;
use crate::entry::entries;
use crate::pool::Pool;
use crate::report::Goals;
use crate::report::Verb;
use crate::walk::Step;
use crate::walk::Walk;
use crate::width::Width;

/// The directory of rule exemplars under the exemplar directory.
const SYNTAX: &str = "syntax";

/// The extension every exemplar carries.
const EXTENSION: &str = "gandr";

/// The sweeps begun in this process: each names its own scratch directory, so
/// two sweeps in one process, as the tests run them, never write over each
/// other's mutants.
static SWEEPS: AtomicUsize = AtomicUsize::new(0);

/// How a mutant writes its tile wrong.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Mutation
{
    /// The tile written as its near miss.
    Missed(String),
    /// The tile left out.
    Deleted,
}

impl core::fmt::Display for Mutation
{
    /// Writes ``written as `<miss>` `` or `deleted`.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Missed(ref text) => write!(f, "written as `{text}`"),
            Self::Deleted => f.write_str("deleted"),
        }
    }
}

/// The bytes a mutation is sited at, in its mutant's text.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Site
{
    /// The first byte.
    start: usize,
    /// One past the last byte; equal to `start` for an empty site.
    end: usize,
}

impl core::fmt::Display for Site
{
    /// Writes `start..end`.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// One mutant of one exemplar, before it is checked.
#[derive(Clone, Debug)]
struct Mutant
{
    /// The exemplar it was made from.
    exemplar: PathBuf,
    /// The tile written wrong, as the exemplar writes it.
    tile: String,
    /// Where the tile starts in the exemplar.
    at: usize,
    /// How it is written wrong.
    mutation: Mutation,
    /// The mutant's text.
    text: String,
    /// Where the mutation lies in that text.
    site: Site,
}

/// The first error a mutant's check reported.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Reported
{
    /// The refusal or lint it names, when it names one.
    name: Option<String>,
    /// What it leads with.
    message: String,
    /// Its primary span, measured in the mutant's own text, when it has one.
    span: Option<Site>,
    /// Whether the mutant was well formed: the lowering read every
    /// declaration and refused none but for what a well-formed form means
    /// where it stands, so the first error is a meaning's, not a form's.
    formed: bool,
}

/// Whether a cause's mutants deleted their tile or missed it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Kind
{
    /// The tile left out.
    Deleted,
    /// The tile written as its near miss.
    Missed,
}

/// What a finding is filed under: one issue per cause, not per finding.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Cause
{
    /// The first error's name, or `unnamed`.
    name: String,
    /// How the tile was written wrong.
    kind: Kind,
}

impl core::fmt::Display for Cause
{
    /// Writes ``` `<name>` deleted ``` or ``` `<name>` missed ```.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let kind = match self.kind {
            Kind::Deleted => "deleted",
            Kind::Missed => "missed",
        };
        write!(f, "`{}` {kind}", self.name)
    }
}

/// A mutant whose first error does not mark its mutation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryFinding
{
    /// The exemplar the mutant was made from.
    exemplar: PathBuf,
    /// The tile written wrong.
    tile: String,
    /// Where the tile starts in the exemplar.
    at: usize,
    /// How it was written wrong.
    mutation: Mutation,
    /// Where the mutation lies in the mutant.
    site: Site,
    /// What the check reported first.
    reported: Reported,
}

impl core::fmt::Display for RecoveryFinding
{
    /// Writes the exemplar's path and the tile's byte, the tile and how it was
    /// written wrong, then the first error's name and the span it marks beside
    /// the mutation's site, or that it marks none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{}:{}: `{}` {}: first error ",
            self.exemplar.display(),
            self.at,
            self.tile,
            self.mutation,
        )?;
        match self.reported.name {
            Some(ref name) => write!(f, "`{name}`")?,
            None => write!(f, "\"{}\"", self.reported.message)?,
        }
        match self.reported.span {
            Some(span) => write!(f, " at {span}, not at {}", self.site),
            None => write!(f, " with no span, not at {}", self.site),
        }
    }
}

impl RecoveryFinding
{
    /// What the finding is filed under: its first error's name, `unnamed` for
    /// an error that names no refusal or lint, and whether its tile was
    /// deleted or missed.
    ///
    /// # Specification
    /// trivial.
    fn cause(&self) -> Cause
    {
        Cause {
            name: self
                .reported
                .name
                .clone()
                .unwrap_or_else(|| "unnamed".to_owned()),
            kind: match self.mutation {
                Mutation::Missed(_) => Kind::Missed,
                Mutation::Deleted => Kind::Deleted,
            },
        }
    }

    /// The exemplar's family: its file's name up to the first dot, the rule
    /// its variants share.
    ///
    /// # Specification
    /// trivial.
    fn family(&self) -> String
    {
        self.exemplar
            .file_name()
            .and_then(std::ffi::OsStr::to_str)
            .and_then(|name| name.split('.').next())
            .unwrap_or_default()
            .to_owned()
    }
}

/// What a sweep of the syntax exemplars found.
#[derive(Clone, Debug, Default)]
pub struct RecoveryReport
{
    /// Each literal tile the exemplars write, with its near miss; none for a
    /// tile every derivation spells as another tile.
    near_misses: BTreeMap<String, Option<String>>,
    /// How many mutants were checked.
    swept: usize,
    /// How many the checker accepted.
    accepted: usize,
    /// How many mutants left a well-formed source the check refused: no
    /// mistake of form is left to mark, so the first refusal is where the
    /// source now goes wrong.
    formed: usize,
    /// The mutants whose first error does not mark their mutation, in
    /// exemplar and byte order.
    findings: Vec<RecoveryFinding>,
}

impl RecoveryReport
{
    /// The mutants whose first error does not mark their mutation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn findings(&self) -> &[RecoveryFinding]
    {
        &self.findings
    }
}

impl core::fmt::Display for RecoveryReport
{
    /// Writes the near-miss table, one ``near miss: `<tile>` → `<miss>` `` line
    /// per tile (`—` for a tile with none), then each finding, then one
    /// ``cause: `<name>` <kind>`` line per cause with its count and families,
    /// the largest first, then the count swept, marked where made, accepted,
    /// well formed and marked elsewhere.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        for (tile, miss) in &self.near_misses {
            match *miss {
                Some(ref miss) => writeln!(f, "near miss: `{tile}` → `{miss}`")?,
                None => writeln!(f, "near miss: `{tile}` → —")?,
            }
        }
        for finding in &self.findings {
            writeln!(f, "{finding}")?;
        }
        let mut causes: BTreeMap<Cause, (usize, BTreeSet<String>)> = BTreeMap::new();
        for finding in &self.findings {
            let &mut (ref mut count, ref mut families) = causes.entry(finding.cause()).or_default();
            *count = count.saturating_add(1);
            let _new = families.insert(finding.family());
        }
        let mut ranked: Vec<(&Cause, &(usize, BTreeSet<String>))> = causes.iter().collect();
        ranked.sort_by_key(|&(cause, &(count, _))| (core::cmp::Reverse(count), cause));
        for (cause, &(count, ref families)) in ranked {
            write!(
                f,
                "cause: {cause}: {count} mutants in {} families: ",
                families.len()
            )?;
            for (index, family) in families.iter().enumerate() {
                if index > 0 {
                    f.write_str(", ")?;
                }
                f.write_str(family)?;
            }
            writeln!(f)?;
        }
        let found = self.findings.len();
        write!(
            f,
            "{} mutants swept: {} marked where they were made, {} accepted, {} well formed, {found} marked elsewhere",
            self.swept,
            self.swept
                .saturating_sub(self.accepted)
                .saturating_sub(self.formed)
                .saturating_sub(found),
            self.accepted,
            self.formed,
        )
    }
}

/// The texts of a grammar's literal tiles, as [`literal_tiles`] reads them.
#[repr(transparent)]
#[derive(Clone, Debug)]
struct Literals(BTreeSet<&'static str>);

/// Every literal tile of `pbg`: the text of each mold's tile written as text,
/// and the ASCII token of each glyph tile.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a mold's label is held exactly when the parser spells it
///   literally; an ASCII spelling is held exactly when it is a token.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the built-in grammar's keywords, punctuation and glyph
///   tokens are held, and no class tile is.
/// - witness: `ledger::recovery::tests::every_near_miss_is_one_edit_from_its_tile_and_no_tile`
#[spec(ensures: |ret| SPELLED.iter().all(|spelled| match spelled.ascii {
    Ascii::Token(LabelText(text)) => ret.0.contains(text),
    Ascii::Head(_) => true,
}))]
fn literal_tiles(pbg: &Pbg) -> Literals
{
    let mut literals: BTreeSet<&'static str> = pbg
        .iter_molds()
        .filter_map(
            |(_, mold)| match tile_spelling(CandidateLabel::from(mold.label)) {
                TileSpelling::Literal(_) => Some(mold.label),
                TileSpelling::Class(_) => None,
            },
        )
        .collect();
    for spelled in SPELLED {
        if let Ascii::Token(LabelText(text)) = spelled.ascii {
            let _new = literals.insert(text);
        }
    }
    Literals(literals)
}

/// The near miss of the tile written `tile`: the first of its text with the
/// last character dropped, its last two characters swapped and its last
/// character doubled that is not empty, differs from the tile and is held in
/// no entry of `literals`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a present answer is one edit from `tile`, non-empty, and held in
///   no entry of `literals`; absent when every derivation is a literal tile or
///   empty.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every literal tile of the built-in grammar, the ones
///   whose dropped spelling is a tile among them.
/// - witness: `ledger::recovery::tests::every_near_miss_is_one_edit_from_its_tile_and_no_tile`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|miss| !miss.is_empty() && miss.as_str() != tile.0 && !literals.0.contains(miss.as_str())))]
fn near_miss(
    tile: LabelText<'_>,
    literals: &Literals,
) -> Option<String>
{
    let characters: Vec<char> = tile.0.chars().collect();
    let dropped: String = characters
        .iter()
        .take(characters.len().saturating_sub(1))
        .collect();
    let swapped: String = match *characters.as_slice() {
        [ref head @ .., last_but_one, last] => {
            head.iter().copied().chain([last, last_but_one]).collect()
        },
        _ => String::new(),
    };
    let doubled: String = characters
        .iter()
        .copied()
        .chain(characters.last().copied())
        .collect();
    [dropped, swapped, doubled].into_iter().find(|candidate| {
        !candidate.is_empty()
            && candidate.as_str() != tile.0
            && !literals.0.contains(candidate.as_str())
    })
}

/// The mutants of the exemplar at `exemplar` whose text is `text`: a near miss
/// and a deletion of each token that is a literal tile.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one deletion per token whose text is held in `literals` or that
///   is a punctuation tile or a quote, and one near miss of each that has one;
///   a near miss's site is its written bytes, a deletion's the layout between
///   the tokens either side of it, in the mutant's text.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a definition's keyword, its `=` and its closing `;` are
///   each deleted and missed, with the deletion of the last sited from the end
///   of the value to the end of the text.
/// - witness: `ledger::recovery::tests::a_deletion_is_sited_between_its_neighbours`
#[spec(ensures: |ref ret| ret.iter().all(|mutant| mutant.site.start <= mutant.site.end && mutant.site.end <= mutant.text.len()))]
fn mutants(
    exemplar: &Path,
    text: SourceText<'_>,
    literals: &Literals,
    near_misses: &mut BTreeMap<String, Option<String>>,
) -> Vec<Mutant>
{
    let text = <&str>::from(text);
    let tokens = label(SourceFragment::from(text));
    let written: Vec<(Token, usize, usize)> = tokens
        .iter()
        .filter(|token| !matches!(token.lexeme, Lexeme::Space))
        .filter_map(|&token| {
            Some((
                token,
                usize::try_from(token.start).ok()?,
                usize::try_from(token.end).ok()?,
            ))
        })
        .collect();
    let mut made = Vec::new();
    for (index, &(token, start, end)) in written.iter().enumerate() {
        let Some(tile) = text.get(start .. end)
        else {
            continue;
        };
        let literal = matches!(token.lexeme, Lexeme::Punct | Lexeme::Quote)
            || (matches!(token.lexeme, Lexeme::LowerWord | Lexeme::UpperWord)
                && literals.0.contains(tile));
        if !literal {
            continue;
        }
        let (Some(before), Some(after)) = (text.get(.. start), text.get(end ..))
        else {
            continue;
        };
        let miss = near_misses
            .entry(tile.to_owned())
            .or_insert_with(|| near_miss(LabelText(tile), literals))
            .clone();
        if let Some(miss) = miss {
            made.push(Mutant {
                exemplar: exemplar.to_path_buf(),
                tile: tile.to_owned(),
                at: start,
                site: Site {
                    start,
                    end: start.saturating_add(miss.len()),
                },
                text: format!("{before}{miss}{after}"),
                mutation: Mutation::Missed(miss),
            });
        }
        let previous = index
            .checked_sub(1)
            .and_then(|previous| written.get(previous))
            .map_or(0, |&(_, _, previous_end)| previous_end);
        let removed = end.saturating_sub(start);
        let next = written
            .get(index.saturating_add(1))
            .map_or(text.len(), |&(_, next_start, _)| next_start)
            .saturating_sub(removed);
        made.push(Mutant {
            exemplar: exemplar.to_path_buf(),
            tile: tile.to_owned(),
            at: start,
            mutation: Mutation::Deleted,
            text: format!("{before}{after}"),
            site: Site {
                start: previous,
                end: next,
            },
        });
    }
    made
}

/// Sweep the syntax exemplars under `directory`: every literal tile of every
/// exemplar written as its near miss and deleted, each mutant checked, and
/// each whose first error does not mark its mutation reported.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one mutant per tile and mutation as [`mutants`] makes them, each
///   checked as `check` checks a source under a `ledger` directory; a mutant is
///   accepted when the check reports no error, counted well formed when the
///   lowering refused none of its declarations but for an unresolved name, a
///   loop's exit outside any loop, an unreachable statement or a descent claim
///   outside a recursive group, and its first error does not mark the site, and
///   a finding otherwise when its first error's primary span neither overlaps
///   nor touches the mutation's site, or the error has none. The scratch
///   directory the mutants are written under is removed.
/// - fails: the exemplars cannot be listed or read, or the mutants cannot be
///   written.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Unreadable`] naming the folder, [`LedgerFault::Unshown`]
/// naming an exemplar, or [`LedgerFault::Unwritable`] naming the scratch
/// directory.
///
/// # Adequacy
/// - hypothesis: L3 — a definition's exemplar is swept tile by tile, every
///   mutant counted and each first error read against its site; a deletion
///   leaving another well-formed declaration whose body the checker refuses, a
///   `rec` deleted or a declaration's keyword name missed, leaving only
///   unresolved names, and a `loop`, `break` or `rec` deleted, leaving an exit
///   outside any loop, a statement no path reaches or a descent claim outside a
///   recursive group, are counted well formed, not filed.
/// - witness: `ledger::recovery::tests::a_definition_is_swept_tile_by_tile`
/// - witness: `ledger::recovery::tests::a_deletion_leaving_a_well_formed_source_is_no_finding_2340`
/// - witness: `ledger::recovery::tests::a_mutant_leaving_only_unresolved_names_is_no_finding_2876`
/// - witness: `ledger::recovery::tests::a_deleted_licence_leaves_a_well_formed_source_3332`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |report| report.accepted.saturating_add(report.formed).saturating_add(report.findings.len()) <= report.swept))]
pub(super) fn sweep(
    pbg: &Pbg,
    directory: &Path,
) -> Result<RecoveryReport, LedgerFault>
{
    let literals = literal_tiles(pbg);
    let mut report = RecoveryReport::default();
    let mut made = Vec::new();
    for path in listed(&directory.join(SYNTAX))? {
        if path.extension().and_then(std::ffi::OsStr::to_str) != Some(EXTENSION) {
            continue;
        }
        let text = std::fs::read_to_string(&path).map_err(|error| LedgerFault::Unshown {
            path: path.clone(),
            error: error.to_string(),
        })?;
        made.extend(mutants(
            &path,
            SourceText::from(text.as_str()),
            &literals,
            &mut report.near_misses,
        ));
    }
    let scratch = std::env::temp_dir().join(format!(
        "gandr-recovery-{}-{}",
        std::process::id(),
        SWEEPS.fetch_add(1, Ordering::Relaxed)
    ));
    let folder = scratch.join("ledger");
    let unwritable = |error| LedgerFault::Unwritable {
        path: folder.clone(),
        error,
    };
    std::fs::create_dir_all(&folder).map_err(unwritable)?;
    for (index, mutant) in made.iter().enumerate() {
        std::fs::write(folder.join(format!("{index}.{EXTENSION}")), &mutant.text)
            .map_err(unwritable)?;
    }
    let mut reported: Vec<Option<Reported>> = vec![None; made.len()];
    let ControlFlow::Continue(_run) = Walk::new(vec![folder.clone()]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            if let Step::Source {
                path, ref composed, ..
            } = step
            {
                // Well formed: the lowering read the source and refused no
                // declaration of it but for what a well-formed form means
                // where it stands — a name no declaration answers, a loop's
                // exit outside any loop, a statement no path reaches, or a
                // descent claim outside a recursive group — so what the check
                // reports is a meaning, not a form.
                let formed = matches!(
                    *composed,
                    Composed::Settled {
                        ref report,
                        ref unstatable,
                        ..
                    } if unstatable.is_empty()
                        && report.declarations().iter().all(|declaration| {
                            !matches!(
                                declaration.produced().refusal(),
                                Maybe::Present(Refusal::Lowering(ref refused))
                                    if !matches!(
                                        *refused,
                                        LoweringRefusal::UnresolvedName { .. }
                                            | LoweringRefusal::OutsideLoop { .. }
                                            | LoweringRefusal::Unreachable { .. }
                                            | LoweringRefusal::OutOfFragment {
                                                boundary: FragmentBoundary::ForeignClaim,
                                                ..
                                            }
                                    )
                            )
                        })
                );
                let index = path
                    .file_stem()
                    .and_then(std::ffi::OsStr::to_str)
                    .and_then(|stem| stem.parse::<usize>().ok());
                // An entry's span is measured from the source's own first
                // byte, past the prelude laid before it.
                let first = entries(&step, Verb::Check(Goals::Gated))
                    .find(|diagnostic| diagnostic.severity == Severity::Error);
                if let (Some(slot), Some(diagnostic)) =
                    (index.and_then(|index| reported.get_mut(index)), first)
                {
                    *slot = Some(Reported {
                        name: match diagnostic.identifier {
                            Maybe::Present(ref identifier) => Some(identifier.to_string()),
                            Maybe::Absent(_) => None,
                        },
                        message: diagnostic.message.text.clone(),
                        span: match diagnostic.span {
                            Maybe::Present(span) => Some(Site {
                                start: usize::from(span.start()),
                                end: usize::from(span.end()),
                            }),
                            Maybe::Absent(_) => None,
                        },
                        formed,
                    });
                }
            }
            ControlFlow::Continue(())
        },
    );
    std::fs::remove_dir_all(&scratch).map_err(unwritable)?;
    report.swept = made.len();
    for (mutant, first) in made.into_iter().zip(reported) {
        let Some(first) = first
        else {
            report.accepted = report.accepted.saturating_add(1);
            continue;
        };
        let marked = first
            .span
            .is_some_and(|span| span.start <= mutant.site.end && mutant.site.start <= span.end);
        if !marked && first.formed {
            report.formed = report.formed.saturating_add(1);
        }
        else if !marked {
            report.findings.push(RecoveryFinding {
                exemplar: mutant.exemplar,
                tile: mutant.tile,
                at: mutant.at,
                mutation: mutant.mutation,
                site: mutant.site,
                reported: first,
            });
        }
    }
    Ok(report)
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::LabelText;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;

    use super::Mutation;
    use super::RecoveryFinding;
    use super::RecoveryReport;
    use super::Reported;
    use super::Site;
    use super::literal_tiles;
    use super::mutants;
    use super::near_miss;
    use super::sweep;

    #[test]
    fn every_near_miss_is_one_edit_from_its_tile_and_no_tile()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let literals = literal_tiles(&pbg);
        for keyword in ["def", "=", ";", "::", "<~>", "@["] {
            assert!(
                literals.0.contains(keyword),
                "`{keyword}` is a literal tile"
            );
        }
        assert!(
            !literals.0.contains("Iso"),
            "a glyph's ASCII head is an identifier, not a tile"
        );
        assert_eq!(
            near_miss(LabelText("def"), &literals).as_deref(),
            Some("de")
        );
        for &tile in &literals.0 {
            let Some(miss) = near_miss(LabelText(tile), &literals)
            else {
                continue;
            };
            assert!(
                !literals.0.contains(miss.as_str()),
                "`{tile}` misses as `{miss}`, a tile"
            );
            let (tile_length, miss_length) = (tile.chars().count(), miss.chars().count());
            assert!(
                tile_length.abs_diff(miss_length) <= 1,
                "`{tile}` misses as `{miss}`, more than one edit away"
            );
        }
    }

    #[test]
    fn a_deletion_is_sited_between_its_neighbours()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let literals = literal_tiles(&pbg);
        let text = "def answer = 42 ;\n";
        let made = mutants(
            Path::new("def-value.gandr"),
            SourceText::from(text),
            &literals,
            &mut BTreeMap::new(),
        );
        let deleted: Vec<(&str, Site, &str)> = made
            .iter()
            .filter(|mutant| mutant.mutation == Mutation::Deleted)
            .map(|mutant| (mutant.tile.as_str(), mutant.site, mutant.text.as_str()))
            .collect();
        assert_eq!(deleted, [
            ("def", Site { start: 0, end: 1 }, " answer = 42 ;\n"),
            ("=", Site { start: 10, end: 12 }, "def answer  42 ;\n"),
            (";", Site { start: 15, end: 17 }, "def answer = 42 \n"),
        ]);
        let missed: Vec<(&str, &Mutation, Site)> = made
            .iter()
            .filter(|mutant| mutant.mutation != Mutation::Deleted)
            .map(|mutant| (mutant.tile.as_str(), &mutant.mutation, mutant.site))
            .collect();
        assert_eq!(
            missed.first(),
            Some(&("def", &Mutation::Missed("de".to_owned()), Site {
                start: 0,
                end: 2
            }))
        );
    }

    #[test]
    fn findings_are_filed_by_cause_the_largest_first()
    {
        let finding = |exemplar: &str, name: Option<&str>, mutation: Mutation| RecoveryFinding {
            exemplar: PathBuf::from(exemplar),
            tile: "=".to_owned(),
            at: 0,
            mutation,
            site: Site { start: 0, end: 1 },
            reported: Reported {
                name: name.map(str::to_owned),
                message: "a message".to_owned(),
                span: Some(Site { start: 9, end: 9 }),
                formed: false,
            },
        };
        let report = RecoveryReport {
            findings: vec![
                finding("syntax/sum-type.gandr", None, Mutation::Deleted),
                finding(
                    "syntax/binary-expression.add.gandr",
                    Some("MalformedForm"),
                    Mutation::Deleted,
                ),
                finding(
                    "syntax/binary-expression.cons.gandr",
                    Some("MalformedForm"),
                    Mutation::Deleted,
                ),
                finding(
                    "syntax/path-type.gandr",
                    Some("MalformedForm"),
                    Mutation::Deleted,
                ),
                finding(
                    "syntax/path-type.gandr",
                    Some("MalformedForm"),
                    Mutation::Missed("==".to_owned()),
                ),
            ],
            ..RecoveryReport::default()
        };
        let causes: Vec<String> = report
            .to_string()
            .lines()
            .filter(|line| line.starts_with("cause: "))
            .map(str::to_owned)
            .collect();
        assert_eq!(causes, [
            "cause: `MalformedForm` deleted: 3 mutants in 2 families: binary-expression, path-type",
            "cause: `MalformedForm` missed: 1 mutants in 1 families: path-type",
            "cause: `unnamed` deleted: 1 mutants in 1 families: sum-type",
        ]);
    }

    #[test]
    fn a_definition_is_swept_tile_by_tile()
    {
        let scratch = std::env::temp_dir().join(format!(
            "gandr-recovery-test-{}-definition",
            std::process::id()
        ));
        let folder = scratch.join("syntax");
        std::fs::create_dir_all(&folder).expect("the scratch folder");
        std::fs::write(
            folder.join("def-value.gandr"),
            "/// `def_value`: a definition.\n@[ checks ]\ndef answer = 42 ;\n",
        )
        .expect("the exemplar is written");
        let pbg = built_in().expect("the built-in grammar builds");
        let report = sweep(&pbg, &scratch).expect("the sweep runs");
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
        assert_eq!(
            report.swept,
            report
                .near_misses
                .values()
                .filter(|miss| miss.is_some())
                .count()
                + report.near_misses.len(),
            "each tile, written once, is deleted, and missed where it has a miss: {report}"
        );
        assert!(report.findings.is_empty(), "{report}");
    }

    /// #2340: `Integer` deleted from `-> -F +{Integer}` leaves the empty sum,
    /// a well-formed type, and the checker's first refusal is the body's
    /// injection at a summand the empty sum lacks. No mistake of form is left
    /// to mark, so the mutant is counted well formed and not filed.
    #[test]
    fn a_deletion_leaving_a_well_formed_source_is_no_finding_2340()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-recovery-test-{}-formed", std::process::id()));
        let folder = scratch.join("syntax");
        std::fs::create_dir_all(&folder).expect("the scratch folder");
        std::fs::write(
            folder.join("labelled-sum-expression.gandr"),
            "/// `labelled_sum_expression`: a labelled sum injection.\n@[ checks ]\ndef one() -> \
             -F +{Integer} {\n  return +{.0 = 1}\n}\n",
        )
        .expect("the exemplar is written");
        let pbg = built_in().expect("the built-in grammar builds");
        let report = sweep(&pbg, &scratch).expect("the sweep runs");
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
        assert!(
            report.findings.iter().all(
                |finding| !(finding.tile == "Integer" && finding.mutation == Mutation::Deleted)
            ),
            "the empty sum the deletion leaves is well formed: {report}"
        );
        assert_eq!(report.formed, 1_usize, "{report}");
        assert!(
            report.findings.len()
                < report
                    .swept
                    .saturating_sub(report.accepted)
                    .saturating_sub(report.formed),
            "the rest is still read against its site: {report}"
        );
    }

    /// #2875: a mistake in a module member or a `rec` group's closing brace
    /// leaves a refusal resting on the repair (the signature's member the
    /// repair dropped, the name the early close moved out of the group)
    /// admitted before the repaired form. Each of these mutants' first error
    /// marks its mutation once refusals of form print first.
    #[test]
    fn a_refusal_resting_on_a_repair_does_not_mark_first_2875()
    {
        let scratch = std::env::temp_dir().join(format!(
            "gandr-recovery-test-{}-resting",
            std::process::id()
        ));
        let folder = scratch.join("syntax");
        std::fs::create_dir_all(&folder).expect("the scratch folder");
        for (name, text) in [
            (
                "hold-expression.gandr",
                include_str!("../../../../corpus/ledger/syntax/hold-expression.gandr"),
            ),
            (
                "rec-block.gandr",
                include_str!("../../../../corpus/ledger/syntax/rec-block.gandr"),
            ),
        ] {
            std::fs::write(folder.join(name), text).expect("the exemplar is written");
        }
        let pbg = built_in().expect("the built-in grammar builds");
        let report = sweep(&pbg, &scratch).expect("the sweep runs");
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
        let missed = |miss: &str| Mutation::Missed(String::from(miss));
        let resting = [
            ("hold-expression.gandr", 127_usize, "{", missed("{{")),
            ("hold-expression.gandr", 131, "type", missed("typ")),
            ("hold-expression.gandr", 131, "type", Mutation::Deleted),
            ("hold-expression.gandr", 143, "=", Mutation::Deleted),
            ("hold-expression.gandr", 145, "String", Mutation::Deleted),
            ("hold-expression.gandr", 151, ";", Mutation::Deleted),
            ("rec-block.gandr", 276, "}", missed("}}")),
            ("rec-block.gandr", 280, "}", missed("}}")),
            ("rec-block.gandr", 284, "@[", missed("@")),
            ("rec-block.gandr", 284, "@[", Mutation::Deleted),
        ];
        for (exemplar, at, tile, mutation) in resting {
            assert!(
                !report.findings.iter().any(|finding| {
                    finding.exemplar.file_name() == Some(exemplar.as_ref())
                        && finding.at == at
                        && finding.tile == tile
                        && finding.mutation == mutation
                }),
                "{exemplar}:{at}: `{tile}` {mutation} is reported first at its mutation: {report}"
            );
        }
    }

    /// #2876: `rec` deleted from `def rec down` leaves a definition that
    /// cannot call itself, and `loop` missed as `loo` renames a declaration
    /// the exemplar names by the keyword. Each leaves a source with another
    /// meaning, refused only at a use no declaration answers, so it is counted
    /// well formed and not filed.
    #[test]
    fn a_mutant_leaving_only_unresolved_names_is_no_finding_2876()
    {
        let scratch = std::env::temp_dir().join(format!(
            "gandr-recovery-test-{}-unresolved",
            std::process::id()
        ));
        let folder = scratch.join("syntax");
        std::fs::create_dir_all(&folder).expect("the scratch folder");
        for (name, text) in [
            (
                "run-expression.gandr",
                include_str!("../../../../corpus/ledger/syntax/run-expression.gandr"),
            ),
            (
                "binary-expression.then.gandr",
                include_str!("../../../../corpus/ledger/syntax/binary-expression.then.gandr"),
            ),
        ] {
            std::fs::write(folder.join(name), text).expect("the exemplar is written");
        }
        let pbg = built_in().expect("the built-in grammar builds");
        let report = sweep(&pbg, &scratch).expect("the sweep runs");
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
        let unresolved = [
            ("run-expression.gandr", 157_usize, "rec", Mutation::Deleted),
            (
                "binary-expression.then.gandr",
                124,
                "loop",
                Mutation::Missed(String::from("loo")),
            ),
        ];
        for &(exemplar, at, tile, ref mutation) in &unresolved {
            assert!(
                !report.findings.iter().any(|finding| {
                    finding.exemplar.file_name() == Some(exemplar.as_ref())
                        && finding.at == at
                        && finding.tile == tile
                        && finding.mutation == *mutation
                }),
                "{exemplar}:{at}: `{tile}` {mutation} leaves only unresolved names: {report}"
            );
        }
        assert!(report.formed >= unresolved.len(), "{report}");
    }

    /// #3332: `loop` deleted leaves its `break` outside any loop, `break`
    /// deleted or missed leaves the loop endless and the statement after it
    /// unreached, and `rec` deleted leaves a descent claim outside a recursive
    /// group. Each form left is well formed and refused for what it means where
    /// it stands, so each mutant is counted well formed and not filed.
    #[test]
    fn a_deleted_licence_leaves_a_well_formed_source_3332()
    {
        let scratch = std::env::temp_dir().join(format!(
            "gandr-recovery-test-{}-licence",
            std::process::id()
        ));
        let folder = scratch.join("syntax");
        std::fs::create_dir_all(&folder).expect("the scratch folder");
        for (name, text) in [
            (
                "break-expression.gandr",
                include_str!("../../../../corpus/ledger/syntax/break-expression.gandr"),
            ),
            (
                "break-value-expression.gandr",
                include_str!("../../../../corpus/ledger/syntax/break-value-expression.gandr"),
            ),
            (
                "rec-block.gandr",
                include_str!("../../../../corpus/ledger/syntax/rec-block.gandr"),
            ),
        ] {
            std::fs::write(folder.join(name), text).expect("the exemplar is written");
        }
        let pbg = built_in().expect("the built-in grammar builds");
        let report = sweep(&pbg, &scratch).expect("the sweep runs");
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
        let licensed = [
            (
                "break-expression.gandr",
                99_usize,
                "loop",
                Mutation::Deleted,
            ),
            (
                "break-expression.gandr",
                106,
                "break",
                Mutation::Missed(String::from("brea")),
            ),
            ("break-expression.gandr", 106, "break", Mutation::Deleted),
            (
                "break-value-expression.gandr",
                119,
                "loop",
                Mutation::Deleted,
            ),
            ("rec-block.gandr", 174, "rec", Mutation::Deleted),
            ("rec-block.gandr", 302, "rec", Mutation::Deleted),
        ];
        for &(exemplar, at, tile, ref mutation) in &licensed {
            assert!(
                !report.findings.iter().any(|finding| {
                    finding.exemplar.file_name() == Some(exemplar.as_ref())
                        && finding.at == at
                        && finding.tile == tile
                        && finding.mutation == *mutation
                }),
                "{exemplar}:{at}: `{tile}` {mutation} leaves a well-formed source: {report}"
            );
        }
        assert!(report.formed >= licensed.len(), "{report}");
    }
}
