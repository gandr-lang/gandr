//! The features verb: the language features that each source uses, as the
//! declaration that the source writes at its head.
//!
//! # The declaration of a source
//!
//! A source declares its language features with the attribute `features` at
//! its head. The lowering knows the feature of each form, of each attribute
//! and of each builtin row that a source writes
//! ([`gandr_surface_lowering::gate`]). [`FeatureCensus`] asks it for the
//! features of each source and answers them as a [`Declaration`]: the
//! attribute to write, which states each feature that the source uses and no
//! other.
//!
//! # The walk's paths, the lowering's features
//!
//! A census reaches its sources as the walk does, and it lays each one out
//! after the prelude and the sources that it imports, as `check` lowers it.
//! The features of a step are those of the source itself, and not those of
//! the prelude or of an import. Nothing is checked. A census of a tree costs
//! one parse and one lowering for each source.
//!
//! # The write
//!
//! Under [`Rewrite::InPlace`] the census writes the declaration into each
//! source whose head states a different one ([`rewritten`]).
//!
//! | The head of the source | The declaration | The write |
//! | ---------------------- | --------------- | --------- |
//! | has the attribute | one feature or more | the attribute is replaced where it stands |
//! | has the attribute alone in its block | no feature | the block and its line are removed |
//! | has the attribute beside others | no feature | the attribute and its comma are removed |
//! | has no attribute | one feature or more | a block of its own is written before the first line that is not a `//!` line of the head |
//! | has no attribute | no feature | nothing |
//!
//! The block stands before a `///` comment, and not after it. A `///` comment
//! documents the declaration that follows it, and an inner block between the
//! two parts them.

use core::ops::Range;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::cells::CensusFault;
use crate::component;
use crate::compose::LoweringCount;
use crate::compose::SourceFeatures;
use crate::compose::unit_source_features;
use crate::format::Rewrite;
use crate::reader::Reader;
use crate::root;
use crate::walk::Reached;
use crate::walk::Traversal;
use crate::walk::walk_step;

/// The line of the head of a source that documents the source.
const INNER_DOC_LINE: &str = "//!";

/// The tile that opens an inner attribute block.
const INNER_OPEN: &str = "@![";

/// The declaration of the language features of one source: the id of each
/// feature that the source uses.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the ids are in their byte order, each one time.
/// - provides: the text of the attribute that the source writes at its head.
/// - fails: never.
/// - panics: none.
/// - executable: none — the constructor is private to the census, which takes
///   the ids from an ordered map.
///
/// # Adequacy
/// - hypothesis: L3 — no id, one id and two ids separate the three spellings.
/// - witness: `features::tests::a_declaration_is_spelled_as_its_source_writes_it`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Declaration(Vec<&'static str>);

impl Declaration
{
    /// The id of each feature that the source uses, in byte order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn features(&self) -> &[&'static str]
    {
        &self.0
    }
}

impl core::fmt::Display for Declaration
{
    /// Writes the block as a source writes it: `@![features("a")]` for one
    /// feature, `@![features(("a", "b"))]` for more, and `tier zero` for a
    /// source that uses none and so writes no attribute.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        if self.0.is_empty() {
            f.write_str("tier zero")
        }
        else {
            write!(f, "{INNER_OPEN}{}]", Entry(&self.0))
        }
    }
}

/// The attribute `features` of a declaration, without its block:
/// `features("a")` for one feature and `features(("a", "b"))` for more.
struct Entry<'declaration>(&'declaration [&'static str]);

impl core::fmt::Display for Entry<'_>
{
    /// Writes the attribute as a source writes it inside a block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self.0 {
            [] => f.write_str("features"),
            [one] => write!(f, "features(\"{one}\")"),
            [first, ref rest @ ..] => {
                write!(f, "features((\"{first}\"")?;
                for feature in rest {
                    write!(f, ", \"{feature}\"")?;
                }
                f.write_str("))")
            },
        }
    }
}

/// How the head of a source stands against the declaration of its step.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Head
{
    /// The head states the declaration.
    Stands,
    /// The head states a different declaration, and the census wrote nothing.
    Differs,
    /// The head stated a different declaration, and the census wrote the
    /// declaration of the step into the source.
    Written,
}

/// One step of a census of features.
#[derive(Debug)]
pub enum FeatureStep<'census>
{
    /// A source and the declaration of the features that it uses.
    Source
    {
        /// The path of the source, as the census reached it.
        path: &'census Path,
        /// The declaration.
        declaration: Declaration,
        /// How the head of the source stands against the declaration.
        head: Head,
    },
    /// A path whose features the census could not read, or whose source it
    /// could not write.
    Fault
    {
        /// The path, as the census reached it.
        path: &'census Path,
        /// Why.
        fault: CensusFault<'census>,
    },
}

/// The features verb over the paths that it was given, reading its sources in
/// order.
#[derive(Debug)]
pub struct FeatureCensus
{
    /// The grammar that each source is parsed under, built one time for the
    /// census.
    grammar: Result<Pbg, PbgError>,
    /// Where the census is among the paths that it was given.
    traversal: Traversal,
    /// What each source is read and written through.
    reader: Reader,
    /// The last source reached, laid out after the prelude and its imports:
    /// the text that the fault of a step borrows.
    laid: String,
    /// What the census does with a source whose head states a different
    /// declaration.
    rewrite: Rewrite,
}

impl FeatureCensus
{
    /// A census of `paths`, in the order given, with nothing read. Under
    /// [`Rewrite::InPlace`] it writes the declaration into each source whose
    /// head states a different one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        paths: Vec<PathBuf>,
        rewrite: Rewrite,
    ) -> Self
    {
        Self {
            grammar: built_in(),
            traversal: Traversal::new(paths),
            reader: Reader::new(),
            laid: String::new(),
            rewrite,
        }
    }

    /// The next source or fault of the census.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each path given is reached in order, as [`crate::Walk`]
    ///   reaches it. Each source is read, laid out after the prelude and the
    ///   sources that it imports, parsed and lowered. Its step holds the
    ///   declaration of the features that the source itself uses, and how its
    ///   head stands against it. Under [`Rewrite::InPlace`] a source whose head
    ///   states a different declaration is written back with the declaration of
    ///   its step, as [`rewritten`] writes it, and no other source is written.
    ///   A path that cannot be listed or read, that names no source, that fails
    ///   to parse or lower, whose source the lowering refuses whole, or whose
    ///   source cannot be written is a [`FeatureStep::Fault`]. Exhaustion is
    ///   stable.
    /// - provides: the pass that `gandr features` renders.
    /// - fails: never; each fault is a step, and the census continues past it.
    /// - panics: none.
    /// - intension: holds one laid-out source at a time.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of the first twin, a source that uses one
    ///   feature and a missing path give the exact line of each one and the
    ///   exit; a source with no attribute, one with a stale attribute, one with
    ///   the attribute beside a different one and one with a `//!` line are
    ///   each written to their exact text, and a second run writes none.
    /// - witness: `gandr-surface-driver::tests::cli::features_prints_the_declaration_of_each_source`
    /// - witness: `gandr-surface-driver::tests::cli::features_writes_the_declaration_of_each_source`
    #[inline]
    #[spec(
        captures: [built = self.grammar.is_ok(), rewrite = self.rewrite],
        ensures: |ref ret| match *ret {
            Maybe::Present(FeatureStep::Fault { fault: CensusFault::Grammar(_), .. }) => !built,
            Maybe::Present(FeatureStep::Source { head: Head::Written, .. }) => rewrite == Rewrite::InPlace,
            Maybe::Present(_) | Maybe::Absent(_) => true,
        },
    )]
    pub fn step(&mut self) -> Maybe<FeatureStep<'_>, walk_step::Absent>
    {
        let reached = match self.traversal.reach() {
            Maybe::Absent(absent) => return Maybe::Absent(absent),
            Maybe::Present(reached) => reached,
        };
        let path = self.traversal.path();
        let fault = match reached {
            Reached::Source => {
                let read = read_features(
                    &self.reader,
                    path,
                    self.grammar.as_ref(),
                    &mut self.laid,
                    self.rewrite,
                );
                match read {
                    Ok((declaration, head)) => {
                        return Maybe::Present(FeatureStep::Source {
                            path,
                            declaration,
                            head,
                        });
                    },
                    Err(fault) => fault,
                }
            },
            Reached::Unreadable(error) => CensusFault::Unreadable(error),
            Reached::NoSource => CensusFault::NoSource,
        };
        Maybe::Present(FeatureStep::Fault { path, fault })
    }
}

/// Read the source at `path` through `reader`, lay it out into `laid` under
/// `grammar`, lower it, and read the features that it uses. Under
/// [`Rewrite::InPlace`], write the declaration into a source whose head
/// states a different one.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`CensusFault`] that stopped the source.
fn read_features<'census>(
    reader: &Reader,
    path: &Path,
    grammar: Result<&'census Pbg, &'census PbgError>,
    laid: &'census mut String,
    rewrite: Rewrite,
) -> Result<(Declaration, Head), CensusFault<'census>>
{
    let read = reader.read(path).map_err(CensusFault::Unreadable)?;
    let grammar = grammar.map_err(CensusFault::Grammar)?;
    let unit = component::lay_out(grammar, path, root::classify(path), read.text());
    let base = usize::from(unit.base);
    *laid = unit.text;
    let laid: &'census str = laid;
    let features = unit_source_features(
        grammar,
        SourceText::from(laid),
        &unit.unit,
        &mut LoweringCount::default(),
    )
    .map_err(CensusFault::Composed)?;
    let (used, site) = match features {
        SourceFeatures::Used { used, site } => (used, site),
        SourceFeatures::Refused(refusal) => return Err(CensusFault::Refused(refusal)),
    };
    let declaration = Declaration(used);
    let own = laid.get(base ..).unwrap_or_default();
    // The lowering measures the attribute in the text of the unit, and the
    // write is in the text of the source.
    let site = site.map(|(entry, block)| {
        (
            entry.start.saturating_sub(base) .. entry.end.saturating_sub(base),
            block.start.saturating_sub(base) .. block.end.saturating_sub(base),
        )
    });
    let head = match rewritten(own, site.as_ref(), &declaration) {
        None => Head::Stands,
        Some(_) if rewrite == Rewrite::Check => Head::Differs,
        Some(text) => {
            // A head that the lowering does not file takes no declaration:
            // a second run would write the block again.
            if !reads_back(grammar, path, &text, &declaration) {
                return Err(CensusFault::Unfiled);
            }
            reader
                .write(path, SourceText::from(text.as_str()))
                .map_err(CensusFault::Unwritable)?;
            Head::Written
        },
    };
    Ok((declaration, head))
}

/// Whether the lowering reads `declaration` back from the head of `text`, the
/// text of the source at `path` with the declaration written into it.
///
/// # Specification
/// - requires: `text` is [`rewritten`] of the source at `path`.
/// - ensures: affirmative exactly when `text` lowers, uses the features of
///   `declaration`, and has the attribute `features` at its head when
///   `declaration` has a feature and no such attribute when it has none.
/// - provides: the proof that a write is one that a second run leaves.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one source, with the declaration that it uses at its head
///   and with no declaration, and a source of tier zero with no attribute; the
///   first and the last are read back.
/// - witness: `features::tests::a_write_is_one_that_the_lowering_reads_back`
///
/// # Cost
/// - time: one parse and one lowering, for a source that the census writes
fn reads_back(
    grammar: &Pbg,
    path: &Path,
    text: &str,
    declaration: &Declaration,
) -> bool
{
    let unit = component::lay_out(grammar, path, root::classify(path), SourceText::from(text));
    let read = unit_source_features(
        grammar,
        SourceText::from(unit.text.as_str()),
        &unit.unit,
        &mut LoweringCount::default(),
    );
    matches!(
        read,
        Ok(SourceFeatures::Used { ref used, ref site })
            if used.as_slice() == declaration.features()
                && site.is_some() != declaration.features().is_empty()
    )
}

/// The text of a source with `declaration` at its head, or nothing when the
/// head of `text` states it.
///
/// # Specification
/// - requires: `site` is the attribute `features` at the head of `text`, when
///   it has one: the bytes of the attribute, and the bytes of the inner block
///   that holds it, which opens with `@![` and closes with `]`.
/// - ensures: the rows of the table of the module documentation. A written
///   block of its own is followed by one blank line. A removed block takes the
///   rest of its line and one blank line after it.
/// - provides: the write of `gandr features --write`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the answer is a text; the witness holds each row.
///
/// # Adequacy
/// - hypothesis: L3 — each row of the table, a head with a `//!` run with and
///   without a blank line after it, and an attribute before and after a
///   different one in its block, each as an exact text.
/// - witness: `features::tests::a_head_is_rewritten_by_each_row_of_the_table`
///
/// # Cost
/// - allocation: the text, one time for a source whose head differs
fn rewritten(
    text: &str,
    site: Option<&(Range<usize>, Range<usize>)>,
    declaration: &Declaration,
) -> Option<String>
{
    let features = declaration.features();
    let (cut, written) = match (site, features.is_empty()) {
        (None, true) => return None,
        (None, false) => {
            let at = after_inner_docs(text);
            (at .. at, format!("{declaration}\n\n"))
        },
        (Some(&(ref entry, _)), false) => (entry.clone(), Entry(features).to_string()),
        (Some(&(ref entry, ref block)), true) => (removal(text, entry, block), String::new()),
    };
    let (before, after) = (text.get(.. cut.start)?, text.get(cut.end ..)?);
    if text.get(cut) == Some(written.as_str()) {
        return None;
    }
    let mut rewritten = String::with_capacity(
        before
            .len()
            .saturating_add(written.len())
            .saturating_add(after.len()),
    );
    rewritten.push_str(before);
    rewritten.push_str(&written);
    rewritten.push_str(after);
    Some(rewritten)
}

/// Where a block of its own is written in `text`: before the first line that
/// is not a `//!` line of the head, blank lines after such a line aside.
///
/// # Specification
/// trivial.
fn after_inner_docs(text: &str) -> usize
{
    let mut at = 0_usize;
    let mut documented = 0_usize;
    for line in text.split_inclusive('\n') {
        let written = line.trim();
        if written.starts_with(INNER_DOC_LINE) {
            at = at.saturating_add(line.len());
            documented = at;
        }
        else if written.is_empty() && documented > 0_usize {
            at = at.saturating_add(line.len());
        }
        else {
            break;
        }
    }
    if documented == 0_usize { 0_usize } else { at }
}

/// The bytes of `text` that the removal of the attribute at `entry` takes:
/// its block with the rest of the line and one blank line, when the attribute
/// is alone in `block`; else the attribute with the comma after it, or with
/// the comma before it when none follows.
///
/// # Specification
/// trivial.
fn removal(
    text: &str,
    entry: &Range<usize>,
    block: &Range<usize>,
) -> Range<usize>
{
    let opened = block.start.saturating_add(INNER_OPEN.len());
    let closed = block.end.saturating_sub(1_usize);
    let before = text.get(opened .. entry.start).unwrap_or_default();
    let after = text.get(entry.end .. closed).unwrap_or_default();
    if before.trim().is_empty() && after.trim().is_empty() {
        let rest = text.get(block.end ..).unwrap_or_default();
        let line = rest
            .find('\n')
            .map_or(rest.len(), |end| end.saturating_add(1));
        let own_line = text
            .get(.. block.start)
            .is_some_and(|head| head.is_empty() || head.ends_with('\n'))
            && rest.get(.. line).is_some_and(|tail| tail.trim().is_empty());
        if !own_line {
            return block.clone();
        }
        let blank = rest
            .get(line ..)
            .and_then(|next| next.split_inclusive('\n').next())
            .filter(|next| next.trim().is_empty())
            .map_or(0_usize, str::len);
        return block.start .. block.end.saturating_add(line).saturating_add(blank);
    }
    let following = after.len().saturating_sub(after.trim_start().len());
    if after.trim_start().starts_with(',') {
        let comma = entry.end.saturating_add(following).saturating_add(1_usize);
        let spaces = text.get(comma .. closed).map_or(0_usize, |tail| {
            tail.len().saturating_sub(tail.trim_start().len())
        });
        return entry.start .. comma.saturating_add(spaces);
    }
    let kept = before.trim_end();
    let comma = kept
        .strip_suffix(',')
        .map_or(entry.start, |head| opened.saturating_add(head.len()));
    comma .. entry.end
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_surface_grammar::built_in;

    use super::Declaration;
    use super::reads_back;
    use super::rewritten;

    #[test]
    fn a_write_is_one_that_the_lowering_reads_back()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let path = Path::new("scratch/one.gandr");
        let used = Declaration(Vec::from(["deprecation"]));
        let body = "@[deprecated] def one() -> Integer = 1;\n";

        assert!(
            reads_back(
                &grammar,
                path,
                &format!("@![features(\"deprecation\")]\n\n{body}"),
                &used
            ),
            "the head states the declaration"
        );
        assert!(
            !reads_back(&grammar, path, body, &used),
            "the head states nothing"
        );
        assert!(
            reads_back(
                &grammar,
                path,
                "def one() -> Integer = 1;\n",
                &Declaration(Vec::new())
            ),
            "a source of tier zero has no attribute"
        );
    }

    #[test]
    fn a_declaration_is_spelled_as_its_source_writes_it()
    {
        assert_eq!(Declaration(Vec::new()).to_string(), "tier zero");
        assert_eq!(
            Declaration(Vec::from(["modules"])).to_string(),
            "@![features(\"modules\")]"
        );
        assert_eq!(
            Declaration(Vec::from(["deprecation", "modules"])).to_string(),
            "@![features((\"deprecation\", \"modules\"))]"
        );
    }

    /// The site of the attribute `features` in `text`: the attribute, and the
    /// inner block that holds it.
    fn site(text: &str) -> (core::ops::Range<usize>, core::ops::Range<usize>)
    {
        let block = text.find("@![").expect("the text has an inner block");
        let closed = text.find(']').expect("the block closes");
        let entry = text.find("features").expect("the block has the attribute");
        let payload = text
            .get(entry ..)
            .and_then(|rest| rest.find(')'))
            .map(|at| entry.saturating_add(at).saturating_add(1))
            .expect("the attribute has a payload");
        let nested = text
            .get(payload ..)
            .is_some_and(|rest| rest.starts_with(')'));
        let ended = payload.saturating_add(usize::from(nested));
        (entry .. ended, block .. closed.saturating_add(1))
    }

    #[test]
    fn a_head_is_rewritten_by_each_row_of_the_table()
    {
        let none = Declaration(Vec::new());
        let one = Declaration(Vec::from(["modules"]));
        let two = Declaration(Vec::from(["deprecation", "modules"]));
        let body = "/// The value one.\ndef one() -> Integer = 1;\n";

        assert_eq!(
            rewritten(body, None, &none),
            None,
            "no attribute and no feature"
        );
        assert_eq!(
            rewritten(body, None, &one),
            Some(format!("@![features(\"modules\")]\n\n{body}")),
            "a block of its own stands before a `///` comment"
        );
        let documented = format!("//! A source.\n\n{body}");
        assert_eq!(
            rewritten(&documented, None, &one),
            Some(format!(
                "//! A source.\n\n@![features(\"modules\")]\n\n{body}"
            )),
            "and after the `//!` lines of the head and their blank line"
        );
        let close = format!("//! A source.\n{body}");
        assert_eq!(
            rewritten(&close, None, &one),
            Some(format!(
                "//! A source.\n@![features(\"modules\")]\n\n{body}"
            )),
            "with no blank line to pass"
        );

        let stated = format!("@![features(\"modules\")]\n\n{body}");
        assert_eq!(
            rewritten(&stated, Some(&site(&stated)), &one),
            None,
            "a head that states the declaration stands"
        );
        assert_eq!(
            rewritten(&stated, Some(&site(&stated)), &two),
            Some(format!(
                "@![features((\"deprecation\", \"modules\"))]\n\n{body}"
            )),
            "the attribute is replaced where it stands"
        );
        assert_eq!(
            rewritten(&stated, Some(&site(&stated)), &none),
            Some(body.to_owned()),
            "a block that holds the attribute alone goes with its line and one blank line"
        );

        let first = format!("@![features(\"modules\"), doc(\"A source.\")]\n\n{body}");
        assert_eq!(
            rewritten(&first, Some(&site(&first)), &none),
            Some(format!("@![doc(\"A source.\")]\n\n{body}")),
            "an attribute before a different one goes with the comma after it"
        );
        let last = format!("@![doc(\"A source.\"), features(\"modules\")]\n\n{body}");
        assert_eq!(
            rewritten(&last, Some(&site(&last)), &none),
            Some(format!("@![doc(\"A source.\")]\n\n{body}")),
            "an attribute after a different one goes with the comma before it"
        );
        assert_eq!(
            rewritten(&last, Some(&site(&last)), &two),
            Some(format!(
                "@![doc(\"A source.\"), features((\"deprecation\", \"modules\"))]\n\n{body}"
            )),
            "and it is replaced beside the other one"
        );
    }
}
