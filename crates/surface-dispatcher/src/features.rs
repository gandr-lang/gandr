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
use crate::reader::Reader;
use crate::root;
use crate::walk::Reached;
use crate::walk::Traversal;
use crate::walk::walk_step;

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
    /// Writes the attribute as a source writes it: `@![features("a")]` for
    /// one feature, `@![features(("a", "b"))]` for more, and `tier zero` for
    /// a source that uses none and so writes no attribute.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self.0.as_slice() {
            [] => f.write_str("tier zero"),
            [one] => write!(f, "@![features(\"{one}\")]"),
            [first, ref rest @ ..] => {
                write!(f, "@![features((\"{first}\"")?;
                for feature in rest {
                    write!(f, ", \"{feature}\"")?;
                }
                f.write_str("))]")
            },
        }
    }
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
    },
    /// A path whose features the census could not read.
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
    /// What each source is read through.
    reader: Reader,
    /// The last source reached, laid out after the prelude and its imports:
    /// the text that the fault of a step borrows.
    laid: String,
}

impl FeatureCensus
{
    /// A census of `paths`, in the order given, with nothing read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(paths: Vec<PathBuf>) -> Self
    {
        Self {
            grammar: built_in(),
            traversal: Traversal::new(paths),
            reader: Reader::new(),
            laid: String::new(),
        }
    }

    /// The next source or fault of the census.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each path given is reached in order, as [`crate::Walk`]
    ///   reaches it. Each source is read, laid out after the prelude and the
    ///   sources that it imports, parsed and lowered. Its step holds the
    ///   declaration of the features that the source itself uses. A path that
    ///   cannot be listed or read, that names no source, that fails to parse
    ///   or lower, or whose source the lowering refuses whole is a
    ///   [`FeatureStep::Fault`]. Exhaustion is stable.
    /// - provides: the pass that `gandr features` renders.
    /// - fails: never; each fault is a step, and the census continues past
    ///   it.
    /// - panics: none.
    /// - intension: holds one laid-out source at a time.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of the first twin, a source that uses one
    ///   feature and a missing path give the exact line of each one and the
    ///   exit.
    /// - witness: `gandr-surface-driver::tests::cli::features_prints_the_declaration_of_each_source`
    #[inline]
    #[spec(
        captures: [built = self.grammar.is_ok()],
        ensures: |ref ret| !(built && matches!(*ret,
            Maybe::Present(FeatureStep::Fault { fault: CensusFault::Grammar(_), .. }))),
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
                match read_features(&self.reader, path, self.grammar.as_ref(), &mut self.laid) {
                    Ok(declaration) => {
                        return Maybe::Present(FeatureStep::Source { path, declaration });
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
/// `grammar`, lower it, and read the features that it uses.
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
) -> Result<Declaration, CensusFault<'census>>
{
    let read = reader.read(path).map_err(CensusFault::Unreadable)?;
    let grammar = grammar.map_err(CensusFault::Grammar)?;
    let unit = component::lay_out(grammar, path, root::classify(path), read.text());
    *laid = unit.text;
    let laid: &'census str = laid;
    let features = unit_source_features(
        grammar,
        SourceText::from(laid),
        &unit.unit,
        &mut LoweringCount::default(),
    )
    .map_err(CensusFault::Composed)?;
    match features {
        SourceFeatures::Used(used) => Ok(Declaration(used)),
        SourceFeatures::Refused(refusal) => Err(CensusFault::Refused(refusal)),
    }
}

#[cfg(test)]
mod tests
{
    use super::Declaration;

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
}
