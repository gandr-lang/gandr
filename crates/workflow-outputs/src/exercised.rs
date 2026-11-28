//! The molds of the grammar that a corpus source exercises, and the molds
//! that no source of a tree exercises.
//!
//! The value of a source is the number of each mold that a tile of its tree
//! has, one on each line. The number of a mold holds only under one grammar,
//! and the key of the value holds the tool, so a value names its molds under
//! the grammar of its tool. The molds that no source exercises are written
//! with their rule, their token and their two contexts, and with no number.
//! A change of the grammar thus moves no line of a mold that it keeps.

use alloc::collections::BTreeSet;
use core::fmt;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RCtxStep;
use gandr_surface_grammar::StepSym;
use gandr_surface_parser::parse;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_theory_graphs::Dir;

/// Why the molds of a source or of a tree could not be written.
///
/// # Specification
/// - provides: one variant for each refusal; each carries its detail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExercisedError
{
    /// The source gives no tree.
    Parse
    {
        /// The refusal of the parser.
        detail: String,
    },
    /// The grammar refuses a lookup of a mold, or a value names no mold.
    Grammar
    {
        /// The refusal of the grammar, or the line of the value.
        detail: String,
    },
}

impl fmt::Display for ExercisedError
{
    /// Writes one line that names the refusal and its detail.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Parse { ref detail } => write!(f, "the source gives no tree: {detail}"),
            Self::Grammar { ref detail } => write!(f, "the grammar names no mold: {detail}"),
        }
    }
}

/// A refusal is an error value, so a caller can return it.
impl core::error::Error for ExercisedError
{
}

/// The writer of the exercised molds under one grammar.
#[derive(Clone, Copy, Debug)]
pub struct Exercised<'grammar>
{
    /// The grammar that parses each source.
    pbg: &'grammar Pbg,
}

impl<'grammar> Exercised<'grammar>
{
    /// The writer of the exercised molds of `pbg`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(pbg: &'grammar Pbg) -> Self
    {
        Self { pbg }
    }

    /// The numbers of the molds that a tile of the tree of `text` has, one on
    /// each line, ascending, each one time.
    ///
    /// # Specification
    /// - ensures: the numbers ascend, and no number is twice.
    ///
    /// # Errors
    /// [`ExercisedError::Parse`] when `text` gives no tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition exercises some molds, and the molds of
    ///   the grammar that it does not exercise are the rest.
    /// - witness: `exercised::tests::the_unexercised_molds_are_the_rest_of_the_grammar`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |lines| lines.lines().map(|line| line.parse::<u32>().unwrap_or(u32::MAX)).is_sorted_by(|left, right| left < right)))]
    #[inline]
    pub fn value(
        &self,
        text: &str,
    ) -> Result<String, ExercisedError>
    {
        let parsed =
            parse(self.pbg, SourceText::from(text)).map_err(|error| ExercisedError::Parse {
                detail: error.to_string(),
            })?;
        let tree = parsed.tree();
        let molds: BTreeSet<u32> = tree
            .positions()
            .filter_map(|position| tree.node(position).map(Node::label))
            .filter_map(|label| match label {
                NodeLabel::Tile(mold) => Some(u32::from(mold)),
                NodeLabel::Wald
                | NodeLabel::Meld(_)
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc => None,
            })
            .collect();
        let mut out = String::new();
        for mold in molds {
            let _written = writeln!(out, "{mold}");
        }
        Ok(out)
    }

    /// The molds of the grammar that no value of `values` names: for each
    /// one, its rule, its token and the symbols on each side of it, in the
    /// order of the numbers of the molds.
    ///
    /// # Specification
    /// - ensures: one line for each mold that no value names.
    ///
    /// # Errors
    /// [`ExercisedError::Grammar`] when a line of a value is not a number, or
    /// the grammar refuses a lookup.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — with no value each mold of the grammar is a line;
    ///   with the value of a definition, its molds are not.
    /// - witness: `exercised::tests::the_unexercised_molds_are_the_rest_of_the_grammar`
    #[inline]
    pub fn unexercised<'value, Values>(
        &self,
        values: Values,
    ) -> Result<String, ExercisedError>
    where
        Values: IntoIterator<Item = &'value [u8]>,
    {
        let mut exercised: BTreeSet<u32> = BTreeSet::new();
        for value in values {
            for line in String::from_utf8_lossy(value).lines() {
                let mold = line
                    .parse::<u32>()
                    .map_err(|error| ExercisedError::Grammar {
                        detail: format!("the line `{line}` of a value is not a number: {error}"),
                    })?;
                exercised.insert(mold);
            }
        }
        let grammar = |error: gandr_surface_grammar::PbgError| ExercisedError::Grammar {
            detail: error.to_string(),
        };
        let mut out = String::new();
        for (id, def) in self.pbg.iter_molds() {
            if exercised.contains(&u32::from(id)) {
                continue;
            }
            let kind = self.pbg.named_kind(id).map_err(grammar)?;
            let left = self.pbg.step(def.rctx, Dir::Left).map_err(grammar)?;
            let right = self.pbg.step(def.rctx, Dir::Right).map_err(grammar)?;
            let _written = writeln!(
                out,
                "{} {} L[{}] R[{}]",
                kind.0,
                def.label,
                side(left),
                side(right)
            );
        }
        Ok(out)
    }

    /// How many molds the grammar has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn molds(&self) -> usize
    {
        self.pbg.iter_molds().count()
    }
}

/// The symbols that one side of a context can step across, each one time,
/// tiles by their label and holes by their sort in angle brackets.
///
/// # Specification
/// trivial.
fn side(steps: &[RCtxStep]) -> String
{
    let crossed: BTreeSet<String> = steps
        .iter()
        .map(|step| match step.crossed {
            StepSym::Tile(label) => label.to_owned(),
            StepSym::Sort(sort) => format!("<{}>", sort.name().0),
        })
        .collect();
    crossed.into_iter().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;

    use super::Exercised;

    /// With no value each mold of the grammar is unexercised. A definition
    /// exercises some molds, and the unexercised molds are the rest.
    #[test]
    fn the_unexercised_molds_are_the_rest_of_the_grammar()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let exercised = Exercised::new(&pbg);
        let all = exercised
            .unexercised(core::iter::empty())
            .expect("the grammar names each mold");
        assert_eq!(
            all.lines().count(),
            exercised.molds(),
            "with no value each mold is a line"
        );
        let value = exercised
            .value(include_str!("compute/fixtures/a-definition-of-one.gandr"))
            .expect("the source gives a tree");
        let named = value.lines().count();
        assert!(named > 0, "a definition exercises a mold");
        let rest = exercised
            .unexercised([value.as_bytes()])
            .expect("the grammar names each mold");
        assert_eq!(
            rest.lines().count(),
            exercised.molds() - named,
            "the molds of the definition are not lines: {value}"
        );
        assert!(
            exercised.unexercised([b"one\n".as_slice()]).is_err(),
            "a line that is not a number is refused"
        );
    }
}
