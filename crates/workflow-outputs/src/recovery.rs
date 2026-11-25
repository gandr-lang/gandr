//! The recovery record of a corpus source: one line, `W`, the count of the
//! obligations of its parse, the count of the positions of its tree and the
//! fingerprint of the tree, separated by tabs.
//!
//! The fingerprint hashes the significant nodes of the tree in preorder, as
//! the digest of the tree does, but names each mold by its rule, its label
//! and its rank among the molds of that rule with that label, not by its
//! [`MoldId`]. A change of the grammar that renumbers the molds moves the
//! digest of each tree. It moves the fingerprint only where a tree changes.

use core::fmt;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::parse;
use gandr_surface_syntax::CloseReach;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

/// Why a record could not be written.
///
/// # Specification
/// - provides: one variant for each refusal; each carries the detail of the
///   refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecordError
{
    /// The grammar names a mold that has no rule.
    Grammar
    {
        /// The refusal of the grammar.
        detail: String,
    },
    /// The source gives no tree.
    Parse
    {
        /// The refusal of the parser.
        detail: String,
    },
}

impl fmt::Display for RecordError
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
            Self::Grammar { ref detail } => {
                write!(f, "the grammar names a mold with no rule: {detail}")
            },
            Self::Parse { ref detail } => write!(f, "the source gives no tree: {detail}"),
        }
    }
}

/// A refusal is an error value, so a caller can return it.
impl core::error::Error for RecordError
{
}

/// The writer of the recovery records under one grammar: the name of each
/// mold by its rule, its label and its rank.
#[derive(Debug)]
pub struct Recorder<'grammar>
{
    /// The grammar that parses each source.
    pbg: &'grammar Pbg,
    /// The name of each mold, at the index of its [`MoldId`].
    spellings: Vec<String>,
}

impl<'grammar> Recorder<'grammar>
{
    /// The recorder of `pbg`: each mold named by its rule, its label and its
    /// rank among the molds of that rule with that label, in the order of
    /// [`Pbg::iter_molds`].
    ///
    /// # Specification
    /// - ensures: each mold of `pbg` has a name.
    ///
    /// # Errors
    /// [`RecordError::Grammar`] when `pbg` names a mold with no rule.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the records of the corpus equal the records that the
    ///   recovery sweep holds; a changed name moves a fingerprint.
    /// - witness: `recovery::tests::a_record_is_one_line_of_four_fields`
    #[inline]
    pub fn new(pbg: &'grammar Pbg) -> Result<Self, RecordError>
    {
        let mut spellings: Vec<String> = Vec::new();
        let mut ranks: Vec<(&str, &str, usize)> = Vec::new();
        for (id, def) in pbg.iter_molds() {
            let rule = pbg
                .rule_of(id)
                .map_err(|error| RecordError::Grammar {
                    detail: error.to_string(),
                })?
                .name;
            let rank = if let Some(entry) = ranks
                .iter_mut()
                .find(|&&mut (name, label, _)| name == rule && label == def.label)
            {
                entry.2 = entry.2.saturating_add(1);
                entry.2
            }
            else {
                ranks.push((rule, def.label, 0));
                0
            };
            let Ok(index) = usize::try_from(u32::from(id))
            else {
                continue;
            };
            if spellings.len() <= index {
                spellings.resize(index.saturating_add(1), String::new());
            }
            if let Some(slot) = spellings.get_mut(index) {
                *slot = format!("{rule} {} {rank}", def.label);
            }
        }
        Ok(Self { pbg, spellings })
    }

    /// The recovery record of the source `text`: `W`, the count of the
    /// obligations of its parse, the count of the positions of its tree and
    /// its [`fingerprint`](Self::fingerprint), separated by tabs, and a
    /// newline.
    ///
    /// # Specification
    /// - ensures: the record is one line that starts with `W` and a tab.
    ///
    /// # Errors
    /// [`RecordError::Parse`] when `text` gives no tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the record of a source of the corpus equals its
    ///   committed record.
    /// - witness: `recovery::tests::a_record_is_one_line_of_four_fields`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |record| record.starts_with("W\t") && record.lines().count() == 1))]
    #[inline]
    pub fn record(
        &self,
        text: &str,
    ) -> Result<String, RecordError>
    {
        let whole =
            parse(self.pbg, SourceText::from(text)).map_err(|error| RecordError::Parse {
                detail: error.to_string(),
            })?;
        let mut row = String::new();
        let _written = writeln!(
            row,
            "W\t{}\t{}\t{}",
            whole.obligations().len(),
            whole.tree().positions().count(),
            self.fingerprint(whole.tree())
        );
        Ok(row)
    }

    /// The fingerprint of `tree`: the BLAKE3 digest, in hexadecimal, of its
    /// significant nodes in preorder. Each node gives its name, a zero byte,
    /// the count of its significant children as eight bytes, little-endian,
    /// and, for a node that carries text, the length of its text as eight
    /// bytes and the text.
    ///
    /// # Specification
    /// - ensures: the fingerprint is 64 hexadecimal digits.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two trees that differ in a significant node differ in
    ///   their fingerprints, and a renumbered mold does not move one.
    /// - witness: `recovery::tests::a_record_is_one_line_of_four_fields`
    #[spec(ensures: |ret| ret.len() == 64)]
    #[inline]
    #[must_use]
    pub fn fingerprint(
        &self,
        tree: &SyntaxTree<'_>,
    ) -> String
    {
        let mut preimage: Vec<u8> = Vec::new();
        let mut pending = vec![tree.root()];
        while let Some(at) = pending.pop() {
            let Some(node) = label_of(tree, at)
            else {
                continue;
            };
            let below: Vec<NodeIndex> = tree
                .children(at)
                .filter(|&child| {
                    label_of(tree, child).is_some_and(|child| bool::from(child.significance()))
                })
                .collect();
            let name = match node {
                NodeLabel::Tile(mold) => format!("tile {}", self.spelled(mold)),
                NodeLabel::Meld(mold) => format!("meld {}", self.spelled(mold)),
                // A close minted at its one place is named as it was before a
                // close could reach back, so the fingerprint of its tree
                // stays.
                NodeLabel::GhostClose { sort, class, reach } if reach == CloseReach::NONE => {
                    format!("GhostClose {{ sort: {sort:?}, class: {class:?} }}")
                },
                other @ (NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc) => format!("{other:?}"),
            };
            preimage.extend_from_slice(name.as_bytes());
            preimage.push(0);
            preimage
                .extend_from_slice(&u64::try_from(below.len()).unwrap_or(u64::MAX).to_le_bytes());
            if bool::from(node.carries_text()) {
                let written = tree.fragment(at).map_or("", <&str>::from);
                preimage.extend_from_slice(
                    &u64::try_from(written.len())
                        .unwrap_or(u64::MAX)
                        .to_le_bytes(),
                );
                preimage.extend_from_slice(written.as_bytes());
            }
            pending.extend(below.into_iter().rev());
        }
        blake3::hash(&preimage).to_hex().to_string()
    }

    /// The name of `mold`, or the empty text when the grammar has no such
    /// mold.
    ///
    /// # Specification
    /// trivial.
    fn spelled(
        &self,
        mold: MoldId,
    ) -> &str
    {
        usize::try_from(u32::from(mold))
            .ok()
            .and_then(|index| self.spellings.get(index))
            .map_or("", String::as_str)
    }
}

/// The label of the node at `at`, when the tree holds it.
///
/// # Specification
/// trivial.
fn label_of(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<NodeLabel>
{
    tree.node(at).map(Node::label)
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;

    use super::Recorder;

    /// A record is one line of four fields, and an edit of a significant
    /// token moves its fingerprint.
    #[test]
    fn a_record_is_one_line_of_four_fields()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let recorder = Recorder::new(&pbg).expect("each mold has a rule");
        let record = recorder
            .record("def one : Nat = 1\n")
            .expect("the source gives a tree");
        let fields: Vec<&str> = record.trim_end().split('\t').collect();
        assert_eq!(fields.first(), Some(&"W"));
        assert_eq!(fields.len(), 4);
        assert_eq!(fields.get(3).map(|field| field.len()), Some(64));
        let other = recorder
            .record("def two : Nat = 2\n")
            .expect("the source gives a tree");
        assert_ne!(record, other);
        assert_eq!(
            record,
            recorder
                .record("def one : Nat = 1\n")
                .expect("the source gives a tree")
        );
    }
}
