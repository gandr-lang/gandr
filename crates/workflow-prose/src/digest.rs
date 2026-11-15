//! The digest of a passage: the BLAKE3 digest of its joined text.
//!
//! The reader joins a paragraph's lines by single spaces before the digest
//! reads them. So the digest names a paragraph across revisions, files and
//! hosts: a paragraph that moves or is re-wrapped keeps its name, and a
//! paragraph that a change rewrites takes a new one.

use core::fmt;

use crate::passage::Text;

/// The digest of one passage's text.
///
/// # Specification
/// - provides: the name the parse cache keeps a parse by, and the name the
///   base's set of held paragraphs holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Digest([u8; 32]);

impl Digest
{
    /// The digest of `text`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two equal texts share a digest and a changed word
    ///   gives another; a digest of anything but the text breaks either.
    /// - witness: `digest::tests::a_text_names_itself_and_a_changed_word_renames_it`
    #[inline]
    #[must_use]
    pub fn of(text: Text<'_>) -> Self
    {
        Self(*blake3::hash(text.0.as_bytes()).as_bytes())
    }

    /// The digest that `name` writes as 64 hexadecimal digits, as the cache
    /// names an entry's file; none for a name of another shape.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a digest's own name reads back as the digest, and a
    ///   partial file's name reads as none.
    /// - witness: `digest::tests::a_text_names_itself_and_a_changed_word_renames_it`
    #[inline]
    #[must_use]
    pub(crate) fn named(name: Text<'_>) -> Option<Self>
    {
        blake3::Hash::from_hex(name.0)
            .ok()
            .map(|hash| Self(*hash.as_bytes()))
    }
}

impl fmt::Display for Digest
{
    /// The digest as 64 lowercase hexadecimal digits.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cache names each entry's file by this text, so a
    ///   shorter or a cased rendering changes the asserted name.
    /// - witness: `digest::tests::a_text_names_itself_and_a_changed_word_renames_it`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
    }
}

#[cfg(test)]
mod tests
{
    use super::Digest;
    use crate::passage::Text;

    #[test]
    fn a_text_names_itself_and_a_changed_word_renames_it()
    {
        let held = Digest::of(Text("The check reads what a change wrote."));
        assert_eq!(
            held,
            Digest::of(Text("The check reads what a change wrote."))
        );
        assert_ne!(
            held,
            Digest::of(Text("The check reads what a change writes."))
        );
        let named = held.to_string();
        assert_eq!(named.len(), 64);
        assert!(
            named
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a' ..= b'f').contains(&byte))
        );
        assert_eq!(
            named,
            blake3::hash(b"The check reads what a change wrote.")
                .to_hex()
                .as_str()
        );
        assert_eq!(Digest::named(Text(&named)), Some(held));
        assert_eq!(Digest::named(Text(&format!("{named}.part7"))), None);
    }
}
