//! The protocol's semantic token stream: its legend, five integers per token,
//! the edit that turns one stream into another, and the id that names a full
//! answer.
//!
//! A client that asked for the tokens once can ask for a delta later. The
//! server names each full answer by the BLAKE3 digest of its integers. A delta
//! that names the last stream answers one edit over the tokens between the
//! ends that the two streams share.

use alloc::vec::Vec;

use anodized::spec;
use serde::Deserialize;
use serde::Serialize;

/// The advertised token types, in the order a token's type integer indexes:
/// the standard types, then `unresolvedReference`.
pub const TOKEN_TYPES: [&str; 15] = [
    "keyword",
    "operator",
    "function",
    "variable",
    "parameter",
    "property",
    "enumMember",
    "type",
    "typeParameter",
    "number",
    "string",
    "comment",
    "macro",
    "label",
    "unresolvedReference",
];

/// The advertised token modifiers, in the order a token's modifier bits
/// index.
pub const TOKEN_MODIFIERS: [&str; 4] = ["declaration", "defaultLibrary", "value", "computation"];

/// The protocol's token stream: five integers per token.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct TokenStream(Vec<u32>);

impl From<Vec<u32>> for TokenStream
{
    /// Read the integers as a stream.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(integers: Vec<u32>) -> Self
    {
        Self(integers)
    }
}

impl AsRef<[u32]> for TokenStream
{
    /// The stream's integers.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stream of five integers, read back whole, differs
    ///   from an empty stream and from any stream of one integer.
    /// - witness: `gandr-surface-lsp::tokens::tests::a_one_line_keyword_encodes_as_five_integers`
    #[inline]
    fn as_ref(&self) -> &[u32]
    {
        &self.0
    }
}

/// What names a full answer to a later request that holds it: for a token
/// stream, the hexadecimal BLAKE3 digest of its integers, each in
/// little-endian bytes; for any other answer, of its JSON text.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct ResultId(String);

impl ResultId
{
    /// The id an answer whose content `value` serializes is named by: the
    /// hexadecimal BLAKE3 digest of its JSON text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: 64 lowercase hexadecimal digits; values serializing to the
    ///   same JSON text have one id, and a value that does not serialize has
    ///   the id of no text.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report pulled twice over one publication shares its
    ///   id, and one pulled after an edit changed it has another.
    /// - witness: `gandr-surface-lsp::server::tests::a_pulled_report_is_named_by_its_digest_and_answered_unchanged`
    #[spec(ensures: |ret| ret.0.len() == 64
        && ret.0.bytes().all(|digit| digit.is_ascii_digit() || (b'a' ..= b'f').contains(&digit)))]
    #[inline]
    #[must_use]
    pub fn of_json<Value>(value: &Value) -> Self
    where
        Value: Serialize + ?Sized,
    {
        let text = serde_json::to_vec(value).unwrap_or_default();
        Self(blake3::hash(&text).to_hex().to_string())
    }
}

/// One edit of a token stream: `delete_count` integers from `start` replaced
/// by `data`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TokensEdit
{
    /// The first integer replaced.
    pub start: u32,
    /// How many integers are replaced.
    pub delete_count: u32,
    /// The integers written in their place.
    pub data: TokenStream,
}

impl TokenStream
{
    /// The id a full answer carrying this stream names it by.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the hexadecimal BLAKE3 digest of the integers, each in
    ///   little-endian bytes, 64 lowercase digits: equal streams have one id,
    ///   whichever connection asked.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two equal streams share an id, and a stream with one
    ///   integer changed has another.
    /// - witness: `tokens::tests::a_delta_replaces_the_tokens_between_the_shared_ends`
    #[spec(ensures: |ret| ret.0.len() == 64
        && ret.0.bytes().all(|digit| digit.is_ascii_digit() || (b'a' ..= b'f').contains(&digit)))]
    #[inline]
    #[must_use]
    pub fn result_id(&self) -> ResultId
    {
        let mut hasher = blake3::Hasher::new();
        for integer in &self.0 {
            let _hasher = hasher.update(&integer.to_le_bytes());
        }
        ResultId(hasher.finalize().to_hex().to_string())
    }

    /// The edits turning `previous` into this stream.
    ///
    /// # Specification
    /// - requires: nothing; integers past a stream's last whole token are not
    ///   compared.
    /// - ensures: no edit when the streams' whole tokens agree; otherwise one
    ///   edit replacing the tokens between the longest prefix and the longest
    ///   suffix of whole tokens the streams share with this stream's tokens
    ///   there, its start and count in integers, each a multiple of five.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a token changed between two kept ones, a token
    ///   appended, a token removed and equal streams each answer the exact
    ///   edit, or none.
    /// - witness: `tokens::tests::a_delta_replaces_the_tokens_between_the_shared_ends`
    #[spec(ensures: |ret| ret.len() <= 1
        && ret.iter().all(|edit| edit.start.is_multiple_of(5) && edit.delete_count.is_multiple_of(5)
            && edit.data.0.len().is_multiple_of(5)))]
    #[inline]
    #[must_use]
    pub fn edits_from(
        &self,
        previous: &Self,
    ) -> Vec<TokensEdit>
    {
        let (old, new) = (previous.0.as_chunks::<5>().0, self.0.as_chunks::<5>().0);
        let prefix = old
            .iter()
            .zip(new)
            .take_while(|&(one, other)| one == other)
            .count();
        let (old, new) = (
            old.get(prefix ..).unwrap_or_default(),
            new.get(prefix ..).unwrap_or_default(),
        );
        let suffix = old
            .iter()
            .rev()
            .zip(new.iter().rev())
            .take_while(|&(one, other)| one == other)
            .count();
        let (old, new) = (
            old.get(.. old.len().saturating_sub(suffix))
                .unwrap_or_default(),
            new.get(.. new.len().saturating_sub(suffix))
                .unwrap_or_default(),
        );
        if old.is_empty() && new.is_empty() {
            return Vec::new();
        }
        let integers = |tokens: usize| u32::try_from(tokens.saturating_mul(5)).unwrap_or(u32::MAX);
        vec![TokensEdit {
            start: integers(prefix),
            delete_count: integers(old.len()),
            data: Self(new.as_flattened().to_vec()),
        }]
    }
}

#[cfg(test)]
mod tests
{
    use super::TokenStream;
    use super::TokensEdit;

    #[test]
    fn a_delta_replaces_the_tokens_between_the_shared_ends()
    {
        let stream = |tokens: &[u32]| {
            TokenStream::from(
                tokens
                    .iter()
                    .flat_map(|&token| [token, 0, 1, 0, 0])
                    .collect::<Vec<_>>(),
            )
        };
        let previous = stream(&[1, 2, 3]);
        assert_eq!(
            stream(&[1, 9, 3]).edits_from(&previous),
            vec![TokensEdit {
                start: 5,
                delete_count: 5,
                data: stream(&[9]),
            }],
            "a token changed between two kept ones: that token alone"
        );
        assert_eq!(
            stream(&[1, 2, 3, 4]).edits_from(&previous),
            vec![TokensEdit {
                start: 15,
                delete_count: 0,
                data: stream(&[4]),
            }],
            "a token appended: inserted at the end"
        );
        assert_eq!(
            stream(&[1, 3]).edits_from(&previous),
            vec![TokensEdit {
                start: 5,
                delete_count: 5,
                data: stream(&[]),
            }],
            "a token removed: deleted"
        );
        assert_eq!(
            stream(&[1, 2, 3]).edits_from(&previous),
            Vec::new(),
            "equal streams: no edit"
        );
        assert_eq!(
            stream(&[1, 2, 3]).result_id(),
            previous.result_id(),
            "equal streams share an id"
        );
        assert_ne!(
            stream(&[1, 9, 3]).result_id(),
            previous.result_id(),
            "a changed stream has another"
        );
    }
}
