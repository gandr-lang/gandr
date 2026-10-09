//! The subset of the protocol's messages this server reads and writes, as
//! serde types: the parameters of the methods it serves, and the results and
//! notifications it sends.
//!
//! A parameter type names only the fields the server reads; every other field
//! a client sends is ignored, as the protocol requires of a field a server
//! does not know.

use std::path::PathBuf;

use serde::Deserialize;
use serde::Serialize;

use crate::position::Range;
use crate::tokens::TOKEN_MODIFIERS;
use crate::tokens::TOKEN_TYPES;
use crate::tokens::TokenStream;

/// The scheme prefix of a URI naming a local file.
const FILE_SCHEME: &str = "file://";

/// The name every diagnostic's `source` and the server's `serverInfo` carry.
const SOURCE: &str = "gandr";

/// A document's URI, as the client spells it.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct DocumentUri(String);

impl From<&str> for DocumentUri
{
    /// Read the text as a URI.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(uri: &str) -> Self
    {
        Self(uri.to_owned())
    }
}

impl DocumentUri
{
    /// The path a `file` URI names.
    ///
    /// # Specification
    /// - requires: nothing; any URI is admissible input.
    /// - ensures: for `file://` followed by an authority, empty or not, and a
    ///   path, the path with its percent-escapes decoded; the empty path for a
    ///   URI of any other scheme, and for a path whose decoded bytes are not
    ///   UTF-8.
    /// - provides: the path the recheck classifies a document by, so a document
    ///   under a `fixture` directory is settled as the walk settles it.
    /// - fails: never; the empty path classifies as the strict root, as a
    ///   source under no root does.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an escaped path, an authority, another scheme and an
    ///   escape decoding to bytes that are not UTF-8, each asserted at its
    ///   exact path.
    /// - witness: `protocol::tests::a_file_uri_names_its_decoded_path`
    #[inline]
    #[must_use]
    pub fn path(&self) -> PathBuf
    {
        let Some(rest) = self.0.strip_prefix(FILE_SCHEME)
        else {
            return PathBuf::new();
        };
        let path = rest
            .find('/')
            .and_then(|slash| rest.get(slash ..))
            .unwrap_or_default();
        percent_encoding::percent_decode_str(path)
            .decode_utf8()
            .map(|path| PathBuf::from(path.as_ref()))
            .unwrap_or_default()
    }
}

/// A document's version, as the client numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct DocumentVersion(i32);

/// The parameters of `textDocument/didOpen`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct DidOpenParams
{
    /// The document opened, with its whole text.
    pub text_document: TextDocumentItem,
}

/// A document the client opened.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct TextDocumentItem
{
    /// The document's URI.
    pub uri: DocumentUri,
    /// The version of its text.
    pub version: DocumentVersion,
    /// Its whole text.
    pub text: String,
}

/// The parameters of `textDocument/didChange`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DidChangeParams
{
    /// The document changed, at its new version.
    pub text_document: VersionedDocument,
    /// The changes, in order; under full synchronisation each carries the
    /// whole text, so the last is the document.
    pub content_changes: Vec<ContentChange>,
}

/// A document at a version.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct VersionedDocument
{
    /// The document's URI.
    pub uri: DocumentUri,
    /// The version the change brings it to.
    pub version: DocumentVersion,
}

/// One change to a document under full synchronisation: its whole new text.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct ContentChange
{
    /// The document's whole text after the change.
    pub text: String,
}

/// The parameters of `textDocument/didClose`, and of
/// `textDocument/semanticTokens/full`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct DocumentParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
}

/// A document, by its URI alone.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct DocumentIdentifier
{
    /// The document's URI.
    pub uri: DocumentUri,
}

/// The parameters of `textDocument/semanticTokens/range`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct RangeParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The range whose tokens are asked for.
    pub range: Range,
}

/// The result of `initialize`: what the server provides, and its name.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InitializeResult
{
    /// The capabilities the server advertises.
    pub capabilities: ServerCapabilities,
    /// The server's name and version.
    pub server_info: ServerInfo,
}

impl InitializeResult
{
    /// What this server advertises.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: positions counted in UTF-16 code units; full document
    ///   synchronisation with open and close notifications; semantic tokens
    ///   over the whole document and over a range, under the legend of
    ///   [`TOKEN_TYPES`] and [`TOKEN_MODIFIERS`]; the server named `gandr` at
    ///   this crate's version. Nothing else: no hover, no completion.
    /// - provides: the one capabilities answer, written by `initialize` and by
    ///   the driver's `gandr lsp --capabilities` alike.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the advertised object compared whole, over the wire
    ///   and through the public display.
    /// - witness: `server::tests::initialize_advertises_the_token_legend`
    /// - witness: `capabilities::capabilities::advertised_capabilities_name_the_token_legend`
    #[inline]
    #[must_use]
    pub const fn advertised() -> Self
    {
        Self {
            capabilities: ServerCapabilities {
                position_encoding: "utf-16",
                text_document_sync: TextDocumentSync {
                    open_close: true,
                    change: SyncKind::FULL,
                },
                semantic_tokens_provider: SemanticTokensProvider {
                    legend: Legend {
                        token_types: TOKEN_TYPES,
                        token_modifiers: TOKEN_MODIFIERS,
                    },
                    full: true,
                    range: true,
                },
            },
            server_info: ServerInfo {
                name: SOURCE,
                version: env!("CARGO_PKG_VERSION"),
            },
        }
    }
}

/// The capabilities the server advertises.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ServerCapabilities
{
    /// The encoding positions are counted in.
    pub position_encoding: &'static str,
    /// How the client keeps the server's copy of a document current.
    pub text_document_sync: TextDocumentSync,
    /// The semantic tokens the server answers.
    pub semantic_tokens_provider: SemanticTokensProvider,
}

/// Document synchronisation, as advertised.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentSync
{
    /// The client sends open and close notifications.
    pub open_close: bool,
    /// What a change notification carries.
    pub change: SyncKind,
}

/// What a change notification carries, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct SyncKind(u8);

impl SyncKind
{
    /// Every change carries the whole document.
    pub const FULL: Self = Self(1);
}

/// The semantic-token provider, as advertised.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SemanticTokensProvider
{
    /// The token types and modifiers a token's integers index.
    pub legend: Legend,
    /// Tokens over the whole document are answered.
    pub full: bool,
    /// Tokens over a range are answered.
    pub range: bool,
}

/// The token legend.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Legend
{
    /// The token types, in the order a token's type integer indexes.
    pub token_types: [&'static str; 14],
    /// The token modifiers, in the order a token's modifier bits index.
    pub token_modifiers: [&'static str; 2],
}

/// The server's name and version.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ServerInfo
{
    /// The server's name.
    pub name: &'static str,
    /// Its version.
    pub version: &'static str,
}

/// The result of a request the server answers.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(untagged)]
pub enum Answer
{
    /// What `initialize` answers: the advertised capabilities, boxed since
    /// they are sent once per session and outweigh every other answer.
    Initialize(Box<InitializeResult>),
    /// What a semantic-tokens request answers for an open document.
    Tokens(SemanticTokens),
    /// `null`: what `shutdown` answers, and a semantic-tokens request for a
    /// document that is not open.
    Nothing,
}

/// The result of a semantic-tokens request.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct SemanticTokens
{
    /// The token stream, five integers per token.
    pub data: TokenStream,
}

/// The parameters of `textDocument/publishDiagnostics`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct PublishParams
{
    /// The document the diagnostics are about.
    pub uri: DocumentUri,
    /// The version of the text they were computed from; absent when the
    /// document was closed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<DocumentVersion>,
    /// Every diagnostic of the document; an empty list clears them.
    pub diagnostics: Vec<Diagnostic>,
}

/// One diagnostic, as the editor shows it.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Diagnostic
{
    /// The range it marks.
    pub range: Range,
    /// How severe it is.
    pub severity: Severity,
    /// The vocabulary name of the refusal it reports, when it reports one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    /// The tool that produced it: always `gandr`.
    pub source: &'static str,
    /// What it says.
    pub message: String,
    /// The loci that explain it, each with what it explains.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub related_information: Vec<RelatedInformation>,
}

impl Diagnostic
{
    /// A diagnostic about the document as a whole, at its origin.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an error at the empty range at line 0, character 0, carrying
    ///   `message` and no code or related location.
    /// - provides: the diagnostic a fault with no position is published as.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source the lowering refuses at no position is
    ///   asserted at its exact diagnostic.
    /// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
    #[inline]
    #[must_use]
    pub fn at_origin(message: String) -> Self
    {
        Self {
            range: Range::default(),
            severity: Severity::ERROR,
            code: None,
            source: SOURCE,
            message,
            related_information: Vec::new(),
        }
    }

    /// A diagnostic at `range`, carrying `message`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        range: Range,
        severity: Severity,
        message: String,
    ) -> Self
    {
        Self {
            range,
            severity,
            code: None,
            source: SOURCE,
            message,
            related_information: Vec::new(),
        }
    }
}

/// A diagnostic's severity, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Severity(u8);

impl Severity
{
    /// An error: the document does not check.
    pub const ERROR: Self = Self(1);
    /// Information: a goal the document leaves open.
    pub const INFORMATION: Self = Self(3);
}

/// A locus that explains a diagnostic.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct RelatedInformation
{
    /// Where it is.
    pub location: Location,
    /// What it explains.
    pub message: String,
}

/// A range in a document.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Location
{
    /// The document.
    pub uri: DocumentUri,
    /// The range within it.
    pub range: Range,
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::DocumentUri;

    #[test]
    fn a_file_uri_names_its_decoded_path()
    {
        let cases = [
            ("file:///tmp/a%20b/c.gandr", "/tmp/a b/c.gandr"),
            (
                "file://localhost/srv/fixture/x.gandr",
                "/srv/fixture/x.gandr",
            ),
            ("file:///x%C3%A9.gandr", "/xé.gandr"),
            ("untitled:Untitled-1", ""),
            ("file:///bad%FF.gandr", ""),
            ("file://host", ""),
        ];
        for (uri, path) in cases {
            assert_eq!(
                DocumentUri::from(uri).path(),
                PathBuf::from(path),
                "{uri} names {path:?}"
            );
        }
    }
}
