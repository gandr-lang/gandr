//! The subset of the protocol's messages this server reads and writes, as
//! serde types: the parameters of the methods it serves, and the results and
//! notifications it sends.
//!
//! A parameter type names only the fields the server reads; every other field
//! a client sends is ignored, as the protocol requires of a field a server
//! does not know.

use alloc::collections::BTreeMap;
use core::fmt;
use core::mem;
use core::time::Duration;
use core::time::TryFromFloatSecsError;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_pretty::Form;
use serde::Deserialize;
use serde::Serialize;
use serde::Serializer;
use serde::ser;
use serde_json::Map;
use serde_json::Value;

use crate::markup::Markup;
use crate::position::Line;
use crate::position::Position;
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

impl From<&DocumentUri> for gandr_surface_render_remote::DocumentUri
{
    /// The render bus's name for the document the client named.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(uri: &DocumentUri) -> Self
    {
        Self::from(uri.0.clone())
    }
}

impl From<&gandr_surface_render_remote::DocumentUri> for DocumentUri
{
    /// The client's name for the document the render bus named.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(uri: &gandr_surface_render_remote::DocumentUri) -> Self
    {
        Self::from(uri.as_ref())
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
    #[spec(ensures: |ret| match self.0.strip_prefix(FILE_SCHEME)
        .and_then(|rest| rest.get(rest.find('/')?..)) {
        Some(path) if !path.contains('%') => ret == std::path::Path::new(path),
        Some(path) => ret.as_os_str().is_empty() || percent_encoding::percent_decode_str(path)
            .eq(ret.as_os_str().as_encoded_bytes().iter().copied()),
        None => ret.as_os_str().is_empty(),
    })]
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

impl fmt::Display for DocumentUri
{
    /// Writes the URI as the client spelled it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A document's version, as the client numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct DocumentVersion(i32);

impl fmt::Display for DocumentVersion
{
    /// Writes the version's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

impl From<DocumentVersion> for gandr_surface_render_remote::DocVersion
{
    /// The render bus's count of the version the client numbered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: DocumentVersion) -> Self
    {
        Self::from(version.0)
    }
}

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
    /// The changes, in order, each against the text the ones before it left.
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

/// One change to a document: the text replacing a range of it, or, with no
/// range, the document's whole new text.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct ContentChange
{
    /// The range the text replaces; none for the whole document.
    #[serde(default)]
    pub range: Option<Range>,
    /// The text replacing the range, or the document's whole text.
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

/// The parameters of `initialize` the server reads: the client's `gandr`
/// settings, passed as its initialization options, and the HTML tags its
/// markdown renderer keeps.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct InitializeParams
{
    /// The `gandr` settings, when the client passes any.
    #[serde(default)]
    pub initialization_options: Option<Settings>,
    /// The client's capabilities, of which the server reads the markdown
    /// renderer's.
    #[serde(default)]
    pub capabilities: Option<ClientCapabilities>,
}

impl InitializeParams
{
    /// The markup a hover is written in for this client: [`Markup::Html`]
    /// when its markdown renderer keeps the `span`, `pre` and `code` tags,
    /// else [`Markup::Markdown`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn markup(&self) -> Markup
    {
        let tags = self
            .capabilities
            .as_ref()
            .and_then(|capabilities| capabilities.general.as_ref())
            .and_then(|general| general.markdown.as_ref())
            .and_then(|markdown| markdown.allowed_tags.as_deref())
            .unwrap_or_default();
        Markup::of(tags)
    }
}

/// The client capabilities the server reads.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct ClientCapabilities
{
    /// `general`.
    #[serde(default)]
    pub general: Option<GeneralCapabilities>,
}

/// The general client capabilities the server reads.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct GeneralCapabilities
{
    /// `general.markdown`: the client's markdown renderer.
    #[serde(default)]
    pub markdown: Option<MarkdownCapabilities>,
}

/// What the client's markdown renderer keeps.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct MarkdownCapabilities
{
    /// `general.markdown.allowedTags`: the HTML tags it renders rather than
    /// strips.
    #[serde(default)]
    pub allowed_tags: Option<Vec<String>>,
}

/// The parameters of `workspace/didChangeConfiguration`: every section the
/// client pushes, of which the server reads `gandr`.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct ConfigurationParams
{
    /// The sections, absent from a client that has the server pull them.
    #[serde(default)]
    pub settings: Option<Sections>,
}

/// The configuration sections a client pushes.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct Sections
{
    /// The `gandr` section.
    #[serde(default)]
    pub gandr: Option<Settings>,
}

/// The `gandr` settings the server reads.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct Settings
{
    /// `gandr.diagnostics`.
    #[serde(default)]
    pub diagnostics: Option<DiagnosticSettings>,
    /// `gandr.presentation`.
    #[serde(default)]
    pub presentation: Option<PresentationSettings>,
}

/// The `gandr.presentation` settings.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct PresentationSettings
{
    /// `gandr.presentation.form`: whether a type is written with the sugar
    /// the surface reads or in the explicit formers.
    #[serde(default)]
    pub form: Option<FormSetting>,
}

/// A `gandr.presentation.form` value.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum FormSetting
{
    /// [`Form::Sugared`].
    Sugared,
    /// [`Form::Explicit`].
    Explicit,
}

impl From<FormSetting> for Form
{
    /// The form `setting` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(setting: FormSetting) -> Self
    {
        match setting {
            FormSetting::Sugared => Self::Sugared,
            FormSetting::Explicit => Self::Explicit,
        }
    }
}

/// The `gandr.diagnostics` settings.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct DiagnosticSettings
{
    /// `gandr.diagnostics.verbosity`: how much of each report a diagnostic
    /// carries.
    #[serde(default)]
    pub verbosity: Option<VerbositySetting>,
    /// `gandr.diagnostics.quiet`: how long, in seconds, a document goes
    /// without a change before a diagnostic held for the form under the caret
    /// publishes; `0` holds nothing.
    #[serde(default)]
    pub quiet: Option<QuietSetting>,
}

/// A `gandr.diagnostics.quiet` value: a nonnegative, finite number of
/// seconds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(try_from = "f64")]
#[repr(transparent)]
pub struct QuietSetting(pub Duration);

impl TryFrom<f64> for QuietSetting
{
    type Error = TryFromFloatSecsError;

    /// The interval `seconds` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the duration of `seconds` seconds.
    /// - fails: a negative, infinite or unrepresentable number of seconds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`TryFromFloatSecsError`] for a number no duration spells.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a configuration naming `0.05` holds for fifty
    ///   milliseconds and one naming `0` holds nothing.
    /// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
    #[spec(ensures: |ret| ret.is_err() || seconds >= 0.0_f64)]
    #[inline]
    fn try_from(seconds: f64) -> Result<Self, Self::Error>
    {
        Duration::try_from_secs_f64(seconds).map(Self)
    }
}

/// A `gandr.diagnostics.verbosity` value, spelled as `gandr check
/// --verbosity` spells it.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum VerbositySetting
{
    /// [`Verbosity::User`].
    User,
    /// [`Verbosity::Detailed`].
    Detailed,
    /// [`Verbosity::Debug`].
    Debug,
    /// [`Verbosity::Json`].
    Json,
}

impl From<VerbositySetting> for Verbosity
{
    /// The verbosity `setting` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(setting: VerbositySetting) -> Self
    {
        match setting {
            VerbositySetting::User => Self::User,
            VerbositySetting::Detailed => Self::Detailed,
            VerbositySetting::Debug => Self::Debug,
            VerbositySetting::Json => Self::Json,
        }
    }
}

impl Settings
{
    /// The verbosity these settings name, when they name one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn verbosity(self) -> Option<Verbosity>
    {
        self.diagnostics
            .and_then(|diagnostics| diagnostics.verbosity)
            .map(Verbosity::from)
    }

    /// The quiet interval these settings name, when they name one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn quiet(self) -> Option<Duration>
    {
        self.diagnostics
            .and_then(|diagnostics| diagnostics.quiet)
            .map(|QuietSetting(quiet)| quiet)
    }

    /// The presentation form these settings name, when they name one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn form(self) -> Option<Form>
    {
        self.presentation
            .and_then(|presentation| presentation.form)
            .map(Form::from)
    }
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

/// The parameters of a request about one position of a document:
/// `textDocument/inlineCompletion` and `textDocument/hover`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct PositionParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The cursor the request is about.
    pub position: Position,
}

/// The parameters of `textDocument/selectionRange`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct SelectionRangeParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The positions whose enclosing forms are asked for.
    pub positions: Vec<Position>,
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
    /// - ensures: positions counted in UTF-16 code units; incremental document
    ///   synchronisation with open and close notifications; semantic tokens
    ///   over the whole document and over a range, under the legend of
    ///   [`TOKEN_TYPES`] and [`TOKEN_MODIFIERS`]; inline completion; document
    ///   symbols, folding ranges and selection ranges; hover; formatting over
    ///   the whole document and over a range; code lenses, resolved in the
    ///   answer, and code actions; the server named `gandr` at this crate's
    ///   version. Nothing else: no completion list.
    /// - provides: the one capabilities answer, written by `initialize` and by
    ///   the driver's `gandr lsp --capabilities` alike.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the complete advertised wire object is checked
    ///   against a pinned supported-method golden; changed encoding, sync mode,
    ///   token legend or capability flags change that observation.
    /// - witness: `server::tests::initialize_advertises_the_token_legend`
    /// - witness: `tests::capabilities::advertised_capabilities_name_the_token_legend`
    #[spec(ensures: |ret|
        matches!(ret.capabilities.position_encoding.as_bytes(), &[b'u', b't', b'f', b'-', b'1', b'6'])
            && ret.capabilities.text_document_sync.open_close
            && ret.capabilities.text_document_sync.change.0 == SyncKind::INCREMENTAL.0
            && ret.capabilities.semantic_tokens_provider.full
            && ret.capabilities.semantic_tokens_provider.range
            && ret.capabilities.inline_completion_provider.0
            && ret.capabilities.document_symbol_provider.0
            && ret.capabilities.folding_range_provider.0
            && ret.capabilities.selection_range_provider.0
            && ret.capabilities.hover_provider.0
            && ret.capabilities.document_formatting_provider.0
            && ret.capabilities.document_range_formatting_provider.0
            && ret.capabilities.code_action_provider.0
            && ret.capabilities.definition_provider.0
            && ret.capabilities.type_definition_provider.0
            && ret.capabilities.completion_provider.0
            && !ret.capabilities.code_lens_provider.resolve_provider)]
    #[inline]
    #[must_use]
    pub const fn advertised() -> Self
    {
        Self {
            capabilities: ServerCapabilities {
                position_encoding: "utf-16",
                text_document_sync: TextDocumentSync {
                    open_close: true,
                    change: SyncKind::INCREMENTAL,
                },
                semantic_tokens_provider: SemanticTokensProvider {
                    legend: Legend {
                        token_types: TOKEN_TYPES,
                        token_modifiers: TOKEN_MODIFIERS,
                    },
                    full: true,
                    range: true,
                },
                inline_completion_provider: Provider::ANSWERED,
                document_symbol_provider: Provider::ANSWERED,
                folding_range_provider: Provider::ANSWERED,
                selection_range_provider: Provider::ANSWERED,
                hover_provider: Provider::ANSWERED,
                document_formatting_provider: Provider::ANSWERED,
                document_range_formatting_provider: Provider::ANSWERED,
                code_lens_provider: CodeLensOptions {
                    resolve_provider: false,
                },
                code_action_provider: Provider::ANSWERED,
                definition_provider: Provider::ANSWERED,
                type_definition_provider: Provider::ANSWERED,
                completion_provider: Provider::ANSWERED,
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
    /// Inline completion is answered.
    pub inline_completion_provider: Provider,
    /// Document symbols are answered.
    pub document_symbol_provider: Provider,
    /// Folding ranges are answered.
    pub folding_range_provider: Provider,
    /// Selection ranges are answered.
    pub selection_range_provider: Provider,
    /// Hovers are answered.
    pub hover_provider: Provider,
    /// Formatting the whole document is answered.
    pub document_formatting_provider: Provider,
    /// Formatting a range is answered.
    pub document_range_formatting_provider: Provider,
    /// Code lenses are answered, each resolved in the answer.
    pub code_lens_provider: CodeLensOptions,
    /// Code actions are answered.
    pub code_action_provider: Provider,
    /// Definition is answered for a declaration's name.
    pub definition_provider: Provider,
    /// Type definition is answered for a declaration's name.
    pub type_definition_provider: Provider,
    /// Completion is answered for a document's declared names and the
    /// grammar's top-level keywords.
    pub completion_provider: Provider,
}

/// Whether a request is answered, advertised as a provider with no options.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Provider(bool);

impl Provider
{
    /// The request is answered.
    pub const ANSWERED: Self = Self(true);
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
    /// A change carries the text replacing one range, or the whole document
    /// when it names none.
    pub const INCREMENTAL: Self = Self(2);
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
    /// What an inline-completion request answers for an open document.
    Inline(InlineCompletionList),
    /// What a document-symbol request answers for an open document.
    Symbols(DocumentSymbols),
    /// What a folding-range request answers for an open document.
    Folds(Vec<FoldingRange>),
    /// What a selection-range request answers for an open document: one per
    /// position asked about, in order.
    Selections(Vec<SelectionRange>),
    /// What a hover request answers over a declaration's name.
    Hover(Hover),
    /// What a formatting request answers for an open document: the edits that
    /// lay it out, in document order.
    Edits(Vec<TextEdit>),
    /// What a code-lens request answers for an open document.
    Lenses(Vec<CodeLens>),
    /// What a code-action request answers over a range of an open document.
    Actions(Vec<CodeAction>),
    /// What a definition or type-definition request answers over a
    /// declaration's name: the location of the declaration's head.
    Definition(Location),
    /// What a completion request answers for an open document: the document's
    /// declared names, then the grammar's top-level keywords.
    Completion(Vec<CompletionItem>),
    /// `null`: what `shutdown` answers, a request about a document that is not
    /// open, and a hover over nothing the server knows.
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

/// The result of an inline-completion request.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct InlineCompletionList
{
    /// The completions, the one shown first; empty when none is shown.
    pub items: Vec<InlineCompletionItem>,
}

/// One declaration of a document, and where the declaration holding it
/// stands among the document's symbols.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DocumentSymbol
{
    /// The declared name.
    pub name: String,
    /// What the declaration declares.
    pub kind: SymbolKind,
    /// The whole declaration.
    pub range: Range,
    /// The declared name's tile.
    pub selection_range: Range,
    /// The position of the declaration holding it among the document's
    /// symbols; none at the top level.
    pub holder: Option<usize>,
}

/// The declarations of a document in source order, each after the one
/// holding it, written as the protocol's nested symbols.
///
/// The nesting is kept flat, a holder named by position, so no type owns its
/// way back to itself; [`Serialize`] builds the nested wire value with a loop.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DocumentSymbols(pub Vec<DocumentSymbol>);

impl Serialize for DocumentSymbols
{
    /// Write the symbols as the protocol's tree: each symbol an object, its
    /// held symbols in source order under `children`, omitted when it holds
    /// none; a holder that is not an earlier symbol writes its symbol at the
    /// top level.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a symbol held by an earlier one, one naming itself
    ///   and one naming a later one, written in order.
    /// - witness: `protocol::tests::a_symbol_naming_itself_or_a_later_one_as_holder_stands_at_the_top`
    #[inline]
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut objects: Vec<Map<String, Value>> = Vec::with_capacity(self.0.len());
        for symbol in &self.0 {
            let mut object = Map::new();
            let _name = object.insert("name".to_owned(), Value::String(symbol.name.clone()));
            let _kind = object.insert("kind".to_owned(), Value::from(symbol.kind.0));
            let _range = object.insert(
                "range".to_owned(),
                serde_json::to_value(symbol.range).map_err(ser::Error::custom)?,
            );
            let _selection = object.insert(
                "selectionRange".to_owned(),
                serde_json::to_value(symbol.selection_range).map_err(ser::Error::custom)?,
            );
            objects.push(object);
        }
        // Every symbol a symbol holds stands after it, so writing from the
        // last gives each holder all its children before it is written itself.
        let mut held: Vec<Vec<Value>> = self.0.iter().map(|_| Vec::new()).collect();
        let mut roots: Vec<Value> = Vec::new();
        for (position, symbol) in self.0.iter().enumerate().rev() {
            let Some(mut object) = objects.pop()
            else {
                break;
            };
            if let Some(children) = held.get_mut(position)
                && !children.is_empty()
            {
                children.reverse();
                let _children =
                    object.insert("children".to_owned(), Value::Array(mem::take(children)));
            }
            match symbol
                .holder
                .filter(|&holder| holder < position)
                .and_then(|holder| held.get_mut(holder))
            {
                Some(siblings) => siblings.push(Value::Object(object)),
                None => roots.push(Value::Object(object)),
            }
        }
        roots.reverse();
        Value::Array(roots).serialize(serializer)
    }
}

/// What a symbol declares, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct SymbolKind(pub u8);

impl SymbolKind
{
    /// A module.
    pub const MODULE: Self = Self(2);
    /// A data declaration: a sum of constructors.
    pub const ENUM: Self = Self(10);
    /// A signature.
    pub const INTERFACE: Self = Self(11);
    /// A function.
    pub const FUNCTION: Self = Self(12);
    /// A value.
    pub const VARIABLE: Self = Self(13);
    /// A codata declaration: a record of observations.
    pub const STRUCT: Self = Self(23);
}

/// A run of lines a client can fold.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FoldingRange
{
    /// The first line folded.
    pub start_line: Line,
    /// The last line folded.
    pub end_line: Line,
    /// `comment` for documentation and a block comment; absent for a form.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<&'static str>,
}

/// The ranges around a position, innermost first, written as the protocol's
/// chain of each range and the range enclosing it.
///
/// The chain is kept flat so no type owns its way back to itself;
/// [`Serialize`] builds the nested wire value with a loop.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SelectionRange
{
    /// The ranges, from the one selected out to the whole document.
    pub ranges: Vec<Range>,
}

impl Serialize for SelectionRange
{
    /// Write the innermost range with each enclosing range as the `parent` of
    /// the one inside it, the outermost with none; no range writes `null`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut built = Value::Null;
        for &range in self.ranges.iter().rev() {
            let mut object = Map::new();
            let _range = object.insert(
                "range".to_owned(),
                serde_json::to_value(range).map_err(ser::Error::custom)?,
            );
            if !built.is_null() {
                let _parent = object.insert("parent".to_owned(), mem::take(&mut built));
            }
            built = Value::Object(object);
        }
        built.serialize(serializer)
    }
}

/// What a hover shows, and the range it is about.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Hover
{
    /// The text shown.
    pub contents: MarkupContent,
    /// The range the text is about.
    pub range: Range,
}

/// One edit: the text replacing a range of the document.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextEdit
{
    /// The range replaced.
    pub range: Range,
    /// The text replacing it.
    pub new_text: String,
}

/// A command a lens or an action names: its title, and the client command it
/// runs, empty for one that runs nothing.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Command
{
    /// The text shown.
    pub title: String,
    /// The client command run when it is chosen.
    pub command: &'static str,
}

/// A code lens: a command shown above a range.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CodeLens
{
    /// The range the lens is about.
    pub range: Range,
    /// What it shows.
    pub command: Command,
}

/// A code action: an edit the client offers to apply.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CodeAction
{
    /// The text shown.
    pub title: String,
    /// Its kind, `quickfix`.
    pub kind: &'static str,
    /// The edit it applies.
    pub edit: WorkspaceEdit,
}

/// Edits to several documents, by URI.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct WorkspaceEdit
{
    /// Each document's edits, in document order.
    pub changes: BTreeMap<DocumentUri, Vec<TextEdit>>,
}

/// The code-lens provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct CodeLensOptions
{
    /// Whether a lens is resolved by a second request: never.
    pub resolve_provider: bool,
}

/// Text in a markup the client renders.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MarkupContent
{
    /// Always `markdown`.
    pub kind: &'static str,
    /// The text.
    pub value: String,
}

/// One inline completion: the snippet inserted, and where.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InlineCompletionItem
{
    /// The text inserted, as a snippet.
    pub insert_text: StringValue,
    /// The range the text replaces: the empty range at the cursor.
    pub range: Range,
}

/// One completion: the name offered, its kind, and the text inserted.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CompletionItem
{
    /// The name offered.
    pub label: String,
    /// The kind the name is: a declaration's, or a keyword's.
    pub kind: u8,
    /// The text inserted: the name.
    pub insert_text: String,
}

/// A string in the protocol's snippet syntax.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct StringValue
{
    /// Always `snippet`.
    pub kind: &'static str,
    /// The snippet.
    pub value: String,
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
    #[spec(ensures: |ret| ret.range == Range::default()
        && ret.severity == Severity::ERROR && ret.code.is_none()
        && ret.source == SOURCE && ret.related_information.is_empty())]
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
    /// A warning: a builtin name the document shadows.
    pub const WARNING: Self = Self(2);
    /// Information: a goal the document leaves open.
    pub const INFORMATION: Self = Self(3);
    /// A hint: a declaration a refusal elsewhere in the document leaves
    /// unsettled, reported beside that refusal rather than as an error.
    pub const HINT: Self = Self(4);
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

    use super::DocumentSymbol;
    use super::DocumentSymbols;
    use super::DocumentUri;
    use super::SymbolKind;
    use crate::position::Range;

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
            ("file://host/", "/"),
            ("file:///a%2fb", "/a/b"),
            ("file:///literal%ZZ", "/literal%ZZ"),
        ];
        for (uri, path) in cases {
            assert_eq!(
                DocumentUri::from(uri).path(),
                PathBuf::from(path),
                "{uri} names {path:?}"
            );
        }
    }

    #[test]
    fn a_symbol_naming_itself_or_a_later_one_as_holder_stands_at_the_top()
    {
        let symbol = |name: &str, holder| DocumentSymbol {
            name: name.to_owned(),
            kind: SymbolKind::FUNCTION,
            range: Range::default(),
            selection_range: Range::default(),
            holder,
        };
        let symbols = DocumentSymbols(Vec::from([
            symbol("outer", None),
            symbol("inner", Some(0_usize)),
            symbol("itself", Some(2_usize)),
            symbol("forward", Some(4_usize)),
            symbol("last", None),
        ]));
        let wire = serde_json::to_value(&symbols).expect("the symbols encode");
        let names: Vec<&str> = wire
            .as_array()
            .map(|roots| {
                roots
                    .iter()
                    .filter_map(|root| root.get("name").and_then(serde_json::Value::as_str))
                    .collect()
            })
            .unwrap_or_default();
        assert_eq!(names, ["outer", "itself", "forward", "last"]);
        assert_eq!(
            wire.pointer("/0/children/0/name")
                .and_then(serde_json::Value::as_str),
            Some("inner"),
            "an earlier holder holds its symbol"
        );
    }
}
