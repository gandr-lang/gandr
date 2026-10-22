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
use gandr_surface_pretty::Spelling;
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
use crate::syntax::TREE_SCHEME;
use crate::tokens::ResultId;
use crate::tokens::TOKEN_MODIFIERS;
use crate::tokens::TOKEN_TYPES;
use crate::tokens::TokenStream;
use crate::tokens::TokensEdit;

/// The scheme prefix of a URI naming a local file.
const FILE_SCHEME: &str = "file://";

/// The bytes a path keeps escaped in a `file` URI: the controls, the space,
/// the delimiters a URI reads around a path, and the escape itself, so the
/// path decodes back to itself.
const PATH_ESCAPED: &percent_encoding::AsciiSet = &percent_encoding::CONTROLS
    .add(b' ')
    .add(b'"')
    .add(b'#')
    .add(b'%')
    .add(b'<')
    .add(b'>')
    .add(b'?')
    .add(b'`')
    .add(b'{')
    .add(b'}');

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

    /// The `file` URI naming the absolute path `path`.
    ///
    /// # Specification
    /// - requires: nothing; any path is admissible input.
    /// - ensures: for a path that is UTF-8 and starts at the root, `file://`
    ///   followed by the path with its controls, spaces, URI delimiters and
    ///   percent signs escaped, which [`Self::path`] reads back as `path`; none
    ///   for any other path.
    /// - provides: the URI a definition in a sibling the document imports
    ///   names.
    /// - fails: never; a path no URI spells answers none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain path, one with a space, a percent sign and a
    ///   non-ASCII letter, and a relative path, each asserted at its exact URI
    ///   or none.
    /// - witness: `protocol::tests::a_path_names_the_file_uri_that_reads_back_to_it`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|uri| uri.path() == path))]
    #[inline]
    #[must_use]
    pub fn of_path(path: &std::path::Path) -> Option<Self>
    {
        let spelled = path.to_str()?;
        if !spelled.starts_with('/') {
            return None;
        }
        Some(Self(format!(
            "{FILE_SCHEME}{}",
            percent_encoding::utf8_percent_encode(spelled, PATH_ESCAPED)
        )))
    }

    /// The `file` URI of the document whose syntax tree this URI names: the
    /// tree scheme, a colon and the rest of the `file` URI after its own
    /// `file:`, with or without the empty authority.
    ///
    /// # Specification
    /// - requires: nothing; any URI is admissible input.
    /// - ensures: for [`TREE_SCHEME`], a colon and a rest starting with `//`, `file:`
    ///   followed by the rest; for a rest starting with a single `/`, `file://`
    ///   followed by the rest; none for a URI of another scheme or a rest
    ///   naming no path.
    /// - provides: the document a `workspace/textDocumentContent` request
    ///   prints the tree of, however the client spells the authority.
    /// - fails: never; a URI naming no document answers none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree URI with and without its empty authority, an
    ///   escaped path, a host, a `file` URI, another scheme and a tree URI with
    ///   no path, each asserted at its exact document or none.
    /// - witness: `protocol::tests::a_tree_uri_names_the_document_it_views`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|source| source.0.starts_with(FILE_SCHEME)
        && source.0.get(FILE_SCHEME.len() ..) == self.0.get(TREE_SCHEME.len().saturating_add(1) ..)
            .map(|rest| rest.strip_prefix("//").unwrap_or(rest))))]
    #[inline]
    #[must_use]
    pub fn viewed(&self) -> Option<Self>
    {
        let rest = self.0.strip_prefix(TREE_SCHEME)?.strip_prefix(':')?;
        if rest.starts_with("//") {
            Some(Self(format!("file:{rest}")))
        }
        else if rest.starts_with('/') {
            Some(Self(format!("{FILE_SCHEME}{rest}")))
        }
        else {
            None
        }
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

/// The parameters of `gandr/importFiles`: the document importing and the
/// files it imports, as a drop of them into it names them.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct ImportFilesParams
{
    /// The document importing.
    pub text_document: DocumentIdentifier,
    /// The files imported, each by its `file` URI.
    pub files: Vec<DocumentUri>,
}

/// The parameters of `gandr/copiedSources`: the document copied from and the
/// ranges copied.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct CopiedSourcesParams
{
    /// The document copied from.
    pub text_document: DocumentIdentifier,
    /// The ranges copied.
    pub ranges: Vec<Range>,
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
/// settings, passed as its initialization options, the HTML tags its
/// markdown renderer keeps, whether it takes a definition as a link, whether
/// it takes a parameter as its place in a signature's label, and the folders
/// it opened.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct InitializeParams
{
    /// The `gandr` settings, when the client passes any.
    #[serde(default)]
    pub initialization_options: Option<Settings>,
    /// The client's capabilities, of which the server reads the markdown
    /// renderer's, the definition request's and the signature-help request's.
    #[serde(default)]
    pub capabilities: Option<ClientCapabilities>,
    /// The folders the client opened, when it names any.
    #[serde(default)]
    pub workspace_folders: Option<Vec<WorkspaceFolder>>,
    /// The one folder the client opened, read when it names no workspace
    /// folders.
    #[serde(default)]
    pub root_uri: Option<DocumentUri>,
    /// How much of its exchanges the client has the server trace, when it
    /// says.
    #[serde(default)]
    pub trace: Option<Trace>,
}

/// A folder the client opened.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct WorkspaceFolder
{
    /// The folder's URI.
    pub uri: DocumentUri,
}

/// The parameters of `workspace/didChangeWorkspaceFolders`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct FoldersChangedParams
{
    /// The folders opened and closed.
    pub event: FoldersChanged,
}

/// The folders a client opened and closed.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct FoldersChanged
{
    /// The folders opened.
    #[serde(default)]
    pub added: Vec<WorkspaceFolder>,
    /// The folders closed.
    #[serde(default)]
    pub removed: Vec<WorkspaceFolder>,
}

impl FoldersChanged
{
    /// The paths of the folders opened, each a `file` URI's path.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn added(&self) -> Vec<PathBuf>
    {
        absolute(self.added.iter().map(|folder| &folder.uri))
    }

    /// The paths of the folders closed, each a `file` URI's path.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn removed(&self) -> Vec<PathBuf>
    {
        absolute(self.removed.iter().map(|folder| &folder.uri))
    }
}

/// The path of each of `uris` that a `file` URI names, in order.
///
/// # Specification
/// trivial.
fn absolute<'uri>(uris: impl Iterator<Item = &'uri DocumentUri>) -> Vec<PathBuf>
{
    uris.map(DocumentUri::path)
        .filter(|path| path.is_absolute())
        .collect()
}

impl InitializeParams
{
    /// The paths of the folders the client opened: its workspace folders, or
    /// its root when it names none, each a `file` URI's path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the path of each workspace folder a `file` URI names, in
    ///   order; when the client names no workspace folders, the root's path if
    ///   a `file` URI names it; nothing otherwise.
    /// - fails: never; a folder no `file` URI names is left out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — folders over a root, a root alone, a folder of
    ///   another scheme and no folder, each at its exact paths.
    /// - witness: `protocol::tests::the_folders_a_client_opened_are_its_roots`
    #[spec(ensures: |ret| ret.iter().all(|path| path.is_absolute()))]
    #[must_use]
    pub fn roots(&self) -> Vec<PathBuf>
    {
        let named = self.workspace_folders.as_ref().map_or_else(
            || self.root_uri.iter().collect::<Vec<_>>(),
            |folders| folders.iter().map(|folder| &folder.uri).collect(),
        );
        absolute(named.into_iter())
    }

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

    /// How a definition is answered to this client: as links from the name
    /// asked about when it declares `textDocument.definition.linkSupport`, as
    /// locations otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn links(&self) -> Linked
    {
        Linked(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.text_document.as_ref())
                .and_then(|text_document| text_document.definition.as_ref())
                .and_then(|definition| definition.link_support)
                .unwrap_or(false),
        )
    }

    /// How a signature's parameters are answered to this client: as their
    /// place in the label when it declares
    /// `textDocument.signatureHelp.signatureInformation.parameterInformation.
    /// labelOffsetSupport`, as their text otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn label_offsets(&self) -> LabelOffsets
    {
        LabelOffsets(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.text_document.as_ref())
                .and_then(|text_document| text_document.signature_help.as_ref())
                .and_then(|help| help.signature_information.as_ref())
                .and_then(|information| information.parameter_information.as_ref())
                .and_then(|parameter| parameter.label_offset_support)
                .unwrap_or(false),
        )
    }

    /// Whether completions are answered to this client with label details:
    /// when it declares `textDocument.completion.completionItem.
    /// labelDetailsSupport`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn label_details(&self) -> LabelsDetailed
    {
        LabelsDetailed(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.text_document.as_ref())
                .and_then(|text_document| text_document.completion.as_ref())
                .and_then(|completion| completion.completion_item.as_ref())
                .and_then(|item| item.label_details_support)
                .unwrap_or(false),
        )
    }

    /// Whether completions are answered to this client with snippets: when
    /// it declares `textDocument.completion.completionItem.snippetSupport`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn snippets(&self) -> TakesSnippets
    {
        TakesSnippets(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.text_document.as_ref())
                .and_then(|text_document| text_document.completion.as_ref())
                .and_then(|completion| completion.completion_item.as_ref())
                .and_then(|item| item.snippet_support)
                .unwrap_or(false),
        )
    }

    /// Whether folds are answered to this client with the text a folded range
    /// shows: when it declares `textDocument.foldingRange.foldingRange.
    /// collapsedText`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn collapsed_folds(&self) -> FoldsCollapsed
    {
        FoldsCollapsed(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.text_document.as_ref())
                .and_then(|text_document| text_document.folding_range.as_ref())
                .and_then(|folding| folding.folding_range.as_ref())
                .and_then(|range| range.collapsed_text)
                .unwrap_or(false),
        )
    }

    /// Whether this client asks for the declarations an inlay hint's label
    /// names by a second request: when the properties it declares under
    /// `textDocument.inlayHint.resolveSupport` name `label.location`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a client declaring no resolve support, one resolving
    ///   the tooltip alone and one resolving the label's locations, each
    ///   asserted at the hint it is sent.
    /// - witness: `server::tests::an_inlay_hint_links_the_families_its_type_names_764`
    #[inline]
    #[must_use]
    pub fn resolves_hint_locations(&self) -> ResolvesHintLocations
    {
        self.capabilities
            .as_ref()
            .and_then(|capabilities| capabilities.text_document.as_ref())
            .and_then(|text_document| text_document.inlay_hint)
            .and_then(|hints| hints.resolve_support)
            .unwrap_or_default()
    }

    /// Whether this client watches files for the server once asked: when it
    /// declares `workspace.didChangeWatchedFiles.dynamicRegistration`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn watches_files(&self) -> WatchesFiles
    {
        WatchesFiles(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.workspace)
                .and_then(|workspace| workspace.did_change_watched_files)
                .and_then(|watched| watched.dynamic_registration)
                .unwrap_or(false),
        )
    }

    /// Whether this client shows the progress of work the server starts: when
    /// it declares `window.workDoneProgress`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn shows_progress(&self) -> ShowsProgress
    {
        ShowsProgress(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.window)
                .and_then(|window| window.work_done_progress)
                .unwrap_or(false),
        )
    }

    /// Which answers this client requests again when asked to: each it
    /// declares `refreshSupport` for under `workspace.codeLens`,
    /// `workspace.semanticTokens`, `workspace.foldingRange`,
    /// `workspace.inlayHint` and `workspace.diagnostics`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn refreshing(&self) -> Refreshing
    {
        let workspace = self
            .capabilities
            .as_ref()
            .and_then(|capabilities| capabilities.workspace)
            .unwrap_or_default();
        let refreshes = |answer: Option<RefreshCapabilities>| {
            answer
                .and_then(|answer| answer.refresh_support)
                .unwrap_or(false)
        };
        Refreshing {
            lenses: Refreshes(refreshes(workspace.code_lens)),
            tokens: Refreshes(refreshes(workspace.semantic_tokens)),
            folds: Refreshes(refreshes(workspace.folding_range)),
            hints: Refreshes(refreshes(workspace.inlay_hint)),
            diagnostics: Refreshes(refreshes(workspace.diagnostics)),
        }
    }

    /// How much of its exchanges this client has the server trace: `off`
    /// when it does not say.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn trace(&self) -> Trace
    {
        self.trace.unwrap_or_default()
    }

    /// Whether this client answers a pull of its settings: when it declares
    /// `workspace.configuration`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pulls_configuration(&self) -> PullsConfiguration
    {
        PullsConfiguration(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.workspace)
                .and_then(|workspace| workspace.configuration)
                .unwrap_or(false),
        )
    }

    /// Whether this client applies an edit the server asks it to: when it
    /// declares `workspace.applyEdit`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn applies_edits(&self) -> AppliesEdits
    {
        AppliesEdits(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.workspace)
                .and_then(|workspace| workspace.apply_edit)
                .unwrap_or(false),
        )
    }

    /// Whether this client shows a document the server asks it to: when it
    /// declares `window.showDocument.support`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn shows_documents(&self) -> ShowsDocuments
    {
        ShowsDocuments(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.window)
                .and_then(|window| window.show_document)
                .and_then(|show| show.support)
                .unwrap_or(false),
        )
    }

    /// Whether this client answers a request for its workspace folders: when
    /// it declares `workspace.workspaceFolders`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lists_folders(&self) -> ListsFolders
    {
        ListsFolders(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.workspace)
                .and_then(|workspace| workspace.workspace_folders)
                .unwrap_or(false),
        )
    }

    /// Whether this client shows the text of a virtual document the server
    /// serves, and so requests it again when asked: when it declares
    /// `workspace.textDocumentContent`, whose refresh the protocol gives no
    /// capability of its own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn views_content(&self) -> ViewsContent
    {
        ViewsContent(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.workspace)
                .is_some_and(|workspace| workspace.text_document_content.is_some()),
        )
    }

    /// Whether this client pulls a document's diagnostics rather than taking
    /// them as they are published: when it declares `textDocument.diagnostic`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pulls_diagnostics(&self) -> PullsDiagnostics
    {
        PullsDiagnostics(
            self.capabilities
                .as_ref()
                .and_then(|capabilities| capabilities.text_document)
                .is_some_and(|text_document| text_document.diagnostic.is_some()),
        )
    }

    /// How this client takes a workspace edit: versioned when it declares
    /// `workspace.workspaceEdit.documentChanges`; annotated as well when it
    /// also declares `workspace.workspaceEdit.changeAnnotationSupport`; and
    /// taking snippet edits when it also declares
    /// `workspace.workspaceEdit.snippetEditSupport` (3.18).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn edits_shaped(&self) -> EditsShaped
    {
        let taken = self
            .capabilities
            .as_ref()
            .and_then(|capabilities| capabilities.workspace)
            .and_then(|workspace| workspace.workspace_edit)
            .unwrap_or_default();
        let versioned = taken.document_changes.unwrap_or(false);
        EditsShaped {
            versioned,
            annotated: versioned && taken.change_annotation_support.is_some(),
            snippets: versioned && taken.snippet_edit_support.unwrap_or(false),
        }
    }
}

/// The paths of `folders`, each a `file` URI's path, in order.
///
/// # Specification
/// trivial.
#[must_use]
pub fn folder_roots(folders: &[WorkspaceFolder]) -> Vec<PathBuf>
{
    absolute(folders.iter().map(|folder| &folder.uri))
}

/// Whether a client applies an edit the server asks it to.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct AppliesEdits(pub bool);

/// Whether a client shows a document the server asks it to.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ShowsDocuments(pub bool);

/// Whether a client answers a request for its workspace folders.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ListsFolders(pub bool);

/// Whether a client shows the text of a virtual document the server serves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ViewsContent(pub bool);

/// Whether a client pulls a document's diagnostics rather than taking them as
/// they are published.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PullsDiagnostics(pub bool);

/// How a client takes a workspace edit.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct EditsShaped
{
    /// Each document's edits with the version of the copy they were made
    /// against.
    pub versioned: bool,
    /// Among versioned edits, each to a document the client holds no copy of
    /// annotated for its user to confirm.
    pub annotated: bool,
    /// Among versioned edits, an edit may be a snippet, its tab stops for the
    /// user to fill.
    pub snippets: bool,
}

impl EditsShaped
{
    /// A client that takes edits by URI alone.
    pub const BY_URI: Self = Self {
        versioned: false,
        annotated: false,
        snippets: false,
    };
}

/// Whether a client answers a pull of its settings.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PullsConfiguration(pub bool);

/// How much of its exchanges the server traces to the client.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum Trace
{
    /// Nothing.
    #[default]
    Off,
    /// Each log line's subject.
    Messages,
    /// Each log line's subject and its detail.
    Verbose,
}

/// The parameters of `$/setTrace`: the level the client sets.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct SetTraceParams
{
    /// The level.
    pub value: Trace,
}

/// The parameters of `$/logTrace`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TraceParams
{
    /// What is traced.
    pub message: String,
    /// Its detail, at [`Trace::Verbose`] alone.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verbose: Option<String>,
}

/// How a window message reads, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct MessageType(u8);

impl MessageType
{
    /// An error.
    pub const ERROR: Self = Self(1);
    /// A warning.
    pub const WARNING: Self = Self(2);
    /// Information.
    pub const INFO: Self = Self(3);
    /// A log line.
    pub const LOG: Self = Self(4);
}

/// The parameters of `window/showMessage` and `window/logMessage`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MessageParams
{
    /// How it reads.
    #[serde(rename = "type")]
    pub kind: MessageType,
    /// The message.
    pub message: String,
}

/// The parameters of `window/showMessageRequest`: a message and the choices
/// put with it.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ChoiceParams
{
    /// How it reads.
    #[serde(rename = "type")]
    pub kind: MessageType,
    /// The message.
    pub message: String,
    /// The choices, in the order shown.
    pub actions: Vec<MessageAction>,
}

/// One choice put to the user, and the one the client answers with.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct MessageAction
{
    /// The text shown.
    pub title: String,
}

/// Whether a client takes a definition as links from the name asked about.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Linked(pub bool);

/// Whether a client takes a signature's parameter as its place in the label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LabelOffsets(pub bool);

/// Whether a client shows a completion's label details.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LabelsDetailed(pub bool);

/// Whether a client takes a completion's text as a snippet.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TakesSnippets(pub bool);

/// Whether a client shows the text a fold names in place of the folded lines.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FoldsCollapsed(pub bool);

/// Whether a client asks for the declarations an inlay hint's label names by
/// a second request: when the properties it resolves name `label.location`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(from = "HintResolveSupport")]
pub struct ResolvesHintLocations(pub bool);

/// `textDocument.inlayHint.resolveSupport`, as a client sends it.
#[derive(Deserialize)]
#[repr(transparent)]
struct HintResolveSupport
{
    /// The properties of a hint the client resolves by a second request.
    #[serde(default)]
    properties: Vec<String>,
}

impl From<HintResolveSupport> for ResolvesHintLocations
{
    /// Whether the properties name `label.location`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — properties naming the tooltip alone, and the tooltip
    ///   with `label.location`, each asserted at the hint its client is sent.
    /// - witness: `server::tests::an_inlay_hint_links_the_families_its_type_names_764`
    #[inline]
    fn from(support: HintResolveSupport) -> Self
    {
        Self(
            support
                .properties
                .iter()
                .any(|property| property == "label.location"),
        )
    }
}

/// Whether a client watches files for the server once asked to.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct WatchesFiles(pub bool);

/// Whether a client shows the progress of work the server starts.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ShowsProgress(pub bool);

/// Whether a client requests an answer again when the server asks.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Refreshes(pub bool);

/// Which answers a client requests again when the server asks.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Refreshing
{
    /// Its code lenses.
    pub lenses: Refreshes,
    /// Its semantic tokens.
    pub tokens: Refreshes,
    /// Its folding ranges.
    pub folds: Refreshes,
    /// Its inlay hints.
    pub hints: Refreshes,
    /// Its pulled diagnostics.
    pub diagnostics: Refreshes,
}

impl Refreshing
{
    /// A client that requests nothing again.
    pub const NONE: Self = Self {
        lenses: Refreshes(false),
        tokens: Refreshes(false),
        folds: Refreshes(false),
        hints: Refreshes(false),
        diagnostics: Refreshes(false),
    };
}

/// The client capabilities the server reads.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct ClientCapabilities
{
    /// `general`.
    #[serde(default)]
    pub general: Option<GeneralCapabilities>,
    /// `textDocument`.
    #[serde(default)]
    pub text_document: Option<TextDocumentCapabilities>,
    /// `workspace`.
    #[serde(default)]
    pub workspace: Option<WorkspaceCapabilities>,
    /// `window`.
    #[serde(default)]
    pub window: Option<WindowCapabilities>,
}

/// The window client capabilities the server reads.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct WindowCapabilities
{
    /// `window.workDoneProgress`: whether it shows the progress of work the
    /// server starts.
    #[serde(default)]
    pub work_done_progress: Option<bool>,
    /// `window.showDocument`.
    #[serde(default)]
    pub show_document: Option<ShowDocumentCapabilities>,
}

/// What a client offers of showing a document the server asks it to.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct ShowDocumentCapabilities
{
    /// `support`: whether it shows one.
    #[serde(default)]
    pub support: Option<bool>,
}

/// The workspace client capabilities the server reads.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct WorkspaceCapabilities
{
    /// `workspace.didChangeWatchedFiles`.
    #[serde(default)]
    pub did_change_watched_files: Option<WatchedFilesCapabilities>,
    /// `workspace.codeLens`.
    #[serde(default)]
    pub code_lens: Option<RefreshCapabilities>,
    /// `workspace.semanticTokens`.
    #[serde(default)]
    pub semantic_tokens: Option<RefreshCapabilities>,
    /// `workspace.foldingRange`.
    #[serde(default)]
    pub folding_range: Option<RefreshCapabilities>,
    /// `workspace.inlayHint`.
    #[serde(default)]
    pub inlay_hint: Option<RefreshCapabilities>,
    /// `workspace.diagnostics`.
    #[serde(default)]
    pub diagnostics: Option<RefreshCapabilities>,
    /// `workspace.configuration`: whether it answers a pull of its settings.
    #[serde(default)]
    pub configuration: Option<bool>,
    /// `workspace.applyEdit`: whether it applies an edit the server asks it
    /// to.
    #[serde(default)]
    pub apply_edit: Option<bool>,
    /// `workspace.workspaceFolders`: whether it answers a request for its
    /// workspace folders.
    #[serde(default)]
    pub workspace_folders: Option<bool>,
    /// `workspace.textDocumentContent`: present when it shows the text of a
    /// virtual document the server serves.
    #[serde(default)]
    pub text_document_content: Option<ContentCapabilities>,
    /// `workspace.workspaceEdit`.
    #[serde(default)]
    pub workspace_edit: Option<WorkspaceEditCapabilities>,
}

/// What a client takes of a workspace edit.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct WorkspaceEditCapabilities
{
    /// `documentChanges`: whether it takes each document's edits with the
    /// version they were made against.
    #[serde(default)]
    pub document_changes: Option<bool>,
    /// `changeAnnotationSupport`: present when it takes edits annotated for
    /// its user to confirm.
    #[serde(default)]
    pub change_annotation_support: Option<AnnotationCapabilities>,
    /// `snippetEditSupport` (3.18): whether it takes an edit whose text is a
    /// snippet.
    #[serde(default)]
    pub snippet_edit_support: Option<bool>,
}

/// What a client offers of annotated edits.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct AnnotationCapabilities
{
    /// `groupsOnLabel`: whether it groups edits by their annotations' labels.
    #[serde(default)]
    pub groups_on_label: Option<bool>,
}

/// What a client offers of showing a virtual document's text.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct ContentCapabilities
{
    /// `dynamicRegistration`: whether it takes the schemes by registration.
    #[serde(default)]
    pub dynamic_registration: Option<bool>,
}

/// What the client offers of requesting a feature's answers again.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct RefreshCapabilities
{
    /// `refreshSupport`: whether it requests the answers again when the
    /// server asks.
    #[serde(default)]
    pub refresh_support: Option<bool>,
}

/// What the client offers of watching files.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct WatchedFilesCapabilities
{
    /// `workspace.didChangeWatchedFiles.dynamicRegistration`: whether it
    /// watches the files a server registers watchers for.
    #[serde(default)]
    pub dynamic_registration: Option<bool>,
}

/// The glob of the files the server has the client watch: every gandr source.
pub const WATCHED_FILES: &str = "**/*.gandr";

/// The parameters of `client/registerCapability`: the registrations asked
/// for.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct RegistrationParams
{
    /// The registrations.
    pub registrations: Vec<Registration>,
}

/// One registration: the method registered under an identifier, with its
/// options.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Registration
{
    /// The identifier a later unregistration names.
    pub id: &'static str,
    /// The method registered.
    pub method: &'static str,
    /// What the client watches.
    pub register_options: WatchedFilesOptions,
}

/// The files a client is asked to watch.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct WatchedFilesOptions
{
    /// One watcher per glob.
    pub watchers: Vec<FileWatcher>,
}

/// A watcher over every file a glob matches, for creation, change and
/// deletion.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct FileWatcher
{
    /// The glob.
    pub glob_pattern: &'static str,
}

impl RegistrationParams
{
    /// The one registration that has the client watch every gandr source,
    /// [`WATCHED_FILES`], for `workspace/didChangeWatchedFiles`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn watched_files() -> Self
    {
        Self {
            registrations: Vec::from([Registration {
                id: "workspace/didChangeWatchedFiles",
                method: "workspace/didChangeWatchedFiles",
                register_options: WatchedFilesOptions {
                    watchers: Vec::from([FileWatcher {
                        glob_pattern: WATCHED_FILES,
                    }]),
                },
            }]),
        }
    }
}

/// The parameters of `client/unregisterCapability`: the registrations
/// withdrawn, under the field name the protocol spells.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct UnregistrationParams
{
    /// The registrations withdrawn.
    pub unregisterations: Vec<Unregistration>,
}

/// One registration withdrawn: the identifier and method it was registered
/// under.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct Unregistration
{
    /// The identifier.
    pub id: &'static str,
    /// The method.
    pub method: &'static str,
}

impl UnregistrationParams
{
    /// The withdrawal of the registration
    /// [`RegistrationParams::watched_files`] makes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn watched_files() -> Self
    {
        Self {
            unregisterations: Vec::from([Unregistration {
                id: "workspace/didChangeWatchedFiles",
                method: "workspace/didChangeWatchedFiles",
            }]),
        }
    }
}

/// The parameters of `workspace/configuration`: the sections pulled.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct PullParams
{
    /// One item per section.
    pub items: Vec<PulledSection>,
}

/// One section pulled.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct PulledSection
{
    /// The section's name.
    pub section: &'static str,
}

impl PullParams
{
    /// The pull of the `gandr` section alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn gandr() -> Self
    {
        Self {
            items: Vec::from([PulledSection { section: "gandr" }]),
        }
    }
}

/// The parameters of `workspace/didChangeWatchedFiles`: each file created,
/// changed or deleted, of which the server reads the URI.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct WatchedFilesParams
{
    /// The changes.
    #[serde(default)]
    pub changes: Vec<FileEvent>,
}

/// One file created, changed or deleted.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct FileEvent
{
    /// The file's URI.
    pub uri: DocumentUri,
}

/// The parameters of `workspace/didCreateFiles` and `didDeleteFiles`, and of
/// `willCreateFiles` and `willDeleteFiles`: each file or folder created or
/// deleted, or about to be, by its URI.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct FilesParams
{
    /// The files and folders.
    #[serde(default)]
    pub files: Vec<FileEvent>,
}

/// The parameters of `workspace/didRenameFiles` and `willRenameFiles`: each
/// file or folder renamed, or about to be.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct RenameFilesParams
{
    /// The renames.
    #[serde(default)]
    pub files: Vec<FileRename>,
}

/// One file or folder renamed: where it was and where it goes.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct FileRename
{
    /// Where it was.
    pub old_uri: DocumentUri,
    /// Where it goes.
    pub new_uri: DocumentUri,
}

/// The token one piece of work's progress is reported under.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct ProgressToken(pub String);

/// The parameters of `window/workDoneProgress/create`: the token the client
/// is asked to show progress under.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct CreateProgressParams
{
    /// The token.
    pub token: ProgressToken,
}

/// The parameters of `window/workDoneProgress/cancel`: the token of the work
/// the client asks to cancel.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct CancelProgressParams
{
    /// The token.
    pub token: ProgressToken,
}

/// The parameters of `$/progress`: where the work under a token is.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ProgressParams
{
    /// The token.
    pub token: ProgressToken,
    /// Where the work is.
    pub value: WorkDone,
}

/// What a piece of work the server reports progress on is, as a client shows
/// it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct WorkTitle(pub &'static str);

/// Where a piece of work is.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum WorkDone
{
    /// It started.
    Begin
    {
        /// What the work is.
        title: WorkTitle,
        /// Whether the client may cancel it: never, as the work runs to its end
        /// before the next message is read.
        cancellable: bool,
        /// What it works on.
        message: String,
    },
    /// It ended.
    End,
}

/// The text document client capabilities the server reads.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentCapabilities
{
    /// `textDocument.definition`.
    #[serde(default)]
    pub definition: Option<DefinitionCapabilities>,
    /// `textDocument.signatureHelp`.
    #[serde(default)]
    pub signature_help: Option<SignatureHelpCapabilities>,
    /// `textDocument.completion`.
    #[serde(default)]
    pub completion: Option<CompletionCapabilities>,
    /// `textDocument.foldingRange`.
    #[serde(default)]
    pub folding_range: Option<FoldingCapabilities>,
    /// `textDocument.inlayHint`.
    #[serde(default)]
    pub inlay_hint: Option<InlayHintCapabilities>,
    /// `textDocument.diagnostic`: present when it pulls a document's
    /// diagnostics.
    #[serde(default)]
    pub diagnostic: Option<DiagnosticCapabilities>,
}

/// What a client offers of pulling a document's diagnostics.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct DiagnosticCapabilities
{
    /// `dynamicRegistration`: whether it takes the pull by registration.
    #[serde(default)]
    pub dynamic_registration: Option<bool>,
}

/// What the client takes in answer to an inlay-hint request.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct InlayHintCapabilities
{
    /// `textDocument.inlayHint.resolveSupport`: whether the properties it
    /// resolves by a second request include the label's locations.
    #[serde(default)]
    pub resolve_support: Option<ResolvesHintLocations>,
}

/// What the client takes in answer to a folding-range request.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct FoldingCapabilities
{
    /// `textDocument.foldingRange.foldingRange`.
    #[serde(default)]
    pub folding_range: Option<FoldingRangeCapabilities>,
}

/// What the client takes of one folding range.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct FoldingRangeCapabilities
{
    /// `…foldingRange.collapsedText`: whether it shows a range's collapsed
    /// text.
    #[serde(default)]
    pub collapsed_text: Option<bool>,
}

/// What the client takes in answer to a completion request.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct CompletionCapabilities
{
    /// `textDocument.completion.completionItem`.
    #[serde(default)]
    pub completion_item: Option<CompletionItemCapabilities>,
}

/// What the client takes of one completion item.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct CompletionItemCapabilities
{
    /// `…completionItem.labelDetailsSupport`: whether it shows an item's
    /// label details.
    #[serde(default)]
    pub label_details_support: Option<bool>,
    /// `…completionItem.snippetSupport`: whether it takes an item's text as
    /// a snippet.
    #[serde(default)]
    pub snippet_support: Option<bool>,
}

/// What the client takes in answer to a signature-help request.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct SignatureHelpCapabilities
{
    /// `textDocument.signatureHelp.signatureInformation`.
    #[serde(default)]
    pub signature_information: Option<SignatureInformationCapabilities>,
}

/// What the client takes of one signature.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct SignatureInformationCapabilities
{
    /// `textDocument.signatureHelp.signatureInformation.parameterInformation`.
    #[serde(default)]
    pub parameter_information: Option<ParameterInformationCapabilities>,
}

/// What the client takes of one parameter.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct ParameterInformationCapabilities
{
    /// `…parameterInformation.labelOffsetSupport`: whether it takes a
    /// parameter as its place in the label.
    #[serde(default)]
    pub label_offset_support: Option<bool>,
}

/// What the client takes in answer to a definition request.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct DefinitionCapabilities
{
    /// `textDocument.definition.linkSupport`: whether it takes links.
    #[serde(default)]
    pub link_support: Option<bool>,
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
    /// `gandr.inlineCompletion`.
    #[serde(default, rename = "inlineCompletion")]
    pub inline_completion: Option<InlineCompletionSettings>,
}

/// The `gandr.inlineCompletion` settings.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct InlineCompletionSettings
{
    /// `gandr.inlineCompletion.trigger`: which requests the parser's ghost
    /// text answers.
    #[serde(default)]
    pub trigger: Option<TriggerSetting>,
}

/// A `gandr.inlineCompletion.trigger` value: which inline completion requests
/// are answered.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum TriggerSetting
{
    /// Only a request the author invoked, as VS Code's
    /// `editor.action.inlineSuggest.trigger` does; one the client makes as
    /// the author types is answered with no item.
    #[default]
    Invoked,
    /// Every request, invoked or made as the author types.
    Automatic,
}

/// The `gandr.presentation` settings.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct PresentationSettings
{
    /// `gandr.presentation.form`: whether a type is written with the sugar
    /// the surface reads or in the explicit formers.
    #[serde(default)]
    pub form: Option<FormSetting>,
    /// `gandr.presentation.spelling`: whether a construct with a glyph is
    /// written with it or in its ASCII spelling.
    #[serde(default)]
    pub spelling: Option<SpellingSetting>,
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

/// A `gandr.presentation.spelling` value, spelled as `gandr --spelling`
/// spells it.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum SpellingSetting
{
    /// [`Spelling::Unicode`].
    Unicode,
    /// [`Spelling::Ascii`].
    Ascii,
}

impl From<SpellingSetting> for Spelling
{
    /// The spelling `setting` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(setting: SpellingSetting) -> Self
    {
        match setting {
            SpellingSetting::Unicode => Self::Unicode,
            SpellingSetting::Ascii => Self::Ascii,
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

    /// The presentation spelling these settings name, when they name one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn spelling(self) -> Option<Spelling>
    {
        self.presentation
            .and_then(|presentation| presentation.spelling)
            .map(Spelling::from)
    }

    /// The inline completion trigger these settings name, when they name one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn trigger(self) -> Option<TriggerSetting>
    {
        self.inline_completion?.trigger
    }
}

/// The parameters of `textDocument/semanticTokens/range` and
/// `textDocument/inlayHint`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct RangeParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The range asked about.
    pub range: Range,
}

/// The parameters of `textDocument/codeAction`: the range asked about and the
/// diagnostics the client shows over it.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct CodeActionParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The range asked about.
    pub range: Range,
    /// What the client shows over the range.
    #[serde(default)]
    pub context: ActionContext,
}

/// What a client shows over the range a code action is asked for.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct ActionContext
{
    /// The diagnostics over the range, each as the client sent it.
    #[serde(default)]
    pub diagnostics: Vec<Value>,
}

/// The parameters of `textDocument/rangesFormatting`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct RangesParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The ranges to format.
    pub ranges: Vec<Range>,
}

/// The parameters of a request about one position of a document:
/// `textDocument/hover`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct PositionParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The cursor the request is about.
    pub position: Position,
}

/// The parameters of `textDocument/inlineCompletion`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct InlineParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The cursor the request is about.
    pub position: Position,
    /// Why the client asked, read as invoked when absent.
    #[serde(default)]
    pub context: Option<InlineContext>,
}

/// `InlineCompletionContext`, of which the server reads why the request was
/// made.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct InlineContext
{
    /// `triggerKind`.
    pub trigger_kind: InlineTriggerKind,
}

/// `InlineCompletionTriggerKind`, as the protocol numbers it: `1` when the
/// author asked, by a command or a key, and `2` when the client asked as the
/// author typed.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(transparent)]
#[repr(transparent)]
pub struct InlineTriggerKind(u8);

impl InlineTriggerKind
{
    /// The client asked as the author typed.
    pub const AUTOMATIC: Self = Self(2);
}

/// The parameters of `textDocument/onTypeFormatting`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct TypedParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// Where the character was typed: just after it.
    pub position: Position,
    /// The character typed.
    pub ch: String,
}

/// The parameters of `textDocument/semanticTokens/full/delta`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DeltaParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The id of the full answer the client holds.
    pub previous_result_id: ResultId,
}

/// The parameters of `textDocument/diagnostic`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The id of the report the client holds, when it holds one.
    #[serde(default)]
    pub previous_result_id: Option<ResultId>,
}

/// The parameters of `textDocument/references`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The cursor the request is about.
    pub position: Position,
    /// What the answer holds besides the uses.
    #[serde(default)]
    pub context: ReferenceContext,
}

/// What a reference request's answer holds besides the uses.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceContext
{
    /// Whether the declaring name is answered too.
    pub include_declaration: bool,
}

/// The parameters of `textDocument/rename`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct RenameParams
{
    /// The document addressed.
    pub text_document: DocumentIdentifier,
    /// The cursor on the name renamed.
    pub position: Position,
    /// The name it is renamed to.
    pub new_name: String,
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
    ///   [`TOKEN_TYPES`] and [`TOKEN_MODIFIERS`]; completion, each item
    ///   resolved by a second request, and inline completion; document symbols,
    ///   folding ranges and selection ranges; inlay hints, each label's
    ///   locations resolved by a second request when the client asks; hover;
    ///   signature help, asked for as a call's `(` or a `,` is typed and again
    ///   at a `)`; definition and type definition; formatting over the whole
    ///   document and over a range; code lenses, code actions, document links
    ///   and workspace symbols, each whole in its answer and resolved by a
    ///   second request as it came; linked editing; workspace folders, with a
    ///   notification as they change; the creation, deletion and renaming of
    ///   gandr sources and folders on disk, each heard of once done, and a
    ///   rename asked about before it is done; the server named `gandr` at this
    ///   crate's version.
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
            && ret.capabilities.semantic_tokens_provider.full.delta
            && ret.capabilities.semantic_tokens_provider.range
            && ret.capabilities.inline_completion_provider.0
            && ret.capabilities.document_symbol_provider.0
            && ret.capabilities.folding_range_provider.0
            && ret.capabilities.inlay_hint_provider.resolve_provider
            && ret.capabilities.selection_range_provider.0
            && ret.capabilities.hover_provider.0
            && matches!(ret.capabilities.signature_help_provider.trigger_characters,
                [open, comma] if matches!(open.as_bytes(), b"(") && matches!(comma.as_bytes(), b","))
            && ret.capabilities.definition_provider.0
            && ret.capabilities.declaration_provider.0
            && ret.capabilities.type_definition_provider.0
            && ret.capabilities.document_formatting_provider.0
            && ret.capabilities.document_range_formatting_provider.ranges_support
            && matches!(ret.capabilities.document_on_type_formatting_provider.first_trigger_character.as_bytes(), b";")
            && ret.capabilities.code_action_provider.resolve_provider
            && matches!(ret.capabilities.execute_command_provider.commands,
                [command] if matches!(command.as_bytes(), b"gandr.applyFill"))
            && ret.capabilities.workspace_symbol_provider.resolve_provider
            && ret.capabilities.document_highlight_provider.0
            && ret.capabilities.references_provider.0
            && ret.capabilities.rename_provider.prepare_provider
            && ret.capabilities.document_link_provider.resolve_provider
            && ret.capabilities.workspace.workspace_folders.supported
            && ret.capabilities.workspace.workspace_folders.change_notifications
            && matches!(ret.capabilities.workspace.file_operations.will_rename.filters,
                [ref file, ref folder] if matches!(file.pattern.glob.as_bytes(), b"**/*.gandr")
                    && matches!(folder.pattern.matches.as_bytes(), b"folder"))
            && matches!(ret.capabilities.workspace.text_document_content.schemes,
                [scheme] if matches!(scheme.as_bytes(), b"gandr-tree"))
            && ret.capabilities.linked_editing_range_provider.0
            && ret.capabilities.call_hierarchy_provider.0
            && ret.capabilities.code_lens_provider.resolve_provider
            && ret.capabilities.completion_provider.resolve_provider
            && ret.capabilities.completion_provider.completion_item.label_details_support
            && matches!(ret.capabilities.diagnostic_provider.identifier.as_bytes(), b"gandr")
            && ret.capabilities.diagnostic_provider.inter_file_dependencies
            && !ret.capabilities.diagnostic_provider.workspace_diagnostics)]
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
                    full: FullOptions { delta: true },
                    range: true,
                },
                completion_provider: CompletionOptions {
                    resolve_provider: true,
                    completion_item: CompletionItemOptions {
                        label_details_support: true,
                    },
                },
                inline_completion_provider: Provider::ANSWERED,
                document_symbol_provider: Provider::ANSWERED,
                folding_range_provider: Provider::ANSWERED,
                inlay_hint_provider: ResolveOptions {
                    resolve_provider: true,
                },
                selection_range_provider: Provider::ANSWERED,
                hover_provider: Provider::ANSWERED,
                signature_help_provider: SignatureHelpOptions {
                    trigger_characters: SIGNATURE_TRIGGERS,
                    retrigger_characters: [")"],
                },
                definition_provider: Provider::ANSWERED,
                declaration_provider: Provider::ANSWERED,
                type_definition_provider: Provider::ANSWERED,
                document_formatting_provider: Provider::ANSWERED,
                document_range_formatting_provider: RangeFormattingOptions {
                    ranges_support: true,
                },
                document_on_type_formatting_provider: OnTypeFormattingOptions {
                    first_trigger_character: FORM_CLOSER,
                },
                code_lens_provider: ResolveOptions {
                    resolve_provider: true,
                },
                code_action_provider: ResolveOptions {
                    resolve_provider: true,
                },
                execute_command_provider: CommandOptions { commands: COMMANDS },
                workspace_symbol_provider: ResolveOptions {
                    resolve_provider: true,
                },
                document_highlight_provider: Provider::ANSWERED,
                references_provider: Provider::ANSWERED,
                rename_provider: RenameOptions {
                    prepare_provider: true,
                },
                document_link_provider: ResolveOptions {
                    resolve_provider: true,
                },
                linked_editing_range_provider: Provider::ANSWERED,
                call_hierarchy_provider: Provider::ANSWERED,
                diagnostic_provider: DiagnosticOptions {
                    identifier: SOURCE,
                    inter_file_dependencies: true,
                    workspace_diagnostics: false,
                },
                workspace: WorkspaceOptions {
                    workspace_folders: FoldersOptions {
                        supported: true,
                        change_notifications: true,
                    },
                    file_operations: FileOperationsOptions {
                        did_create: OperationFilters::SOURCES,
                        did_rename: OperationFilters::SOURCES,
                        did_delete: OperationFilters::SOURCES,
                        will_rename: OperationFilters::SOURCES,
                    },
                    text_document_content: ContentOptions {
                        schemes: [TREE_SCHEME],
                    },
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
    /// Completion is answered, each item with its label details, and resolved
    /// by a second request.
    pub completion_provider: CompletionOptions,
    /// Inline completion is answered.
    pub inline_completion_provider: Provider,
    /// Document symbols are answered.
    pub document_symbol_provider: Provider,
    /// Folding ranges are answered.
    pub folding_range_provider: Provider,
    /// Inlay hints are answered, the declarations a label names located now
    /// or by a second request.
    pub inlay_hint_provider: ResolveOptions,
    /// Selection ranges are answered.
    pub selection_range_provider: Provider,
    /// Hovers are answered.
    pub hover_provider: Provider,
    /// Signature help is answered, asked for by the characters that open and
    /// separate a call's arguments.
    pub signature_help_provider: SignatureHelpOptions,
    /// Definitions are answered: where what a written name refers to is
    /// written.
    pub definition_provider: Provider,
    /// Declarations are answered: where what a written name refers to is
    /// declared, its signature for a name declared in two halves.
    pub declaration_provider: Provider,
    /// Type definitions are answered: where the families a node's type names
    /// are declared.
    pub type_definition_provider: Provider,
    /// Formatting the whole document is answered.
    pub document_formatting_provider: Provider,
    /// Formatting a range is answered, and several ranges at once.
    pub document_range_formatting_provider: RangeFormattingOptions,
    /// Typing the `;` that closes a top-level form lays that form out.
    pub document_on_type_formatting_provider: OnTypeFormattingOptions,
    /// Code lenses are answered, each whole, and resolved as it came.
    pub code_lens_provider: ResolveOptions,
    /// Code actions are answered, each with its edit, and resolved as it
    /// came.
    pub code_action_provider: ResolveOptions,
    /// The commands the server runs when a client executes one: each a code
    /// lens may name.
    pub execute_command_provider: CommandOptions,
    /// Workspace symbols are answered: the names the open documents' import
    /// closures and the sources under the opened folders declare, each with
    /// its location, and resolved as it came.
    pub workspace_symbol_provider: ResolveOptions,
    /// Document highlights are answered: the declaring name and the uses of
    /// the name at a position, within the document.
    pub document_highlight_provider: Provider,
    /// References are answered: the uses the open documents make of the name
    /// at a position, and its declaring name when asked.
    pub references_provider: Provider,
    /// Renaming is answered, a rename prepared first: the name at a position,
    /// its declaring name and its uses in every source importing it.
    pub rename_provider: RenameOptions,
    /// Document links are answered, each with its target, and resolved as it
    /// came: every path import's address, linked to the file it names.
    pub document_link_provider: ResolveOptions,
    /// Linked editing is answered: a binder local to a declaration and its
    /// uses, an edit of one applying to all.
    pub linked_editing_range_provider: Provider,
    /// The call hierarchy is answered: the declared values a definition
    /// uses, and those whose definitions use it.
    pub call_hierarchy_provider: Provider,
    /// A document's diagnostics are answered when its client pulls them:
    /// what its copy last published, named by their digest.
    pub diagnostic_provider: DiagnosticOptions,
    /// The workspace features answered.
    pub workspace: WorkspaceOptions,
}

/// The diagnostic provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticOptions
{
    /// The name the client keeps the pulled diagnostics under.
    pub identifier: &'static str,
    /// Whether a document's diagnostics change when another document does:
    /// they do, a copy being judged with its import closure.
    pub inter_file_dependencies: bool,
    /// Whether `workspace/diagnostic` is answered: it is not, a source no
    /// editor holds being checked by no one.
    pub workspace_diagnostics: bool,
}

/// The range-formatting provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct RangeFormattingOptions
{
    /// Several ranges are formatted by one request.
    pub ranges_support: bool,
}

/// The rename provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct RenameOptions
{
    /// A rename is prepared before it is asked for.
    pub prepare_provider: bool,
}

/// A provider whose answers a second request resolves, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct ResolveOptions
{
    /// Whether an answer is resolved by a second request.
    pub resolve_provider: bool,
}

/// The completion provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CompletionOptions
{
    /// Whether an item is resolved by a second request.
    pub resolve_provider: bool,
    /// What the items carry.
    pub completion_item: CompletionItemOptions,
}

/// What the completion items carry, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct CompletionItemOptions
{
    /// Whether an item carries label details to a client that shows them.
    pub label_details_support: bool,
}

/// The commands the server runs, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct CommandOptions
{
    /// Their names.
    pub commands: [&'static str; 1],
}

/// The command applying the one checked fill a model proposed for a range:
/// its arguments are the document's URI and the range. The server runs it,
/// asking the client to apply the fill's edit.
pub const APPLY_FILL: &str = "gandr.applyFill";

/// The command a references lens names: its arguments are the document's
/// URI, the name's position and the locations of its uses. The client runs
/// it, showing those uses; the server runs nothing for it.
pub const SHOW_REFERENCES: &str = "gandr.showReferences";

/// Every command the server runs.
pub const COMMANDS: [&str; 1] = [APPLY_FILL];

/// The parameters of `workspace/executeCommand`: the command and what it is
/// run on.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct ExecuteCommandParams
{
    /// The command's name.
    pub command: String,
    /// Its arguments, in order.
    #[serde(default)]
    pub arguments: Vec<Value>,
}

/// The parameters of `workspace/applyEdit`: the edit the client is asked to
/// apply, and the label its undo stack shows.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ApplyEditParams
{
    /// What the edit does, as the client shows it.
    pub label: &'static str,
    /// The edit.
    pub edit: WorkspaceEdit,
}

/// A client's answer to `workspace/applyEdit`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct AppliedEdit
{
    /// Whether the edit was applied.
    pub applied: bool,
    /// Why it was not, when the client says.
    #[serde(default)]
    pub failure_reason: Option<String>,
}

/// The parameters of `window/showDocument`: the document the client is
/// asked to show, focused, with a range selected.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ShowDocumentParams
{
    /// The document.
    pub uri: DocumentUri,
    /// Whether the editor showing it takes the focus.
    pub take_focus: bool,
    /// The range selected in it.
    pub selection: Range,
}

/// The parameters of `workspace/textDocumentContent` and of its refresh: the
/// virtual document whose text is asked for, or asked for again.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct ContentParams
{
    /// The virtual document.
    pub uri: DocumentUri,
}

/// What `workspace/textDocumentContent` answers: the virtual document's text.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct ContentResult
{
    /// The text.
    pub text: String,
}

/// An item a second request resolves as it came: what the first answered
/// whole.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unresolved
{
    /// A code action, its edit carried by the listing.
    Action,
    /// A document link, its target carried by the listing.
    Link,
    /// A workspace symbol, its location carried by the listing.
    Symbol,
}

impl Unresolved
{
    /// Whether `item` holds what the protocol requires of this kind of item:
    /// a code action's title, a document link's range, a workspace symbol's
    /// name and location.
    ///
    /// # Specification
    /// - requires: nothing; any value is admissible input.
    /// - ensures: `Ok` exactly when `item` is an object holding each field the
    ///   kind requires, a title and a name as strings and a range as a range.
    /// - fails: the first field missing or of another shape.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind's item as listed reads; one without its
    ///   required field, and one of another kind, are refused.
    /// - witness: `protocol::tests::a_resolved_item_needs_what_its_kind_requires`
    #[spec(ensures: |ret| ret.is_err() || item.is_object())]
    pub fn read(
        self,
        item: &Value,
    ) -> Result<(), serde_json::Error>
    {
        let field = |name: &'static str| {
            item.get(name)
                .ok_or_else(|| <serde_json::Error as serde::de::Error>::missing_field(name))
        };
        match self {
            Self::Action => String::deserialize(field("title")?).map(drop),
            Self::Link => Range::deserialize(field("range")?).map(drop),
            Self::Symbol => {
                String::deserialize(field("name")?)?;
                field("location").map(drop)
            },
        }
    }
}

/// The workspace features, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkspaceOptions
{
    /// The folders the client opens.
    pub workspace_folders: FoldersOptions,
    /// The file operations the server hears of.
    pub file_operations: FileOperationsOptions,
    /// The schemes of the virtual documents whose text the server serves.
    pub text_document_content: ContentOptions,
}

/// The virtual documents whose text the server serves, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct ContentOptions
{
    /// The schemes: the syntax tree view's.
    pub schemes: [&'static str; 1],
}

/// Workspace folders, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FoldersOptions
{
    /// The folders a client opened are read at `initialize`.
    pub supported: bool,
    /// The client tells the server as it opens and closes folders.
    pub change_notifications: bool,
}

/// The file operations the server hears of, as advertised: a creation, a
/// deletion and a rename once done, and a rename before it is done, each of
/// the files and folders its filters match.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FileOperationsOptions
{
    /// Creations, once done.
    pub did_create: OperationFilters,
    /// Renames, once done.
    pub did_rename: OperationFilters,
    /// Deletions, once done.
    pub did_delete: OperationFilters,
    /// Renames, before they are done.
    pub will_rename: OperationFilters,
}

/// The files and folders one file operation is heard of for.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct OperationFilters
{
    /// The filters, any of which matching admits a file or folder.
    pub filters: [OperationFilter; 2],
}

impl OperationFilters
{
    /// Every gandr source on disk, and every folder on disk, which may hold
    /// some.
    pub const SOURCES: Self = Self {
        filters: [
            OperationFilter {
                scheme: "file",
                pattern: OperationPattern {
                    glob: "**/*.gandr",
                    matches: "file",
                },
            },
            OperationFilter {
                scheme: "file",
                pattern: OperationPattern {
                    glob: "**",
                    matches: "folder",
                },
            },
        ],
    };
}

/// One filter of a file operation: the URI scheme and the pattern a file or
/// folder matches.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct OperationFilter
{
    /// The URI scheme.
    pub scheme: &'static str,
    /// The pattern.
    pub pattern: OperationPattern,
}

/// A file operation's pattern: a glob, and whether it matches files or
/// folders.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct OperationPattern
{
    /// The glob.
    pub glob: &'static str,
    /// `file` or `folder`.
    pub matches: &'static str,
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
    /// Tokens over the whole document are answered, and as edits of the last
    /// full answer.
    pub full: FullOptions,
    /// Tokens over a range are answered.
    pub range: bool,
}

/// The whole-document semantic tokens, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct FullOptions
{
    /// A delta request is answered.
    pub delta: bool,
}

/// The token legend.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Legend
{
    /// The token types, in the order a token's type integer indexes.
    pub token_types: [&'static str; 15],
    /// The token modifiers, in the order a token's modifier bits index.
    pub token_modifiers: [&'static str; 4],
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
    /// What a semantic-tokens delta request answers for an open document
    /// whose last full answer the client names.
    Deltas(SemanticTokensDelta),
    /// What a completion request answers at a position of an open document.
    Completions(CompletionList),
    /// What a completion-item resolution answers: the item, with a declared
    /// name's head and documentation; boxed, one item outweighing a list's
    /// handle.
    Resolved(Box<CompletionItem>),
    /// What a code action's, code lens's, document link's or workspace
    /// symbol's resolution answers: the item as it came, every field the
    /// client sent kept.
    Unchanged(Value),
    /// What a signature-help request answers at a position of an open
    /// document: the declared head of the call the position stands in.
    Signatures(SignatureHelp),
    /// What an inline-completion request answers for an open document.
    Inline(InlineCompletionList),
    /// What a document-symbol request answers for an open document.
    Symbols(DocumentSymbols),
    /// What a folding-range request answers for an open document.
    Folds(Vec<FoldingRange>),
    /// What an inlay-hint request answers for an open document: the hints
    /// over the range asked about, in document order.
    Hints(Vec<InlayHint>),
    /// What `inlayHint/resolve` answers: the hint with every name its label
    /// writes located.
    Hint(InlayHint),
    /// What `gandr/copiedSources` answers for an open document: the sources
    /// declaring what the copied ranges name, ascending.
    Sources(Vec<DocumentUri>),
    /// What a selection-range request answers for an open document: one per
    /// position asked about, in order.
    Selections(Vec<SelectionRange>),
    /// What a hover request answers over a declaration's name.
    Hover(Hover),
    /// What a definition or type-definition request answers to a client that
    /// takes links.
    Links(Vec<LocationLink>),
    /// What a definition or type-definition request answers to a client that
    /// takes none.
    Locations(Vec<Location>),
    /// What a formatting request answers for an open document: the edits that
    /// lay it out, in document order.
    Edits(Vec<TextEdit>),
    /// What a code-lens request answers for an open document.
    Lenses(Vec<CodeLens>),
    /// What a code-lens resolution answers for a references lens: the lens
    /// with its count and the command showing its uses.
    Lens(CodeLens),
    /// What a code-action request answers over a range of an open document.
    Actions(Vec<CodeAction>),
    /// What a workspace-symbol request answers: the names found, each where
    /// its name is written.
    Found(Vec<SymbolInformation>),
    /// What a document-highlight request answers: the name at the position,
    /// where it is declared and every use of it in the document.
    Highlights(Vec<DocumentHighlight>),
    /// What a prepare-rename request answers: the name a rename at the
    /// position renames.
    Renaming(PrepareRename),
    /// What a rename request answers: the edits renaming the name everywhere
    /// it is written.
    Renamed(WorkspaceEdit),
    /// What a document-link request answers for an open document: each path
    /// import's address, in source order.
    Imports(Vec<DocumentLink>),
    /// What a linked-editing request answers: the ranges an edit of one
    /// applies to.
    Mirrored(LinkedEditingRanges),
    /// What a call-hierarchy preparation answers: the declared value the
    /// name at the position names.
    Callables(Vec<CallHierarchyItem>),
    /// What an incoming-calls request answers: each declared value whose
    /// definition uses the item, with the uses.
    Callers(Vec<IncomingCall>),
    /// What an outgoing-calls request answers: each declared value the
    /// item's definition uses, with the uses.
    Callees(Vec<OutgoingCall>),
    /// What a text-document-content request answers for a virtual document
    /// that views an open one: its printed syntax tree.
    Content(ContentResult),
    /// What a pull of an open document's diagnostics answers: what its copy
    /// last published, or that the client already holds it.
    Diagnosed(DiagnosticReport),
    /// `null`: what `shutdown` answers, a request about a document that is not
    /// open, and a hover over nothing the server knows.
    Nothing,
}

/// A link from the name a request was made at to where what it names is
/// written.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LocationLink
{
    /// The name the request was made at.
    pub origin_selection_range: Range,
    /// The document the target is written in.
    pub target_uri: DocumentUri,
    /// The whole target: a binder, or its declaring form.
    pub target_range: Range,
    /// The target's name, inside the whole target.
    pub target_selection_range: Range,
}

/// A declared value a call hierarchy shows: a declaration the lowering
/// admits as a value, which a use may call.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CallHierarchyItem
{
    /// The declared name.
    pub name: String,
    /// What it declares: a function.
    pub kind: SymbolKind,
    /// The document it is written in.
    pub uri: DocumentUri,
    /// Its definition's whole form.
    pub range: Range,
    /// Its name in its definition.
    pub selection_range: Range,
}

/// The parameters of `callHierarchy/incomingCalls` and
/// `callHierarchy/outgoingCalls`: the item a preparation answered.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct CallsParams
{
    /// The item asked about.
    pub item: CallHierarchyItem,
}

/// A declared value whose definition uses the item asked about.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct IncomingCall
{
    /// The declared value calling.
    pub from: CallHierarchyItem,
    /// Each use of the item in its definition, in document order.
    pub from_ranges: Vec<Range>,
}

/// A declared value the item asked about uses in its definition.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OutgoingCall
{
    /// The declared value called.
    pub to: CallHierarchyItem,
    /// Each use of it in the item's definition, in document order.
    pub from_ranges: Vec<Range>,
}

/// The ranges of a document that an edit of one applies to, each spelling
/// the same name, and the words an edit may leave there.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LinkedEditingRanges
{
    /// The ranges: a binder's name, then its uses.
    pub ranges: Vec<Range>,
    /// The words a name is written as, the parser's
    /// [`gandr_surface_parser::WORD_PATTERN`]: an edit that leaves a range
    /// outside it ends the linked edit.
    pub word_pattern: &'static str,
}

/// A range of a document that names another file: a path import's address.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DocumentLink
{
    /// The address, between its quotes.
    pub range: Range,
    /// The file it names.
    pub target: DocumentUri,
    /// The path of that file, as the dispatcher reads it, shown where the
    /// link is hovered.
    pub tooltip: String,
}

/// The result of a semantic-tokens request.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticTokens
{
    /// The id a delta request names this answer by: present on a full
    /// answer, absent on a range answer.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result_id: Option<ResultId>,
    /// The token stream, five integers per token.
    pub data: TokenStream,
}

/// The result of a semantic-tokens delta request: the edits turning the
/// stream the client holds into the current one.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticTokensDelta
{
    /// The id a later delta request names the current stream by.
    pub result_id: ResultId,
    /// The edits, at most one.
    pub edits: Vec<TokensEdit>,
}

/// The result of a completion request: every name and keyword the word at the
/// cursor may complete to, best first.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CompletionList
{
    /// Whether typing further may offer what this list does not: never, the
    /// list holding every item the word's prefix admits.
    pub is_incomplete: bool,
    /// The items, in the order [`CompletionItem::sort_text`] keeps.
    pub items: Vec<CompletionItem>,
}

/// One completion: the name or keyword offered, what it is, the edit that
/// writes it over the word at the cursor, what it is typed or declared as, and,
/// for a declared name, the document it was offered in, where a resolution
/// reads its documentation.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CompletionItem
{
    /// The name or keyword.
    pub label: String,
    /// What it is, as the protocol numbers completion kinds.
    pub kind: CompletionItemKind,
    /// Where it stands among the list's items, as text the client sorts by.
    pub sort_text: String,
    /// The edit writing it over the word at the cursor.
    pub text_edit: TextEdit,
    /// How the edit's text reads: a snippet for a keyword written as its
    /// form; none when it is the plain text.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub insert_text_format: Option<InsertTextFormat>,
    /// The text the client filters the item by when its edit writes more
    /// than the label: the keyword of a form written as a snippet.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub filter_text: Option<String>,
    /// What a declared name's head writes, or a binder's name and type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// The same, beside the label, to a client that shows label details.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label_details: Option<LabelDetails>,
    /// The documentation written for a declared name, once resolved.
    #[serde(skip_deserializing, skip_serializing_if = "Option::is_none")]
    pub documentation: Option<MarkupContent>,
    /// Where a declared name was offered; none for a binder or a keyword,
    /// which resolve to themselves, and for a name its document does not
    /// import yet.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub data: Option<CompletionData>,
    /// The edit importing the source that declares a name its document does
    /// not import yet, made beside the item's own when it is chosen.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub additional_text_edits: Option<Vec<TextEdit>>,
}

/// What a client shows beside a completion's label: the rest of its head,
/// right after the label, or what it is, apart from it.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct LabelDetails
{
    /// The head after the name: its parameters and result, or ` : ` and its
    /// type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// A head that does not start with the name, whole.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
}

/// Where a declared name was offered: the document whose names it was read
/// from.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct CompletionData
{
    /// The document.
    pub uri: DocumentUri,
}

/// What a completion item is, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct CompletionItemKind(u8);

impl CompletionItemKind
{
    /// A data family's constructor.
    pub const CONSTRUCTOR: Self = Self(4);
    /// A data family.
    pub const ENUM: Self = Self(13);
    /// A declaration written as a value.
    pub const FUNCTION: Self = Self(3);
    /// A keyword opening a form.
    pub const KEYWORD: Self = Self(14);
    /// A binder in scope.
    pub const VARIABLE: Self = Self(6);
}

/// How a completion's text reads, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct InsertTextFormat(u8);

impl InsertTextFormat
{
    /// A snippet: `$1` and `${1:name}` are tab stops, `$`, `}` and `\`
    /// escaped.
    pub const SNIPPET: Self = Self(2);
}

/// The character whose typing closes a top-level form: what on-type
/// formatting answers.
pub const FORM_CLOSER: &str = ";";

/// The on-type-formatting provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
#[repr(transparent)]
pub struct OnTypeFormattingOptions
{
    /// The character that asks for formatting as it is typed.
    pub first_trigger_character: &'static str,
}

/// The characters that ask for signature help as they are typed: the `(` that
/// opens a call's arguments and the `,` between them.
pub const SIGNATURE_TRIGGERS: [&str; 2] = ["(", ","];

/// The signature-help provider, as advertised.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureHelpOptions
{
    /// The characters that ask for help as they are typed.
    pub trigger_characters: [&'static str; 2],
    /// The characters that ask again while help is shown: the `)` that may
    /// leave the call.
    pub retrigger_characters: [&'static str; 1],
}

/// The result of a signature-help request: the one head the call's name
/// refers to, and the argument the position writes.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureHelp
{
    /// The signatures, one.
    pub signatures: Vec<SignatureInformation>,
    /// The signature shown: the first.
    pub active_signature: u32,
    /// The parameter the position writes; `null` past the last parameter.
    pub active_parameter: Option<u32>,
}

/// One signature: its label, its documentation and its parameters.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SignatureInformation
{
    /// The declared head, on one line.
    pub label: String,
    /// The documentation written for the declaration, when it has any.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub documentation: Option<MarkupContent>,
    /// The parameters, in written order.
    pub parameters: Vec<ParameterInformation>,
}

/// One parameter of a signature.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ParameterInformation
{
    /// Where it stands in the signature's label.
    pub label: ParameterLabel,
    /// The documentation written before the parameter, when it has any.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub documentation: Option<MarkupContent>,
}

/// Where a parameter stands in its signature's label.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(untagged)]
pub enum ParameterLabel
{
    /// Its text, for a client that takes no offsets.
    Text(String),
    /// Its start and end in the label, in UTF-16 code units.
    Offsets([u32; 2]),
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
    /// What the declaration writes after its name before its body or
    /// definition — a function's parameters and result, a declared type — its
    /// layout collapsed; none when it writes nothing there.
    pub detail: Option<String>,
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
            if let Some(ref detail) = symbol.detail {
                let _detail = object.insert("detail".to_owned(), Value::String(detail.clone()));
            }
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
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct SymbolKind(u8);

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
    /// A family's constructor.
    pub const CONSTRUCTOR: Self = Self(9);
    /// A theory's operation.
    pub const METHOD: Self = Self(6);
    /// A theory's law.
    pub const PROPERTY: Self = Self(7);
    /// An observation: of a codata declaration, or a theory's.
    pub const FIELD: Self = Self(8);
    /// A theory's sort, shape or extension: a type the theory is over.
    pub const TYPE_PARAMETER: Self = Self(26);
    /// A world: a place a term is judged at.
    pub const CONSTANT: Self = Self(14);
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
    /// What a client shows in place of the folded lines: the first line's
    /// text before the range, then what the form writes before its body, the
    /// body elided; absent for a comment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub collapsed_text: Option<String>,
}

impl FoldingRange
{
    /// This range as answered to a client that `collapsed` says shows a
    /// fold's text or not: the same lines and kind, the text kept only when
    /// it does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn answered(
        &self,
        collapsed: FoldsCollapsed,
    ) -> Self
    {
        Self {
            start_line: self.start_line,
            end_line: self.end_line,
            kind: self.kind,
            collapsed_text: collapsed.0.then(|| self.collapsed_text.clone()).flatten(),
        }
    }
}

/// A label a client draws between the characters of a line without writing
/// it to the document.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InlayHint
{
    /// Where the label is drawn: before the character at this position.
    pub position: Position,
    /// The text drawn, whole or in parts.
    pub label: HintLabel,
    /// What the label says.
    pub kind: InlayHintKind,
    /// The document a resolution reads the label's locations from; none for
    /// a label naming no declaration, or one listed with its locations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<HintData>,
}

/// What an inlay hint draws: its text whole, or in parts each a declaration
/// name may link from.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(untagged)]
pub enum HintLabel
{
    /// The text, naming no declaration.
    Text(String),
    /// The text in parts, in the order drawn.
    Parts(Vec<HintLabelPart>),
}

/// One part of an inlay hint's label: text, and the declaration it names.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct HintLabelPart
{
    /// The text of the part.
    pub value: String,
    /// Where the name the part writes is declared; none for text between
    /// names, and for a name until the hint is resolved.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<Location>,
}

/// The document whose hint a resolution reads again.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[repr(transparent)]
pub struct HintData
{
    /// The document the hint is drawn in.
    pub uri: DocumentUri,
}

/// An inlay hint a client asks to resolve: where it is drawn, and the
/// document when its label names a declaration.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct HintResolution
{
    /// Where the label is drawn.
    pub position: Position,
    /// The document; none for a hint listed whole.
    #[serde(default)]
    pub data: Option<HintData>,
}

impl fmt::Display for HintLabel
{
    /// The text drawn: the whole text, or the parts' values in order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every hint's label over two corpus sources, each
    ///   asserted at its exact text.
    /// - witness: `inlay::tests::each_binder_that_writes_no_type_is_hinted`
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Text(ref text) => f.write_str(text),
            Self::Parts(ref parts) => parts.iter().try_for_each(|part| f.write_str(&part.value)),
        }
    }
}

/// `InlayHintKind`, as the protocol numbers it.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
#[repr(transparent)]
pub struct InlayHintKind(u8);

impl InlayHintKind
{
    /// The label is a type.
    pub const TYPE: Self = Self(1);
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
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextEdit
{
    /// The range replaced.
    pub range: Range,
    /// The text replacing it.
    pub new_text: String,
}

/// A command a lens or an action names: its title, the command it runs,
/// empty for one that runs nothing, and the command's arguments.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Command
{
    /// The text shown.
    pub title: String,
    /// The command run when it is chosen.
    #[serde(rename = "command")]
    pub name: &'static str,
    /// What it is run on, in order; none is written when there is none.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<Value>,
}

/// A code lens: a command shown above a range, or the position a resolution
/// fills its command from.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CodeLens
{
    /// The range the lens is about.
    pub range: Range,
    /// What it shows; none until the lens is resolved.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub command: Option<Command>,
    /// The name a resolution counts the references of.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<LensData>,
}

/// The name a references lens counts: where it is written.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LensData
{
    /// The document writing it.
    pub uri: DocumentUri,
    /// Where in that document.
    pub position: Position,
}

/// A code lens a client asks to resolve: its range, and the name it counts
/// when it is a references lens.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct LensResolution
{
    /// The range the lens is about.
    pub range: Range,
    /// The name it counts; none for a lens listed with its command.
    #[serde(default)]
    pub data: Option<LensData>,
}

/// A code action: an edit the client offers to apply, with the diagnostics it
/// answers.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CodeAction
{
    /// The text shown.
    pub title: String,
    /// Its kind, `quickfix`.
    pub kind: &'static str,
    /// The diagnostics it answers, each as the client sent it.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<Value>,
    /// Whether it is the fix the client applies when its user asks for the
    /// preferred one.
    #[serde(skip_serializing_if = "core::ops::Not::not")]
    pub is_preferred: bool,
    /// The edit it applies.
    pub edit: WorkspaceEdit,
}

/// Edits to several documents: by URI, or, for a client that takes them so,
/// as each document's edits with the version of its copy they were made
/// against and the annotations they name.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkspaceEdit
{
    /// Each document's edits, in document order, by URI; none once versioned.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub changes: Option<BTreeMap<DocumentUri, Vec<TextEdit>>>,
    /// Each document's edits with the version they were made against, in URI
    /// order.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub document_changes: Vec<TextDocumentEdit>,
    /// The annotations the edits name, by identifier.
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub change_annotations: BTreeMap<&'static str, ChangeAnnotation>,
}

impl WorkspaceEdit
{
    /// Edits by URI, as every client takes them.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn of(changes: BTreeMap<DocumentUri, Vec<TextEdit>>) -> Self
    {
        Self {
            changes: Some(changes),
            document_changes: Vec::new(),
            change_annotations: BTreeMap::new(),
        }
    }

    /// These edits as a client taking edits as `shaped` reads them, where
    /// `held` is the version of the client's copy of a document, none when it
    /// holds none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: unchanged unless `shaped.versioned` and the edits are by URI;
    ///   then the same edits as one document change per document, in URI order,
    ///   each naming the version `held` gives it, and none by URI. When
    ///   `shaped.annotated`, each edit to a document `held` gives no version
    ///   names [`UNHELD`], whose annotation asks the user to confirm, described
    ///   once when any edit names it.
    /// - provides: a rename's, a file move's, a quick fix's and an applied
    ///   fill's edit, as the client asking takes it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rename across a document the client holds and an
    ///   importer it does not is answered by URI to a client that declares
    ///   nothing, versioned to one that declares document changes, and
    ///   annotated as well to one that also declares annotations.
    /// - witness: `server::tests::a_rename_is_versioned_and_annotated_as_its_client_takes_edits`
    #[spec(ensures: |ret| (!shaped.versioned || ret.changes.is_none())
        && (shaped.annotated || ret.change_annotations.is_empty()))]
    #[must_use]
    pub fn shaped<Held>(
        mut self,
        shaped: EditsShaped,
        held: Held,
    ) -> Self
    where
        Held: Fn(&DocumentUri) -> Option<DocumentVersion>,
    {
        let Some(changes) = self.changes.take_if(|_| shaped.versioned)
        else {
            return self;
        };
        for (uri, edits) in changes {
            let version = held(&uri);
            let annotation = (shaped.annotated && version.is_none()).then_some(UNHELD);
            if annotation.is_some() {
                self.change_annotations
                    .insert(UNHELD, ChangeAnnotation::UNHELD);
            }
            self.document_changes.push(TextDocumentEdit {
                text_document: EditedDocument { uri, version },
                edits: edits
                    .into_iter()
                    .map(|edit| {
                        DocumentEdit::Text(AnnotatedEdit {
                            range: edit.range,
                            new_text: edit.new_text,
                            annotation_id: annotation,
                        })
                    })
                    .collect(),
            });
        }
        self
    }
}

/// The annotation an edit to a document the client holds no copy of names.
pub const UNHELD: &str = "unheld";

/// One document's edits, with the version of the copy they were made against.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentEdit
{
    /// The document and its version.
    pub text_document: EditedDocument,
    /// Its edits, in document order.
    pub edits: Vec<DocumentEdit>,
}

/// A document and the version of the client's copy, null when it holds none.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct EditedDocument
{
    /// The document.
    pub uri: DocumentUri,
    /// The version of the client's copy.
    pub version: Option<DocumentVersion>,
}

/// One edit of a document's: its text, or, to a client that takes them, a
/// snippet whose tab stops the user fills.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(untagged)]
pub enum DocumentEdit
{
    /// Text, with the annotation it names, if any.
    Text(AnnotatedEdit),
    /// A snippet.
    Snippet(SnippetEdit),
}

/// An edit whose text is a snippet (3.18 `SnippetTextEdit`).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SnippetEdit
{
    /// The range replaced.
    pub range: Range,
    /// The snippet replacing it.
    pub snippet: StringValue,
}

/// One edit, with the annotation it names, if any.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AnnotatedEdit
{
    /// The range replaced.
    pub range: Range,
    /// The text replacing it.
    pub new_text: String,
    /// The annotation it names.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub annotation_id: Option<&'static str>,
}

/// What an annotated edit tells its user, and whether it asks them to confirm.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ChangeAnnotation
{
    /// The text shown with the edit.
    pub label: &'static str,
    /// Whether the user confirms the edit before it is applied.
    pub needs_confirmation: bool,
    /// What the edit does, shown less prominently.
    pub description: &'static str,
}

impl ChangeAnnotation
{
    /// The annotation [`UNHELD`] names.
    pub const UNHELD: Self = Self {
        label: "Edit a file this editor has not opened",
        needs_confirmation: true,
        description: "The edit changes the file on disk; this editor holds no copy of it.",
    };
}

/// The name a rename at a position renames, as `textDocument/prepareRename`
/// answers it.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct PrepareRename
{
    /// Where the name is written at the position.
    pub range: Range,
    /// The name, offered as the rename's starting text.
    pub placeholder: String,
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

/// What a pull of a document's diagnostics answers.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum DiagnosticReport
{
    /// Every diagnostic the copy last published, named by their digest.
    Full
    {
        /// The digest the client names them by in its next pull.
        #[serde(rename = "resultId")]
        result_id: ResultId,
        /// The diagnostics.
        items: Vec<Diagnostic>,
    },
    /// The diagnostics the client names by its previous report's digest are
    /// still the copy's.
    Unchanged
    {
        /// That digest.
        #[serde(rename = "resultId")]
        result_id: ResultId,
    },
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
    /// Where the code is described: the issue tracking an unimplemented
    /// refusal, when the diagnostic reports one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_description: Option<CodeDescription>,
    /// The tool that produced it: always `gandr`.
    pub source: &'static str,
    /// What it says.
    pub message: String,
    /// The loci that explain it, each with what it explains.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub related_information: Vec<RelatedInformation>,
    /// How the editor marks the range besides its severity: faded, for
    /// what is unnecessary.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tags: Vec<DiagnosticTag>,
}

impl Diagnostic
{
    /// A diagnostic about the document as a whole, at its origin.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an error at the empty range at line 0, character 0, carrying
    ///   `message` and no code, code description or related location.
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
        && ret.code_description.is_none()
        && ret.source == SOURCE && ret.related_information.is_empty() && ret.tags.is_empty())]
    #[inline]
    #[must_use]
    pub fn at_origin(message: String) -> Self
    {
        Self {
            range: Range::default(),
            severity: Severity::ERROR,
            code: None,
            code_description: None,
            source: SOURCE,
            message,
            related_information: Vec::new(),
            tags: Vec::new(),
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
            code_description: None,
            source: SOURCE,
            message,
            related_information: Vec::new(),
            tags: Vec::new(),
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

/// How a diagnostic's range is marked besides its severity, as the protocol
/// numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct DiagnosticTag(u8);

impl DiagnosticTag
{
    /// Unnecessary: a binder no use refers to, which the editor fades.
    pub const UNNECESSARY: Self = Self(1);
}

/// Where a diagnostic's code is described.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CodeDescription
{
    /// The address a client opens for the code.
    pub href: String,
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

/// A declared name of the workspace, where its name is written.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SymbolInformation
{
    /// The name.
    pub name: String,
    /// What it declares.
    pub kind: SymbolKind,
    /// The range of its name in the document writing it.
    pub location: Location,
    /// The name of the declaration holding it: a module, a theory, a family
    /// or a codata declaration; none at the top of its source.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub container_name: Option<String>,
}

/// The parameters of `workspace/symbol`: the characters the names asked for
/// hold, in order.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[repr(transparent)]
pub struct WorkspaceSymbolParams
{
    /// The query; empty asks for every name.
    #[serde(default)]
    pub query: String,
}

/// A range of a document a highlight request marks.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DocumentHighlight
{
    /// The range: a name's declaring name or one of its uses.
    pub range: Range,
    /// Whether it declares the name or reads it.
    pub kind: HighlightKind,
}

/// What a highlighted range does with the name, as the protocol numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct HighlightKind(u8);

impl HighlightKind
{
    /// Neither reads nor writes: a declaring name.
    pub const TEXT: Self = Self(1);
    /// Reads the name: a use.
    pub const READ: Self = Self(2);
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use super::DocumentSymbol;
    use super::DocumentSymbols;
    use super::DocumentUri;
    use super::InitializeParams;
    use super::SymbolKind;
    use super::Unresolved;
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
    fn a_tree_uri_names_the_document_it_views()
    {
        let cases = [
            ("gandr-tree:///tmp/a.gandr", Some("file:///tmp/a.gandr")),
            ("gandr-tree:/tmp/a.gandr", Some("file:///tmp/a.gandr")),
            (
                "gandr-tree:/tmp/a%20b.gandr",
                Some("file:///tmp/a%20b.gandr"),
            ),
            ("gandr-tree://host/a.gandr", Some("file://host/a.gandr")),
            ("file:///tmp/a.gandr", None),
            ("gandr-trees:/tmp/a.gandr", None),
            ("gandr-tree:a.gandr", None),
        ];
        for (uri, viewed) in cases {
            assert_eq!(
                DocumentUri::from(uri).viewed(),
                viewed.map(DocumentUri::from),
                "{uri} views {viewed:?}"
            );
        }
    }

    #[test]
    fn the_folders_a_client_opened_are_its_roots()
    {
        let roots = |params: serde_json::Value| {
            serde_json::from_value::<InitializeParams>(params)
                .expect("the parameters read")
                .roots()
        };
        assert_eq!(
            roots(serde_json::json!({
                "rootUri": "file:///root",
                "workspaceFolders": [
                    { "uri": "file:///one", "name": "one" },
                    { "uri": "untitled:two", "name": "two" },
                    { "uri": "file:///a%20three", "name": "three" },
                ],
            })),
            [PathBuf::from("/one"), PathBuf::from("/a three")],
            "the workspace folders are the roots, a folder of another scheme left out"
        );
        assert_eq!(
            roots(serde_json::json!({ "rootUri": "file:///root", "workspaceFolders": null })),
            [PathBuf::from("/root")],
            "a client naming no workspace folders is rooted at its root"
        );
        assert_eq!(
            roots(serde_json::json!({})),
            Vec::<PathBuf>::new(),
            "a client naming no folder has no root"
        );
    }

    #[test]
    fn a_path_names_the_file_uri_that_reads_back_to_it()
    {
        let cases = [
            ("/tmp/c.gandr", Some("file:///tmp/c.gandr")),
            (
                "/tmp/a b/50%/xé.gandr",
                Some("file:///tmp/a%20b/50%25/x%C3%A9.gandr"),
            ),
            ("/tmp/q?#.gandr", Some("file:///tmp/q%3F%23.gandr")),
            ("relative/c.gandr", None),
        ];
        for (path, uri) in cases {
            let named = DocumentUri::of_path(Path::new(path));
            assert_eq!(
                named.as_ref().map(ToString::to_string).as_deref(),
                uri,
                "{path:?} is named {uri:?}"
            );
            if let Some(named) = named {
                assert_eq!(
                    named.path(),
                    PathBuf::from(path),
                    "{uri:?} reads back {path:?}"
                );
            }
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
            detail: None,
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

    #[test]
    fn a_resolved_item_needs_what_its_kind_requires()
    {
        let range = serde_json::json!({"start": {"line": 0_u8, "character": 0_u8},
            "end": {"line": 0_u8, "character": 3_u8}});
        let action = serde_json::json!({"title": "Fill", "kind": "quickfix", "edit": {"changes": {}},
            "isPreferred": true});
        let lens = serde_json::json!({"range": range, "command": {"title": "✓", "command": ""}});
        let link = serde_json::json!({"range": range, "target": "file:///tmp/base.gandr"});
        let symbol = serde_json::json!({"name": "Succ", "kind": 9_u8,
            "location": {"uri": "file:///tmp/base.gandr"}});
        let reads = |kind: Unresolved, item: &serde_json::Value| kind.read(item).is_ok();
        assert!(
            reads(Unresolved::Action, &action)
                && reads(Unresolved::Link, &link)
                && reads(Unresolved::Symbol, &symbol),
            "each kind's item as listed reads, a field it does not require kept aside"
        );
        assert!(
            !reads(Unresolved::Action, &serde_json::json!({"kind": "quickfix"}))
                && !reads(Unresolved::Link, &serde_json::json!({"range": "0:0"}))
                && !reads(Unresolved::Symbol, &serde_json::json!({"name": "Succ"}))
                && !reads(Unresolved::Symbol, &serde_json::json!([])),
            "an item without a required field, or with one of another shape, is refused"
        );
        assert!(
            !reads(Unresolved::Action, &lens) && !reads(Unresolved::Link, &action),
            "an item of another kind is refused"
        );
    }
}
