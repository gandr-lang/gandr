//! The versioned render-bus frame: the envelope that carries the presentation
//! seam across a process boundary.
//!
//! # Routing
//!
//! A frame is document-scoped or connection-scoped. A document-scoped frame
//! carries the document's URI and the editor's version of it — the version the
//! report describes — and a renderer paints it only while that version matches
//! the buffer it shows, asking for a [`FrameBody::Resync`] otherwise, so a
//! stale report is dropped rather than painted. A connection-scoped frame
//! concerns no one document.
//!
//! # Versioning
//!
//! The wire image carries [`WIRE_SCHEMA_VERSION`] in every frame, and a decode
//! refuses any other. The version moves whenever a wire field is renamed,
//! removed, or changes meaning; an added field leaves it.
//!
//! # Session shape
//!
//! The message set is the projection of one binary session,
//! `?Attach . !Hello . μX. (!Frame . X & ?Resync . X & ?Detach . end)`, so a
//! typed endpoint can carry the same frames as its messages.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::present::DiagCard;
use crate::present::GoalCard;
use crate::present::HlSpan;
use crate::present::MarkSpan;

/// A render-bus wire schema version.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireSchemaVersion(u32);

impl From<u32> for WireSchemaVersion
{
    /// Read a `u32` as a schema version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: u32) -> Self
    {
        Self(version)
    }
}

impl From<WireSchemaVersion> for u32
{
    /// Read the version back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: WireSchemaVersion) -> Self
    {
        version.0
    }
}

impl fmt::Display for WireSchemaVersion
{
    /// Write the version number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// The render-bus wire schema version this crate writes and reads.
pub const WIRE_SCHEMA_VERSION: WireSchemaVersion = WireSchemaVersion(1);

/// The editor's version of a document, as the language server protocol counts
/// it.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DocVersion(i32);

impl From<i32> for DocVersion
{
    /// Read an `i32` as a document version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: i32) -> Self
    {
        Self(version)
    }
}

impl From<DocVersion> for i32
{
    /// Read the version back out as an `i32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: DocVersion) -> Self
    {
        version.0
    }
}

/// A document's URI, as the language server protocol names a document.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DocumentUri(String);

impl From<String> for DocumentUri
{
    /// Read a string as a document URI.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(uri: String) -> Self
    {
        Self(uri)
    }
}

impl AsRef<str> for DocumentUri
{
    /// Borrow the URI's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for DocumentUri
{
    /// Write the URI.
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

/// A document's identity at one version: its URI and the editor's version.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct DocId
{
    /// The document's URI.
    pub uri: DocumentUri,
    /// The editor's version of the document.
    pub version: DocVersion,
}

/// What a frame is about: one document at one version, or the connection.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum FrameScope
{
    /// The frame concerns the connection, no one document.
    Connection,
    /// The frame concerns this document at this version.
    Document(DocId),
}

/// The renderer-facing report a [`FrameBody::Frame`] carries: highlights,
/// marks, diagnostic cards and goal cards over one document version.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ReportView
{
    /// The highlight spans over the document.
    pub highlights: Vec<HlSpan>,
    /// The mark spans: error underlines and hole tints.
    pub marks: Vec<MarkSpan>,
    /// The diagnostic cards.
    pub diagnostics: Vec<DiagCard>,
    /// The goal cards, in source order.
    pub goals: Vec<GoalCard>,
}

/// The payload of a [`RenderFrame`].
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(tag = "kind", content = "data", rename_all = "snake_case")
)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FrameBody
{
    /// Server to client on attach: the documents the server tracks.
    /// Connection-scoped.
    Hello
    {
        /// The tracked documents, each at its current version.
        docs: Vec<DocId>,
    },
    /// The whole report for one document version. Document-scoped.
    Frame
    {
        /// The report.
        report: ReportView,
    },
    /// Client to server: the client fell behind and asks for a whole
    /// [`Self::Frame`] at the frame's document version. Document-scoped.
    Resync,
    /// Either direction: close the stream. Connection-scoped.
    Detach,
}

/// One render-bus message: a body and the scope it is routed by.
///
/// # Specification
/// - ensures: a [`FrameBody::Frame`] or [`FrameBody::Resync`] is
///   document-scoped and a [`FrameBody::Hello`] or [`FrameBody::Detach`] is
///   connection-scoped, in every frame built by the four constructors or
///   decoded.
/// - provides: under the `serde` feature, the wire image `{"schema_version",
///   "doc_uri", "doc_version", "body"}`, the two routing keys `null` for a
///   connection-scoped frame; the decode refuses another schema version, keys
///   present one without the other, and keys that disagree with the body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RenderFrame
{
    /// The frame's routing.
    scope: FrameScope,
    /// The frame's payload.
    body: FrameBody,
}

impl RenderFrame
{
    /// The attach greeting: the documents the server tracks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a connection-scoped [`FrameBody::Hello`] carrying `docs`
    ///   unchanged.
    /// - provides: the server's first message.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the scope and the body read back separate this
    ///   constructor from one that routes the greeting to a document.
    /// - witness: `wire::tests::connection_scoped_constructors_omit_routing_keys`
    #[inline]
    #[must_use]
    pub const fn hello(docs: Vec<DocId>) -> Self
    {
        Self {
            scope: FrameScope::Connection,
            body: FrameBody::Hello { docs },
        }
    }

    /// The whole report for `document`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a frame scoped to `document` whose body is
    ///   [`FrameBody::Frame`] carrying `report` unchanged.
    /// - provides: the message a renderer paints.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the scope, the version and the body read back
    ///   separate this constructor from one that drops or swaps them.
    /// - witness: `wire::tests::document_scoped_constructors_populate_routing_keys`
    #[inline]
    #[must_use]
    pub const fn frame(
        document: DocId,
        report: ReportView,
    ) -> Self
    {
        Self {
            scope: FrameScope::Document(document),
            body: FrameBody::Frame { report },
        }
    }

    /// The request for a whole frame at `document`'s version.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a frame scoped to `document` whose body is
    ///   [`FrameBody::Resync`].
    /// - provides: the client's catch-up request.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the scope and the body read back separate this
    ///   constructor from one that leaves the request unrouted.
    /// - witness: `wire::tests::document_scoped_constructors_populate_routing_keys`
    #[inline]
    #[must_use]
    pub const fn resync(document: DocId) -> Self
    {
        Self {
            scope: FrameScope::Document(document),
            body: FrameBody::Resync,
        }
    }

    /// The close of the stream.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a connection-scoped [`FrameBody::Detach`].
    /// - provides: either side's last message.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the scope and the body read back separate this
    ///   constructor from one that routes the close to a document.
    /// - witness: `wire::tests::connection_scoped_constructors_omit_routing_keys`
    #[inline]
    #[must_use]
    pub const fn detach() -> Self
    {
        Self {
            scope: FrameScope::Connection,
            body: FrameBody::Detach,
        }
    }

    /// The frame's routing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> &FrameScope
    {
        &self.scope
    }

    /// The frame's payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> &FrameBody
    {
        &self.body
    }
}

/// The encode image of a [`RenderFrame`], borrowing the frame's parts.
#[cfg(feature = "serde")]
#[derive(serde::Serialize)]
struct RenderFrameImage<'frame>
{
    /// Always [`WIRE_SCHEMA_VERSION`].
    schema_version: WireSchemaVersion,
    /// The document's URI; `None` for a connection-scoped frame.
    doc_uri: Option<&'frame DocumentUri>,
    /// The document's version; `None` exactly when [`Self::doc_uri`] is.
    doc_version: Option<DocVersion>,
    /// The payload.
    body: &'frame FrameBody,
}

#[cfg(feature = "serde")]
impl serde::Serialize for RenderFrame
{
    /// Encode the frame with its schema version and its routing keys.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the image carries [`WIRE_SCHEMA_VERSION`], the document's URI
    ///   and version for a document-scoped frame and `null` for both otherwise,
    ///   and the adjacently tagged body.
    /// - fails: propagates the serializer's own error.
    /// - panics: none.
    ///
    /// # Errors
    /// The serializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact keys of a document-scoped image, and every
    ///   body decoding back to its frame, separate an encode that drops, swaps
    ///   or nulls a routing key.
    /// - witness: `wire::tests::frame_body_is_adjacently_tagged_on_the_wire`
    /// - witness: `wire::tests::every_body_variant_round_trips_through_json`
    #[inline]
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (doc_uri, doc_version) = match self.scope {
            | FrameScope::Connection => (None, None),
            | FrameScope::Document(ref document) => (Some(&document.uri), Some(document.version)),
        };
        let image = RenderFrameImage {
            schema_version: WIRE_SCHEMA_VERSION,
            doc_uri,
            doc_version,
            body: &self.body,
        };

        image.serialize(serializer)
    }
}

/// The decode image of a [`RenderFrame`]: its fields before the routing and
/// version checks.
#[cfg(feature = "serde")]
#[derive(serde::Deserialize)]
struct RenderFrameWire
{
    /// The decoded schema version.
    schema_version: WireSchemaVersion,
    /// The decoded document URI, absent for a connection-scoped frame.
    doc_uri: Option<DocumentUri>,
    /// The decoded document version, absent with the URI.
    doc_version: Option<DocVersion>,
    /// The decoded payload; its variant decides which routing is lawful.
    body: FrameBody,
}

/// A connection-scoped body a decoded frame routed to a document.
#[cfg(feature = "serde")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConnectionBody
{
    /// [`FrameBody::Hello`].
    Hello,
    /// [`FrameBody::Detach`].
    Detach,
}

/// A document-scoped body a decoded frame left unrouted.
#[cfg(feature = "serde")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DocumentBody
{
    /// [`FrameBody::Frame`].
    Frame,
    /// [`FrameBody::Resync`].
    Resync,
}

/// Why a decoded image is not a frame.
#[cfg(feature = "serde")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FrameDecodeError
{
    /// The image is at another schema version.
    SchemaVersion
    {
        /// The version the image carries.
        found: WireSchemaVersion,
    },
    /// One routing key is present without the other.
    RoutingLockstep,
    /// A connection-scoped body carries document routing keys.
    ConnectionScopedRouted
    {
        /// The body.
        body: ConnectionBody,
    },
    /// A document-scoped body carries no routing keys.
    DocumentScopedUnrouted
    {
        /// The body.
        body: DocumentBody,
    },
}

#[cfg(feature = "serde")]
impl fmt::Display for FrameDecodeError
{
    /// Write the broken invariant.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: names the version found and the version supported, the
    ///   lockstep rule, or the body and the routing it requires.
    /// - provides: the message a decode failure carries.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::SchemaVersion { found } => write!(
                f,
                "render frame schema_version {found} is not the supported wire schema {WIRE_SCHEMA_VERSION}"
            ),
            | Self::RoutingLockstep => f.write_str(
                "render frame doc_uri and doc_version must be present or absent in lockstep",
            ),
            | Self::ConnectionScopedRouted { body } => {
                let name = match body {
                    | ConnectionBody::Hello => "hello",
                    | ConnectionBody::Detach => "detach",
                };
                write!(
                    f,
                    "{name} render frames must not carry document routing keys"
                )
            },
            | Self::DocumentScopedUnrouted { body } => {
                let name = match body {
                    | DocumentBody::Frame => "frame",
                    | DocumentBody::Resync => "resync",
                };
                write!(f, "{name} render frames require document routing keys")
            },
        }
    }
}

#[cfg(feature = "serde")]
impl RenderFrame
{
    /// Validate a decoded image into a frame.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the frame carries the image's body, scoped to the
    ///   image's document when both routing keys are present and to the
    ///   connection when both are absent.
    /// - fails: [`FrameDecodeError::SchemaVersion`] for any version but
    ///   [`WIRE_SCHEMA_VERSION`]; [`FrameDecodeError::RoutingLockstep`] for one
    ///   key without the other; [`FrameDecodeError::ConnectionScopedRouted`]
    ///   and [`FrameDecodeError::DocumentScopedUnrouted`] for routing that
    ///   disagrees with the body. The checks run in that order.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`FrameDecodeError`] naming the first broken invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every body is decoded at its lawful routing, and each
    ///   refusal is triggered by one image that breaks only its invariant: a
    ///   foreign version, each half of the lockstep, a routed greeting and an
    ///   unrouted report, each asserted by its message.
    /// - witness: `wire::tests::every_body_variant_round_trips_through_json`
    /// - witness: `wire::tests::a_frame_is_refused_at_another_schema_version`
    /// - witness: `wire::tests::deserialize_rejects_doc_uri_doc_version_lockstep_violations`
    /// - witness: `wire::tests::deserialize_rejects_body_routing_mismatches`
    fn from_wire(wire: RenderFrameWire) -> Result<Self, FrameDecodeError>
    {
        if wire.schema_version != WIRE_SCHEMA_VERSION {
            return Err(FrameDecodeError::SchemaVersion {
                found: wire.schema_version,
            });
        }
        let scope = match (wire.doc_uri, wire.doc_version) {
            | (Some(uri), Some(version)) => FrameScope::Document(DocId { uri, version }),
            | (None, None) => FrameScope::Connection,
            | (Some(_), None) | (None, Some(_)) => return Err(FrameDecodeError::RoutingLockstep),
        };
        match (&wire.body, &scope) {
            | (&(FrameBody::Hello { .. } | FrameBody::Detach), &FrameScope::Connection)
            | (&(FrameBody::Frame { .. } | FrameBody::Resync), &FrameScope::Document(_)) => {},
            | (&FrameBody::Hello { .. }, &FrameScope::Document(_)) => {
                return Err(FrameDecodeError::ConnectionScopedRouted {
                    body: ConnectionBody::Hello,
                });
            },
            | (&FrameBody::Detach, &FrameScope::Document(_)) => {
                return Err(FrameDecodeError::ConnectionScopedRouted {
                    body: ConnectionBody::Detach,
                });
            },
            | (&FrameBody::Frame { .. }, &FrameScope::Connection) => {
                return Err(FrameDecodeError::DocumentScopedUnrouted {
                    body: DocumentBody::Frame,
                });
            },
            | (&FrameBody::Resync, &FrameScope::Connection) => {
                return Err(FrameDecodeError::DocumentScopedUnrouted {
                    body: DocumentBody::Resync,
                });
            },
        }

        Ok(Self {
            scope,
            body: wire.body,
        })
    }
}

#[cfg(feature = "serde")]
impl<'input> serde::Deserialize<'input> for RenderFrame
{
    /// Decode a frame and validate its version and routing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the frame [`RenderFrame::from_wire`] validates
    ///   from the decoded image.
    /// - fails: the deserializer's error for a malformed image, and a custom
    ///   error carrying the [`FrameDecodeError`] message for an image that
    ///   breaks a frame invariant.
    /// - panics: none.
    ///
    /// # Errors
    /// The deserializer's error, or the broken invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every body round-trips, and each broken invariant is
    ///   refused with its own message, which separates a validating decode from
    ///   a structural one.
    /// - witness: `wire::tests::every_body_variant_round_trips_through_json`
    /// - witness: `wire::tests::a_frame_is_refused_at_another_schema_version`
    /// - witness: `wire::tests::deserialize_rejects_doc_uri_doc_version_lockstep_violations`
    /// - witness: `wire::tests::deserialize_rejects_body_routing_mismatches`
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'input>,
    {
        let wire = RenderFrameWire::deserialize(deserializer)?;

        Self::from_wire(wire).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::DocId;
    use super::DocVersion;
    use super::DocumentUri;
    use super::FrameBody;
    use super::FrameScope;
    use super::RenderFrame;
    use super::ReportView;
    use super::WIRE_SCHEMA_VERSION;
    use crate::present::ByteOffset;
    use crate::present::ByteRange;
    use crate::present::GoalCard;
    use crate::present::HlRole;
    use crate::present::HlSpan;

    /// An editor version, written as a count.
    #[repr(transparent)]
    struct Version(i32);

    /// The document `file:///a.gandr` at the [`Version`] given.
    ///
    /// # Specification
    /// trivial.
    fn document(Version(version): Version) -> DocId
    {
        DocId {
            uri: DocumentUri::from(alloc::string::String::from("file:///a.gandr")),
            version: DocVersion::from(version),
        }
    }

    /// The JSON image of `frame`.
    ///
    /// # Specification
    /// trivial.
    fn image(frame: &RenderFrame) -> serde_json::Value
    {
        serde_json::to_value(frame).expect("a frame serializes")
    }

    /// The message `image` is refused with.
    ///
    /// # Specification
    /// trivial.
    fn refusal(image: serde_json::Value) -> alloc::string::String
    {
        serde_json::from_value::<RenderFrame>(image)
            .expect_err("the image breaks a frame invariant")
            .to_string()
    }

    #[test]
    fn document_scoped_constructors_populate_routing_keys()
    {
        let report = RenderFrame::frame(document(Version(7)), ReportView::default());
        assert_eq!(
            &FrameScope::Document(document(Version(7))),
            report.scope(),
            "a report is routed to its document at its version"
        );
        assert_eq!(
            &FrameBody::Frame {
                report: ReportView::default(),
            },
            report.body(),
            "the report is carried unchanged"
        );

        let resync = RenderFrame::resync(document(Version(8)));
        assert_eq!(
            &FrameScope::Document(document(Version(8))),
            resync.scope(),
            "a resync is routed to the version it asks for"
        );
        assert_eq!(&FrameBody::Resync, resync.body(), "the body is a resync");
    }

    #[test]
    fn connection_scoped_constructors_omit_routing_keys()
    {
        let hello = RenderFrame::hello(vec![document(Version(1))]);
        assert_eq!(
            &FrameScope::Connection,
            hello.scope(),
            "the greeting concerns the connection"
        );
        assert_eq!(
            &FrameBody::Hello {
                docs: vec![document(Version(1))],
            },
            hello.body(),
            "the greeting carries the tracked documents"
        );

        let detach = RenderFrame::detach();
        assert_eq!(
            &FrameScope::Connection,
            detach.scope(),
            "the close concerns the connection"
        );
        assert_eq!(&FrameBody::Detach, detach.body(), "the body is a close");
    }

    #[test]
    fn every_body_variant_round_trips_through_json()
    {
        let report = ReportView {
            highlights: vec![HlSpan {
                range: ByteRange::new(ByteOffset::from(0_usize), ByteOffset::from(3_usize))
                    .expect("an ordered range"),
                role: HlRole::Keyword,
            }],
            goals: vec![GoalCard {
                label: "?0".into(),
                note: "hole".into(),
                expected: None,
                ctx: Vec::new(),
                range: ByteRange::new(ByteOffset::from(8_usize), ByteOffset::from(9_usize))
                    .expect("an ordered range"),
            }],
            ..ReportView::default()
        };
        let frames = [
            RenderFrame::hello(vec![document(Version(1))]),
            RenderFrame::hello(Vec::new()),
            RenderFrame::frame(document(Version(2)), report),
            RenderFrame::frame(document(Version(2)), ReportView::default()),
            RenderFrame::resync(document(Version(2))),
            RenderFrame::detach(),
        ];
        for frame in frames {
            let json = serde_json::to_string(&frame).expect("serialize");
            let back: RenderFrame = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(frame, back, "the frame round-trips: {json}");
        }
    }

    #[test]
    fn a_frame_is_refused_at_another_schema_version()
    {
        let frame = RenderFrame::resync(document(Version(2)));
        let mut foreign = image(&frame);
        assert_eq!(
            u32::from(WIRE_SCHEMA_VERSION),
            foreign["schema_version"],
            "the image carries the supported version"
        );
        let back: RenderFrame =
            serde_json::from_value(foreign.clone()).expect("the supported version decodes");
        assert_eq!(frame, back, "the version round-trips with the frame");

        for version in [
            u32::from(WIRE_SCHEMA_VERSION).saturating_add(1),
            u32::from(WIRE_SCHEMA_VERSION).saturating_sub(1),
        ] {
            foreign["schema_version"] = serde_json::Value::from(version);
            let refused = refusal(foreign.clone());
            assert!(
                refused.contains(&alloc::format!(
                    "render frame schema_version {version} is not the supported wire schema {WIRE_SCHEMA_VERSION}"
                )),
                "the refusal names both versions: {refused}"
            );
        }
    }

    #[test]
    fn deserialize_rejects_doc_uri_doc_version_lockstep_violations()
    {
        let mut missing_version = image(&RenderFrame::resync(document(Version(2))));
        missing_version["doc_version"] = serde_json::Value::Null;
        let missing_version_err = refusal(missing_version);
        assert!(
            missing_version_err.contains("lockstep"),
            "a URI without a version names the lockstep invariant: {missing_version_err}"
        );

        let mut missing_uri = image(&RenderFrame::resync(document(Version(2))));
        missing_uri["doc_uri"] = serde_json::Value::Null;
        let missing_uri_err = refusal(missing_uri);
        assert!(
            missing_uri_err.contains("lockstep"),
            "a version without a URI names the lockstep invariant: {missing_uri_err}"
        );
    }

    #[test]
    fn deserialize_rejects_body_routing_mismatches()
    {
        let routed = |frame: &RenderFrame| {
            let mut routed = image(frame);
            routed["doc_uri"] = serde_json::Value::from("file:///a.gandr");
            routed["doc_version"] = serde_json::Value::from(2_i32);
            routed
        };
        let unrouted = |frame: &RenderFrame| {
            let mut unrouted = image(frame);
            unrouted["doc_uri"] = serde_json::Value::Null;
            unrouted["doc_version"] = serde_json::Value::Null;
            unrouted
        };
        let cases = [
            (
                routed(&RenderFrame::hello(Vec::new())),
                "hello render frames must not carry document routing keys",
            ),
            (
                routed(&RenderFrame::detach()),
                "detach render frames must not carry document routing keys",
            ),
            (
                unrouted(&RenderFrame::frame(
                    document(Version(2)),
                    ReportView::default(),
                )),
                "frame render frames require document routing keys",
            ),
            (
                unrouted(&RenderFrame::resync(document(Version(2)))),
                "resync render frames require document routing keys",
            ),
        ];
        for (image, message) in cases {
            let refused = refusal(image);
            assert!(
                refused.contains(message),
                "the refusal names the body and its routing: {refused}"
            );
        }
    }

    #[test]
    fn frame_body_is_adjacently_tagged_on_the_wire()
    {
        let resync = image(&RenderFrame::resync(document(Version(5))));
        assert_eq!(
            serde_json::json!({
                "schema_version": u32::from(WIRE_SCHEMA_VERSION),
                "doc_uri": "file:///a.gandr",
                "doc_version": 5_i32,
                "body": {"kind": "resync"},
            }),
            resync,
            "a document-scoped frame carries both routing keys and a tagged body"
        );

        let hello = image(&RenderFrame::hello(vec![document(Version(1))]));
        assert_eq!(
            serde_json::json!({
                "schema_version": u32::from(WIRE_SCHEMA_VERSION),
                "doc_uri": null,
                "doc_version": null,
                "body": {
                    "kind": "hello",
                    "data": {"docs": [{"uri": "file:///a.gandr", "version": 1_i32}]},
                },
            }),
            hello,
            "a connection-scoped frame nulls both routing keys"
        );
    }
}
