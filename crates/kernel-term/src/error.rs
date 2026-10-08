//! The decoder's closed rejection vocabulary.
//!
//! A decode failure is a **format** failure and is held apart from a typing
//! failure, so the two never blur: nothing here says a term is ill-typed, and
//! nothing a checker later reports says an artifact was malformed.
//!
//! The vocabulary is a rejection triple — truncation, an unknown tag at a named
//! site, a violated structural invariant — plus the two refusals that exist so
//! that a reserved part of the format is refused *by name* rather than as a
//! generic bad byte, and the version refusal that names the version it met
//! rather than guessing at it.

use core::error::Error;
use core::fmt;

use crate::wire::FormatVersion;
use crate::wire::WireTag;

/// A reserved declaration kind: a shape the encoder never emits and the decoder
/// refuses distinctly.
///
/// The kinds a module layer would export are reserved together, so graduating
/// one of them into the kernel never renumbers a shipped format. A live kind,
/// such as the abstract type, is written and decoded like a definition and has
/// no variant here: this vocabulary lists only kinds the decoder refuses.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ReservedKind
{
    /// A reserved module-signature declaration kind.
    ModuleSig,
    /// A reserved module-definition declaration kind.
    ModuleDef,
    /// A reserved functor-definition declaration kind.
    FunctorDef,
}

impl fmt::Display for ReservedKind
{
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::ModuleSig => "ModuleSig",
            | Self::ModuleDef => "ModuleDef",
            | Self::FunctorDef => "FunctorDef",
        })
    }
}

/// A reserved slot or section that must be empty, or a live one whose content
/// the decoder refuted.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ReservedSlot
{
    /// The minted-atom table disagreed with the declarations decoded beside it.
    ///
    /// This is the one refusal in the family that is not about emptiness: the
    /// table is live, and it is refuted rather than believed.
    MintedAtomTable,
    /// The structured-name record carried a segment. A name is a sequence of
    /// segments rather than a flat dotted string, and the point of reserving it
    /// is that a namespace layer's strings must never become the export
    /// identity; until one exists the count is pinned to zero.
    StructuredName,
    /// The erasure annotation slot was non-empty.
    ErasureAnnotation,
    /// The modes-and-grades annotation slot was non-empty.
    ModeGradeAnnotation,
    /// The directedness-and-variance annotation slot was non-empty.
    DirectednessVariance,
}

impl fmt::Display for ReservedSlot
{
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::MintedAtomTable => "the minted-atom table",
            | Self::StructuredName => "the structured-name record",
            | Self::ErasureAnnotation => "the erasure annotation slot",
            | Self::ModeGradeAnnotation => "the modes-and-grades annotation slot",
            | Self::DirectednessVariance => "the directedness-and-variance annotation slot",
        })
    }
}

/// Where in the closed grammar an unknown tag byte was met.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TagSite
{
    /// A declaration's admission mark.
    Admission,
    /// A declaration's kind byte, outside the live and reserved kinds alike.
    DeclarationKind,
    /// A subterm-table node tag, outside the frozen block.
    Node,
    /// A base-type atom.
    BaseType,
    /// A literal sign.
    Sign,
    /// A literal kind.
    LiteralKind,
    /// An injection side.
    Side,
    /// A landmark-constraint relation.
    ConstraintRelation,
}

impl fmt::Display for TagSite
{
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Admission => "an admission mark",
            | Self::DeclarationKind => "a declaration kind",
            | Self::Node => "a subterm-table node tag",
            | Self::BaseType => "a base-type atom",
            | Self::Sign => "a literal sign",
            | Self::LiteralKind => "a literal kind",
            | Self::Side => "an injection side",
            | Self::ConstraintRelation => "a constraint relation",
        })
    }
}

/// Which structural invariant a malformed artifact violated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MalformedSite
{
    /// The magic did not match a gandr kernel export.
    Header,
    /// A varint was overlong — that is, non-minimal — or exceeded the 64-bit
    /// range.
    Varint,
    /// A decoded index did not fit its target width.
    IndexRange,
    /// A level atom's offset met or exceeded the decode cap, or its
    /// reconstruction overflowed.
    LevelOffset,
    /// A decoded landmark-constraint side was not variable-only, which its
    /// smart constructor refuses.
    ConstraintForm,
    /// A literal payload was not reconstructible: a magnitude or fraction
    /// carried a non-digit byte, or a string literal's bytes were not UTF-8.
    LiteralPayload,
    /// A decoded child's polarity did not fit the slot its parent's constructor
    /// requires.
    Polarity,
    /// A child index was not strictly earlier than its own entry's global
    /// index, so acyclicity and topological order were violated.
    ChildOrder,
    /// The subterm table exceeded the entry cap as its entries accrued.
    TableSize,
    /// A declaration root's expanded tree size exceeded the per-declaration
    /// work cap.
    ExpandedWork,
    /// The artifact-total expanded tree size exceeded the artifact work cap.
    ArtifactExpandedWork,
    /// The bytes decoded but were not the canonical encoding of what they
    /// decoded to: a redundant duplicate entry, a mis-ordered table, or a dead
    /// entry no declaration root reaches.
    NonCanonical,
    /// Bytes remained after a complete artifact was decoded.
    TrailingBytes,
}

impl fmt::Display for MalformedSite
{
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Header => "the artifact magic did not match",
            | Self::Varint => "a varint was overlong or out of range",
            | Self::IndexRange => "a decoded index did not fit its width",
            | Self::LevelOffset => "a level atom offset exceeded the decode cap",
            | Self::ConstraintForm => "a constraint side was not variable-only",
            | Self::LiteralPayload => "a literal payload was not reconstructible",
            | Self::Polarity => "a decoded node had the wrong polarity for its slot",
            | Self::ChildOrder => "a child index was not strictly earlier than its entry",
            | Self::TableSize => "the subterm table exceeded the entry cap",
            | Self::ExpandedWork => "a declaration's expanded size exceeded the work cap",
            | Self::ArtifactExpandedWork => {
                "the artifact-total expanded size exceeded the artifact work cap"
            },
            | Self::NonCanonical => "the bytes were not the canonical encoding",
            | Self::TrailingBytes => "bytes remained after a complete artifact",
        })
    }
}

/// Why decoding an artifact failed.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DecodeError
{
    /// The artifact ended mid-field.
    Truncated,
    /// A tag byte fell outside the closed vocabulary at a tagged position.
    UnknownTag
    {
        /// Where the tag was read.
        site: TagSite,
        /// The offending byte.
        tag: WireTag,
    },
    /// The bytes were structurally decodable but violated an invariant.
    Malformed
    {
        /// Which invariant was violated.
        site: MalformedSite,
    },
    /// A reserved declaration kind was present.
    ReservedDeclarationKind
    {
        /// The reserved kind met.
        kind: ReservedKind,
    },
    /// A reserved slot or section was occupied, or a live one was refuted.
    ReservedSlotOccupied
    {
        /// The slot in question.
        slot: ReservedSlot,
    },
    /// The artifact declared a format version this decoder does not implement.
    UnsupportedVersion
    {
        /// The version the artifact declared.
        found: FormatVersion,
    },
}

impl fmt::Display for DecodeError
{
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Truncated => f.write_str("the artifact ended mid-field"),
            | Self::UnknownTag { site, tag } => {
                write!(f, "unknown tag {tag} where {site} was expected")
            },
            | Self::Malformed { site } => write!(f, "malformed artifact: {site}"),
            | Self::ReservedDeclarationKind { kind } => {
                write!(f, "the reserved declaration kind {kind} is not admitted")
            },
            | Self::ReservedSlotOccupied { slot } => {
                write!(f, "{slot} did not hold its required content")
            },
            | Self::UnsupportedVersion { found } => {
                write!(f, "unsupported artifact format version {found}")
            },
        }
    }
}

impl Error for DecodeError
{
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;

    use super::DecodeError;
    use super::MalformedSite;
    use super::ReservedKind;
    use super::ReservedSlot;
    use super::TagSite;
    use crate::wire::FormatVersion;
    use crate::wire::WireTag;

    #[test]
    fn every_refusal_renders_its_site_and_its_byte()
    {
        assert_eq!(
            String::from("unknown tag 0x2a where a subterm-table node tag was expected"),
            format!("{}", DecodeError::UnknownTag {
                site: TagSite::Node,
                tag: WireTag::from(0x2a),
            })
        );
        assert_eq!(
            String::from("malformed artifact: the bytes were not the canonical encoding"),
            format!("{}", DecodeError::Malformed {
                site: MalformedSite::NonCanonical,
            })
        );
        assert_eq!(
            String::from("the reserved declaration kind FunctorDef is not admitted"),
            format!("{}", DecodeError::ReservedDeclarationKind {
                kind: ReservedKind::FunctorDef,
            })
        );
        assert_eq!(
            String::from("the minted-atom table did not hold its required content"),
            format!("{}", DecodeError::ReservedSlotOccupied {
                slot: ReservedSlot::MintedAtomTable,
            })
        );
        assert_eq!(
            String::from("unsupported artifact format version 0"),
            format!("{}", DecodeError::UnsupportedVersion {
                found: FormatVersion::from(0),
            })
        );
        assert_eq!(
            String::from("the artifact ended mid-field"),
            format!("{}", DecodeError::Truncated)
        );
    }

    #[test]
    fn every_tag_site_and_malformed_site_names_itself()
    {
        let sites = [
            (TagSite::Admission, "an admission mark"),
            (TagSite::DeclarationKind, "a declaration kind"),
            (TagSite::Node, "a subterm-table node tag"),
            (TagSite::BaseType, "a base-type atom"),
            (TagSite::Sign, "a literal sign"),
            (TagSite::LiteralKind, "a literal kind"),
            (TagSite::Side, "an injection side"),
            (TagSite::ConstraintRelation, "a constraint relation"),
        ];
        for (site, expected) in sites {
            assert_eq!(String::from(expected), format!("{site}"));
        }

        let malformed = [
            (MalformedSite::Header, "the artifact magic did not match"),
            (
                MalformedSite::Varint,
                "a varint was overlong or out of range",
            ),
            (
                MalformedSite::IndexRange,
                "a decoded index did not fit its width",
            ),
            (
                MalformedSite::LevelOffset,
                "a level atom offset exceeded the decode cap",
            ),
            (
                MalformedSite::ConstraintForm,
                "a constraint side was not variable-only",
            ),
            (
                MalformedSite::LiteralPayload,
                "a literal payload was not reconstructible",
            ),
            (
                MalformedSite::Polarity,
                "a decoded node had the wrong polarity for its slot",
            ),
            (
                MalformedSite::ChildOrder,
                "a child index was not strictly earlier than its entry",
            ),
            (
                MalformedSite::TableSize,
                "the subterm table exceeded the entry cap",
            ),
            (
                MalformedSite::ExpandedWork,
                "a declaration's expanded size exceeded the work cap",
            ),
            (
                MalformedSite::ArtifactExpandedWork,
                "the artifact-total expanded size exceeded the artifact work cap",
            ),
            (
                MalformedSite::NonCanonical,
                "the bytes were not the canonical encoding",
            ),
            (
                MalformedSite::TrailingBytes,
                "bytes remained after a complete artifact",
            ),
        ];
        for (site, expected) in malformed {
            assert_eq!(String::from(expected), format!("{site}"));
        }

        let slots = [
            (ReservedSlot::StructuredName, "the structured-name record"),
            (
                ReservedSlot::ErasureAnnotation,
                "the erasure annotation slot",
            ),
            (
                ReservedSlot::ModeGradeAnnotation,
                "the modes-and-grades annotation slot",
            ),
            (
                ReservedSlot::DirectednessVariance,
                "the directedness-and-variance annotation slot",
            ),
        ];
        for (slot, expected) in slots {
            assert_eq!(String::from(expected), format!("{slot}"));
        }

        let kinds = [
            (ReservedKind::ModuleSig, "ModuleSig"),
            (ReservedKind::ModuleDef, "ModuleDef"),
        ];
        for (kind, expected) in kinds {
            assert_eq!(String::from(expected), format!("{kind}"));
        }
    }
}
