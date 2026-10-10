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
///
/// # Specification
/// - requires: the value classifies a format refusal, not a typing judgement.
/// - ensures: retains the named refusal category and its declared payload so
///   distinct format causes remain observable.
/// - panics: none.
/// - executable: none — this closed classification is a data declaration;
///   reader operations select it and formatting exposes its payload.
///
/// # Adequacy
/// - hypothesis: L3 covers every refusal category and site, all tag-byte
///   spellings, version and quantity ceilings, the two sort literals, and
///   refusal by a real exhausted byte sink. It observes distinct causes,
///   complete numeric payloads and exact sink error kinds, separating collapsed
///   classifications, lost high bits and swallowed failures. Diagnostic wording
///   and nondefault formatter flags are outside the hypothesis.
/// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
    /// Writes the reserved kind's name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one fixed name per variant.
    /// - provides: the rendering a refusal message interpolates, so a reserved
    ///   kind names itself rather than a numeric tag.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   its output nor refusal state; observing those effects here would
    ///   require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers every refusal category and site, all tag-byte
    ///   spellings, version and quantity ceilings, the two sort literals, and
    ///   refusal by a real exhausted byte sink. It observes distinct causes,
    ///   complete numeric payloads and exact sink error kinds, separating
    ///   collapsed classifications, lost high bits and swallowed failures.
    ///   Diagnostic wording and nondefault formatter flags are outside the
    ///   hypothesis.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
///
/// # Specification
/// - requires: the value classifies a format refusal, not a typing judgement.
/// - ensures: retains the named refusal category and its declared payload so
///   distinct format causes remain observable.
/// - panics: none.
/// - executable: none — this closed classification is a data declaration;
///   reader operations select it and formatting exposes its payload.
///
/// # Adequacy
/// - hypothesis: L3 covers every refusal category and site, all tag-byte
///   spellings, version and quantity ceilings, the two sort literals, and
///   refusal by a real exhausted byte sink. It observes distinct causes,
///   complete numeric payloads and exact sink error kinds, separating collapsed
///   classifications, lost high bits and swallowed failures. Diagnostic wording
///   and nondefault formatter flags are outside the hypothesis.
/// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ReservedSlot
{
    /// The minted-atom table disagreed with the declarations decoded beside it.
    ///
    /// This is the one refusal in the family that is not about emptiness: the
    /// table is live, and it is refuted rather than believed.
    MintedAtomTable,
    /// The erasure annotation slot was non-empty.
    ErasureAnnotation,
    /// The modes-and-grades annotation slot was non-empty.
    ModeGradeAnnotation,
    /// The directedness-and-variance annotation slot was non-empty.
    DirectednessVariance,
}

impl fmt::Display for ReservedSlot
{
    /// Writes the reserved slot's description.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one fixed description per variant.
    /// - provides: the rendering a refusal message interpolates, so a non-empty
    ///   reserved slot names itself.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   its output nor refusal state; observing those effects here would
    ///   require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers every refusal category and site, all tag-byte
    ///   spellings, version and quantity ceilings, the two sort literals, and
    ///   refusal by a real exhausted byte sink. It observes distinct causes,
    ///   complete numeric payloads and exact sink error kinds, separating
    ///   collapsed classifications, lost high bits and swallowed failures.
    ///   Diagnostic wording and nondefault formatter flags are outside the
    ///   hypothesis.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::MintedAtomTable => "the minted-atom table",
            | Self::ErasureAnnotation => "the erasure annotation slot",
            | Self::ModeGradeAnnotation => "the modes-and-grades annotation slot",
            | Self::DirectednessVariance => "the directedness-and-variance annotation slot",
        })
    }
}

/// Where in the closed grammar an unknown tag byte was met.
///
/// # Specification
/// - requires: the value classifies a format refusal, not a typing judgement.
/// - ensures: retains the named refusal category and its declared payload so
///   distinct format causes remain observable.
/// - panics: none.
/// - executable: none — this closed classification is a data declaration;
///   reader operations select it and formatting exposes its payload.
///
/// # Adequacy
/// - hypothesis: L3 covers every refusal category and site, all tag-byte
///   spellings, version and quantity ceilings, the two sort literals, and
///   refusal by a real exhausted byte sink. It observes distinct causes,
///   complete numeric payloads and exact sink error kinds, separating collapsed
///   classifications, lost high bits and swallowed failures. Diagnostic wording
///   and nondefault formatter flags are outside the hypothesis.
/// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
    /// Writes the tag site's description.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one fixed description per variant.
    /// - provides: the rendering an unknown-tag refusal interpolates, so the
    ///   message says which alphabet the tag was read against.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   its output nor refusal state; observing those effects here would
    ///   require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers every refusal category and site, all tag-byte
    ///   spellings, version and quantity ceilings, the two sort literals, and
    ///   refusal by a real exhausted byte sink. It observes distinct causes,
    ///   complete numeric payloads and exact sink error kinds, separating
    ///   collapsed classifications, lost high bits and swallowed failures.
    ///   Diagnostic wording and nondefault formatter flags are outside the
    ///   hypothesis.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
///
/// # Specification
/// - requires: the value classifies a format refusal, not a typing judgement.
/// - ensures: retains the named refusal category and its declared payload so
///   distinct format causes remain observable.
/// - panics: none.
/// - executable: none — this closed classification is a data declaration;
///   reader operations select it and formatting exposes its payload.
///
/// # Adequacy
/// - hypothesis: L3 covers every refusal category and site, all tag-byte
///   spellings, version and quantity ceilings, the two sort literals, and
///   refusal by a real exhausted byte sink. It observes distinct causes,
///   complete numeric payloads and exact sink error kinds, separating collapsed
///   classifications, lost high bits and swallowed failures. Diagnostic wording
///   and nondefault formatter flags are outside the hypothesis.
/// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
    /// A structured-name segment was not UTF-8 or held the separator `.`, so it
    /// was not a segment a name can carry.
    NameSegment,
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
    /// Writes the malformed site's description.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one fixed description per variant.
    /// - provides: the rendering a malformed-artifact refusal interpolates, so
    ///   the message names the discipline the bytes broke.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   its output nor refusal state; observing those effects here would
    ///   require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers every refusal category and site, all tag-byte
    ///   spellings, version and quantity ceilings, the two sort literals, and
    ///   refusal by a real exhausted byte sink. It observes distinct causes,
    ///   complete numeric payloads and exact sink error kinds, separating
    ///   collapsed classifications, lost high bits and swallowed failures.
    ///   Diagnostic wording and nondefault formatter flags are outside the
    ///   hypothesis.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
            | Self::NameSegment => "a name segment was not UTF-8 or held the separator",
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
///
/// # Specification
/// - requires: the value classifies a format refusal, not a typing judgement.
/// - ensures: retains the named refusal category and its declared payload so
///   distinct format causes remain observable.
/// - panics: none.
/// - executable: none — this closed classification is a data declaration;
///   reader operations select it and formatting exposes its payload.
///
/// # Adequacy
/// - hypothesis: L3 covers every refusal category and site, all tag-byte
///   spellings, version and quantity ceilings, the two sort literals, and
///   refusal by a real exhausted byte sink. It observes distinct causes,
///   complete numeric payloads and exact sink error kinds, separating collapsed
///   classifications, lost high bits and swallowed failures. Diagnostic wording
///   and nondefault formatter flags are outside the hypothesis.
/// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
    /// Writes the decode failure's message.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one message per variant, interpolating the payload a
    ///   variant carries.
    /// - provides: the rendering [`core::error::Error`] reporting reads; the
    ///   message names the refusal rather than the byte offset, so it says
    ///   nothing an attacker could not already infer.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   its output nor refusal state; observing those effects here would
    ///   require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers every refusal category and site, all tag-byte
    ///   spellings, version and quantity ceilings, the two sort literals, and
    ///   refusal by a real exhausted byte sink. It observes distinct causes,
    ///   complete numeric payloads and exact sink error kinds, separating
    ///   collapsed classifications, lost high bits and swallowed failures.
    ///   Diagnostic wording and nondefault formatter flags are outside the
    ///   hypothesis.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
    extern crate std;

    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::DecodeError;
    use super::MalformedSite;
    use super::ReservedKind;
    use super::ReservedSlot;
    use super::TagSite;
    use crate::wire::FormatVersion;
    use crate::wire::WireTag;

    #[test]
    fn diagnostics_preserve_semantic_distinctions_and_sink_refusal()
    {
        let mut empty = [];
        let refusal = self::std::io::Write::write_all(&mut empty.as_mut_slice(), b"x")
            .expect_err("an exhausted byte sink refuses output")
            .kind();
        let check_sink = |value: &dyn core::fmt::Display| {
            let mut storage = [];
            let actual = self::std::io::Write::write_fmt(
                &mut storage.as_mut_slice(),
                format_args!("{value}"),
            )
            .expect_err("formatting propagates sink refusal");
            assert_eq!(refusal, actual.kind());
        };
        let distinct = |texts: Vec<String>| {
            for (index, text) in texts.iter().enumerate() {
                for other in texts.iter().skip(index.saturating_add(1)) {
                    assert_ne!(text, other, "different causes remain distinguishable");
                }
            }
        };
        let mut errors = vec![DecodeError::Truncated];
        let mut names = Vec::new();
        for kind in [
            ReservedKind::ModuleSig,
            ReservedKind::ModuleDef,
            ReservedKind::FunctorDef,
        ] {
            names.push(format!("{kind}"));
            check_sink(&kind);
            let error = DecodeError::ReservedDeclarationKind { kind };
            assert!(format!("{error}").contains(format!("{kind}").as_str()));
            errors.push(error);
        }
        distinct(names);
        let mut names = Vec::new();
        for slot in [
            ReservedSlot::MintedAtomTable,
            ReservedSlot::ErasureAnnotation,
            ReservedSlot::ModeGradeAnnotation,
            ReservedSlot::DirectednessVariance,
        ] {
            names.push(format!("{slot}"));
            check_sink(&slot);
            let error = DecodeError::ReservedSlotOccupied { slot };
            assert!(format!("{error}").contains(format!("{slot}").as_str()));
            errors.push(error);
        }
        distinct(names);
        let mut names = Vec::new();
        for site in [
            TagSite::Admission,
            TagSite::DeclarationKind,
            TagSite::Node,
            TagSite::BaseType,
            TagSite::Sign,
            TagSite::LiteralKind,
            TagSite::Side,
            TagSite::ConstraintRelation,
        ] {
            names.push(format!("{site}"));
            check_sink(&site);
            for byte in [0u8, 127, 128, 255] {
                let error = DecodeError::UnknownTag {
                    site,
                    tag: WireTag(byte),
                };
                let text = format!("{error}");
                assert!(text.contains(format!("{site}").as_str()));
                assert!(text.contains(format!("0x{byte:02x}").as_str()));
                errors.push(error);
            }
        }
        distinct(names);
        let mut names = Vec::new();
        for site in [
            MalformedSite::Header,
            MalformedSite::Varint,
            MalformedSite::IndexRange,
            MalformedSite::LevelOffset,
            MalformedSite::ConstraintForm,
            MalformedSite::LiteralPayload,
            MalformedSite::NameSegment,
            MalformedSite::Polarity,
            MalformedSite::ChildOrder,
            MalformedSite::TableSize,
            MalformedSite::ExpandedWork,
            MalformedSite::ArtifactExpandedWork,
            MalformedSite::NonCanonical,
            MalformedSite::TrailingBytes,
        ] {
            names.push(format!("{site}"));
            check_sink(&site);
            let error = DecodeError::Malformed { site };
            assert!(format!("{error}").contains(format!("{site}").as_str()));
            errors.push(error);
        }
        distinct(names);
        for version in [0u16, 1, u16::MAX] {
            let wrapped = FormatVersion(version);
            assert_eq!(format!("{version}"), format!("{wrapped}"));
            check_sink(&wrapped);
            let error = DecodeError::UnsupportedVersion { found: wrapped };
            assert!(format!("{error}").contains(format!("{version}").as_str()));
            errors.push(error);
        }
        let mut rendered = Vec::new();
        for error in errors {
            check_sink(&error);
            rendered.push(format!("{error}"));
        }
        distinct(rendered);
        for byte in 0u8 ..= u8::MAX {
            let tag = WireTag(byte);
            assert_eq!(format!("0x{byte:02x}"), format!("{tag}"));
            check_sink(&tag);
        }
        for quantity in [0u64, 1, u64::MAX] {
            let work = crate::ExpandedWork(quantity);
            assert_eq!(format!("{quantity}"), format!("{work}"));
            check_sink(&work);
        }
        for quantity in [0usize, 1, usize::MAX] {
            let count = crate::TableEntryCount(quantity);
            assert_eq!(format!("{quantity}"), format!("{count}"));
            check_sink(&count);
        }
        for (sort, literal) in [
            (crate::GroundSort::Value, "+"),
            (crate::GroundSort::Computation, "-"),
        ] {
            assert_eq!(literal, format!("{sort}"));
            check_sink(&sort);
        }
    }
}
