//! The one canonical byte form of an entry, and its bounded reader.
//!
//! An [`Entry`] is a [`Record`] beside the digest of each source file that
//! the reader read. The form is the header, then each source, then the
//! identity, then the outcome. Each integer is little-endian at a fixed
//! width: a tag is one byte, a count or a length eight bytes, a size eight
//! bytes and a niche's count sixteen bytes. A text is its length, then its
//! UTF-8 bytes.
//!
//! [`Entry::decode`] reads the form back. Each count and each length is
//! bounded by the bytes that remain, so a hostile count allocates nothing
//! past the input. Each tag names one variant, each text is UTF-8, a refused
//! outcome names at least one refusal, and no byte follows the entry. So one
//! entry has one form, and a decode then an encode gives the same bytes.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::names::Available;
use crate::names::Bytes;
use crate::names::Commit;
use crate::names::FieldName;
use crate::names::FunctionPath;
use crate::names::LlvmType;
use crate::names::Offset;
use crate::names::SourcePath;
use crate::names::Symbol;
use crate::names::Target;
use crate::names::TypeName;
use crate::names::VariantName;
use crate::record::Arm;
use crate::record::Discriminant;
use crate::record::Extension;
use crate::record::Field;
use crate::record::Function;
use crate::record::Identity;
use crate::record::Layout;
use crate::record::Niche;
use crate::record::Operand;
use crate::record::Outcome;
use crate::record::Part;
use crate::record::Passage;
use crate::record::Record;
use crate::record::Refusal;
use crate::record::Shape;
use crate::record::Unstatable;

/// The first bytes of each entry: the name of the form and its version.
const HEADER: &[u8] = b"gandr-rust-record\x01";

/// A borrowed run of bytes that a decoder reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Encoded<'bytes>(pub &'bytes [u8]);

/// The canonical bytes of one entry.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Canonical(Vec<u8>);

impl Canonical
{
    /// The bytes, borrowed for a decoder or a writer.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn as_encoded(&self) -> Encoded<'_>
    {
        Encoded(&self.0)
    }
}

/// The BLAKE3 digest of a source file's bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Digest([u8; 32]);

impl Digest
{
    /// The digest of `contents`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn of(contents: Encoded<'_>) -> Self
    {
        Self(*blake3::hash(contents.0).as_bytes())
    }
}

/// A source file that the reader read, and the digest of the bytes that it
/// read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceFile
{
    /// The file's path.
    pub path: SourcePath,
    /// The digest of the bytes that the reader compiled.
    pub digest: Digest,
}

/// A record beside the source files that its reader read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// Each source file that the reader read, in the order that it read
    /// them.
    pub sources: Vec<SourceFile>,
    /// The record.
    pub record: Record,
}

/// Why bytes are not an entry for the expected identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Undecoded
{
    /// The bytes do not start with the header of this form and its version.
    Header,
    /// The bytes end before the value at the offset.
    Truncated(Offset),
    /// The tag at the offset names no variant of its place.
    Tag(Offset),
    /// The text at the offset is not UTF-8.
    Text(Offset),
    /// The refused outcome at the offset names no refusal.
    Empty(Offset),
    /// Bytes follow the entry, from the offset.
    Trailing(Offset),
    /// Another toolchain wrote the record.
    Toolchain(Commit),
    /// The record is for another target.
    Target(Target),
}

impl fmt::Display for Undecoded
{
    /// Names the cause and, where it has one, the offset.
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
            Self::Header => f.write_str("the bytes are not a record of this form"),
            Self::Truncated(at) => write!(f, "the record ends before the value at byte {at}"),
            Self::Tag(at) => write!(f, "the tag at byte {at} names no variant"),
            Self::Text(at) => write!(f, "the text at byte {at} is not UTF-8"),
            Self::Empty(at) => write!(f, "the refused outcome at byte {at} names no refusal"),
            Self::Trailing(at) => write!(f, "bytes follow the record from byte {at}"),
            Self::Toolchain(ref commit) => {
                write!(f, "the toolchain at commit {commit} wrote the record")
            },
            Self::Target(ref target) => write!(f, "the record is for the target {target}"),
        }
    }
}

impl Entry
{
    /// The entry's one canonical byte form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Entry::decode`] of the bytes, under the entry's own
    ///   identity, gives the entry back; equal entries give equal bytes.
    /// - provides: the bytes that the reader writes and the cache keeps.
    /// - fails: nothing.
    /// - panics: none.
    /// - executable: none — the inverse is the decoder, which the witness runs.
    ///
    /// # Cost
    /// - allocation: the canonical bytes, growth within the entry
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a round trip through the decoder over an entry that
    ///   holds each variant of each tag gives the entry and the same bytes.
    /// - witness: `tests::each_variant_round_trips_through_its_bytes`
    #[must_use]
    #[inline]
    pub fn encode(&self) -> Canonical
    {
        let mut writer = Writer {
            bytes: Vec::from(HEADER),
        };
        writer.count(Count(self.sources.len()));
        for source in &self.sources {
            writer.text(Text(source.path.as_ref()));
            writer.bytes.extend_from_slice(&source.digest.0);
        }
        writer.text(Text(self.record.identity.commit.as_ref()));
        writer.text(Text(self.record.identity.target.as_ref()));
        match self.record.outcome {
            Outcome::Read(ref functions) => {
                writer.tag(Tag::READ);
                writer.count(Count(functions.len()));
                for function in functions {
                    writer.function(function);
                }
            },
            Outcome::Refused(ref refusals) => {
                writer.tag(Tag::REFUSED);
                writer.count(Count(refusals.len()));
                for refusal in refusals {
                    writer.refusal(refusal);
                }
            },
        }
        Canonical(writer.bytes)
    }

    /// Reads an entry from its canonical bytes, and refuses a record of
    /// another toolchain or of another target than `expected`.
    ///
    /// # Specification
    /// - requires: nothing; any bytes are an input.
    /// - ensures: on success the bytes are the canonical form of the entry, and
    ///   the record's identity equals `expected`.
    /// - fails: [`Undecoded`] with the first fault in the order of the bytes;
    ///   an identity that differs from `expected` fails after the whole entry
    ///   reads, with [`Undecoded::Toolchain`] before [`Undecoded::Target`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Undecoded`], as above.
    ///
    /// # Cost
    /// - allocation: the decoded entry, growth within the length of the bytes
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each proper prefix of an entry's bytes is truncated,
    ///   a byte past the end is trailing, a tag past its variants is refused at
    ///   its offset, a text that is not UTF-8 is refused, a count past the
    ///   bytes allocates nothing and is truncated, an empty refusal list is
    ///   refused, and another commit or target is refused by its name.
    /// - witness: `tests::each_proper_prefix_is_truncated`
    /// - witness: `tests::a_byte_past_the_end_is_trailing`
    /// - witness: `tests::a_tag_past_its_variants_is_refused_at_its_offset`
    /// - witness: `tests::text_that_is_not_utf8_is_refused`
    /// - witness: `tests::a_count_past_the_bytes_is_truncated`
    /// - witness: `tests::a_refused_outcome_with_no_refusal_is_refused`
    /// - witness: `tests::another_toolchain_or_target_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entry| entry.record.identity == *expected))]
    #[inline]
    pub fn decode(
        bytes: Encoded<'_>,
        expected: &Identity,
    ) -> Result<Self, Undecoded>
    {
        if !bytes.0.starts_with(HEADER) {
            return Err(Undecoded::Header);
        }
        let mut reader = Reader {
            bytes: bytes.0,
            at: HEADER.len(),
        };
        let count = reader.count()?;
        let mut sources = Vec::new();
        for _ in 0 .. count.0 {
            let path = SourcePath::from(reader.text()?);
            let digest = reader.digest()?;
            sources.push(SourceFile { path, digest });
        }
        let commit = Commit::from(reader.text()?);
        let target = Target::from(reader.text()?);
        let at = reader.offset();
        let outcome = match reader.tag()? {
            Tag::READ => {
                let count = reader.count()?;
                let mut functions = Vec::new();
                for _ in 0 .. count.0 {
                    functions.push(reader.function()?);
                }
                Outcome::Read(functions)
            },
            Tag::REFUSED => {
                let count = reader.count()?;
                if count.0 == 0 {
                    return Err(Undecoded::Empty(at));
                }
                let mut refusals = Vec::new();
                for _ in 0 .. count.0 {
                    refusals.push(reader.refusal()?);
                }
                Outcome::Refused(refusals)
            },
            Tag(_) => return Err(Undecoded::Tag(at)),
        };
        if reader.at != reader.bytes.len() {
            return Err(Undecoded::Trailing(reader.offset()));
        }
        if commit != expected.commit {
            return Err(Undecoded::Toolchain(commit));
        }
        if target != expected.target {
            return Err(Undecoded::Target(target));
        }
        Ok(Self {
            sources,
            record: Record {
                identity: Identity { commit, target },
                outcome,
            },
        })
    }
}

/// One tag byte: which variant of its place a value is.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Tag(u8);

impl Tag
{
    /// An outcome that reads each function.
    const READ: Self = Self(0);
    /// An outcome that refuses.
    const REFUSED: Self = Self(1);
}

/// A count of values or a length of text, as the platform counts it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Count(usize);

/// The text of a name, as the form holds it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Text<'text>(&'text str);

/// A run of bytes of a fixed width.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Chunk<const WIDTH: usize>([u8; WIDTH]);

/// The canonical bytes as the encoder appends them.
#[repr(transparent)]
struct Writer
{
    /// The bytes so far.
    bytes: Vec<u8>,
}

impl Writer
{
    /// Appends one tag.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the tag's byte, growth within the entry
    fn tag(
        &mut self,
        tag: Tag,
    )
    {
        self.bytes.push(tag.0);
    }

    /// Appends a count or a length.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the count's eight bytes, growth within the entry
    fn count(
        &mut self,
        count: Count,
    )
    {
        self.bytes
            .extend_from_slice(&u64::try_from(count.0).unwrap_or(u64::MAX).to_le_bytes());
    }

    /// Appends a size, an offset or an alignment.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the size's eight bytes, growth within the entry
    fn size(
        &mut self,
        size: Bytes,
    )
    {
        self.bytes.extend_from_slice(&u64::from(size).to_le_bytes());
    }

    /// Appends a text: its length, then its bytes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the text's length and bytes, growth within the entry
    fn text(
        &mut self,
        text: Text<'_>,
    )
    {
        self.count(Count(text.0.len()));
        self.bytes.extend_from_slice(text.0.as_bytes());
    }

    /// Appends one function.
    ///
    /// # Specification
    /// trivial.
    fn function(
        &mut self,
        function: &Function,
    )
    {
        self.text(Text(function.path.as_ref()));
        self.text(Text(function.symbol.as_ref()));
        self.count(Count(function.arguments.len()));
        for argument in &function.arguments {
            self.operand(argument);
        }
        self.operand(&function.result);
    }

    /// Appends one operand: its passage, then its layout.
    ///
    /// # Specification
    /// trivial.
    fn operand(
        &mut self,
        operand: &Operand,
    )
    {
        match operand.passage {
            Passage::Ignore => self.tag(Tag(0)),
            Passage::Direct(ref part) => {
                self.tag(Tag(1));
                self.part(part);
            },
            Passage::Pair(ref first, ref second) => {
                self.tag(Tag(2));
                self.part(first);
                self.part(second);
            },
            Passage::Cast(ref part) => {
                self.tag(Tag(3));
                self.part(part);
            },
            Passage::Indirect(ref part) => {
                self.tag(Tag(4));
                self.part(part);
            },
            Passage::OnStack(ref part) => {
                self.tag(Tag(5));
                self.part(part);
            },
        }
        self.layout(&operand.layout);
    }

    /// Appends one part of a passage: its type, then its extension.
    ///
    /// # Specification
    /// trivial.
    fn part(
        &mut self,
        part: &Part,
    )
    {
        self.text(Text(part.ty.as_ref()));
        self.tag(match part.extension {
            Extension::Plain => Tag(0),
            Extension::Zero => Tag(1),
            Extension::Sign => Tag(2),
        });
    }

    /// Appends one layout.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the niche's count of available values, growth within the
    ///   entry
    fn layout(
        &mut self,
        layout: &Layout,
    )
    {
        self.text(Text(layout.ty.as_ref()));
        self.size(layout.size);
        self.size(layout.stride);
        self.size(layout.align);
        match layout.niche {
            Niche::None => self.tag(Tag(0)),
            Niche::At {
                offset,
                width,
                available,
            } => {
                self.tag(Tag(1));
                self.size(offset);
                self.size(width);
                self.bytes
                    .extend_from_slice(&u128::from(available).to_le_bytes());
            },
        }
        match layout.shape {
            Shape::Scalar => self.tag(Tag(0)),
            Shape::Struct(ref fields) => {
                self.tag(Tag(1));
                self.fields(fields);
            },
            Shape::Enum {
                discriminant,
                ref arms,
            } => {
                self.tag(Tag(2));
                match discriminant {
                    Discriminant::Unneeded => self.tag(Tag(0)),
                    Discriminant::Niche { offset } => {
                        self.tag(Tag(1));
                        self.size(offset);
                    },
                    Discriminant::Tag { offset, size } => {
                        self.tag(Tag(2));
                        self.size(offset);
                        self.size(size);
                    },
                }
                self.count(Count(arms.len()));
                for arm in arms {
                    self.text(Text(arm.name.as_ref()));
                    self.fields(&arm.fields);
                }
            },
        }
    }

    /// Appends a list of fields.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        &mut self,
        fields: &[Field],
    )
    {
        self.count(Count(fields.len()));
        for field in fields {
            self.text(Text(field.name.as_ref()));
            self.size(field.offset);
        }
    }

    /// Appends one refusal.
    ///
    /// # Specification
    /// trivial.
    fn refusal(
        &mut self,
        refusal: &Refusal,
    )
    {
        match *refusal {
            Refusal::Generic(ref path) => {
                self.tag(Tag(0));
                self.text(Text(path.as_ref()));
            },
            Refusal::NotPublic(ref path) => {
                self.tag(Tag(1));
                self.text(Text(path.as_ref()));
            },
            Refusal::Missing(ref path) => {
                self.tag(Tag(2));
                self.text(Text(path.as_ref()));
            },
            Refusal::Inlined(ref path) => {
                self.tag(Tag(3));
                self.text(Text(path.as_ref()));
            },
            Refusal::Unstated {
                ref function,
                ref ty,
                why,
            } => {
                self.tag(Tag(4));
                self.text(Text(function.as_ref()));
                self.text(Text(ty.as_ref()));
                self.tag(match why {
                    Unstatable::Unsized => Tag(0),
                    Unstatable::Uninhabited => Tag(1),
                    Unstatable::Array => Tag(2),
                    Unstatable::Union => Tag(3),
                    Unstatable::Passage => Tag(4),
                });
            },
        }
    }
}

/// The bytes of an entry, read from the front, each read bounded by the
/// bytes that remain.
struct Reader<'bytes>
{
    /// The whole input.
    bytes: &'bytes [u8],
    /// The offset of the next unread byte.
    at: usize,
}

impl Reader<'_>
{
    /// The offset of the next unread byte.
    ///
    /// # Specification
    /// trivial.
    fn offset(&self) -> Offset
    {
        Offset::from(u64::try_from(self.at).unwrap_or(u64::MAX))
    }

    /// The next `width` bytes, or a truncation at the offset.
    ///
    /// # Specification
    /// trivial.
    fn take<const WIDTH: usize>(&mut self) -> Result<Chunk<WIDTH>, Undecoded>
    {
        let at = self.offset();
        let chunk = self
            .bytes
            .get(self.at ..)
            .and_then(|rest| rest.first_chunk::<WIDTH>())
            .ok_or(Undecoded::Truncated(at))?;
        self.at = self.at.saturating_add(WIDTH);
        Ok(Chunk(*chunk))
    }

    /// The next tag.
    ///
    /// # Specification
    /// trivial.
    fn tag(&mut self) -> Result<Tag, Undecoded>
    {
        let Chunk([byte]) = self.take::<1>()?;
        Ok(Tag(byte))
    }

    /// The next count or length, bounded by the bytes that remain: each
    /// counted value takes at least one byte.
    ///
    /// # Specification
    /// trivial.
    fn count(&mut self) -> Result<Count, Undecoded>
    {
        let at = self.offset();
        let count = u64::from_le_bytes(self.take::<8>()?.0);
        let remaining = self.bytes.len().saturating_sub(self.at);
        match usize::try_from(count) {
            Ok(count) if count <= remaining => Ok(Count(count)),
            Ok(_) | Err(_) => Err(Undecoded::Truncated(at)),
        }
    }

    /// The next size, offset or alignment.
    ///
    /// # Specification
    /// trivial.
    fn size(&mut self) -> Result<Bytes, Undecoded>
    {
        Ok(Bytes::from(u64::from_le_bytes(self.take::<8>()?.0)))
    }

    /// The next digest.
    ///
    /// # Specification
    /// trivial.
    fn digest(&mut self) -> Result<Digest, Undecoded>
    {
        Ok(Digest(self.take::<32>()?.0))
    }

    /// The next text.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the copy of the text, durable by the decoded entry
    fn text(&mut self) -> Result<String, Undecoded>
    {
        let at = self.offset();
        let length = self.count()?;
        let end = self.at.saturating_add(length.0);
        let raw = self
            .bytes
            .get(self.at .. end)
            .ok_or(Undecoded::Truncated(at))?;
        let Ok(text) = core::str::from_utf8(raw)
        else {
            return Err(Undecoded::Text(at));
        };
        self.at = end;
        Ok(String::from(text))
    }

    /// The next extension.
    ///
    /// # Specification
    /// trivial.
    fn extension(&mut self) -> Result<Extension, Undecoded>
    {
        let at = self.offset();
        match self.tag()? {
            Tag(0) => Ok(Extension::Plain),
            Tag(1) => Ok(Extension::Zero),
            Tag(2) => Ok(Extension::Sign),
            Tag(_) => Err(Undecoded::Tag(at)),
        }
    }

    /// The next part of a passage.
    ///
    /// # Specification
    /// trivial.
    fn part(&mut self) -> Result<Part, Undecoded>
    {
        let ty = LlvmType::from(self.text()?);
        let extension = self.extension()?;
        Ok(Part { ty, extension })
    }

    /// The next function.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the arguments, growth within the length of the bytes
    fn function(&mut self) -> Result<Function, Undecoded>
    {
        let path = FunctionPath::from(self.text()?);
        let symbol = Symbol::from(self.text()?);
        let count = self.count()?;
        let mut arguments = Vec::new();
        for _ in 0 .. count.0 {
            arguments.push(self.operand()?);
        }
        let result = self.operand()?;
        Ok(Function {
            path,
            symbol,
            arguments,
            result,
        })
    }

    /// The next operand.
    ///
    /// # Specification
    /// trivial.
    fn operand(&mut self) -> Result<Operand, Undecoded>
    {
        let at = self.offset();
        let passage = match self.tag()? {
            Tag(0) => Passage::Ignore,
            Tag(1) => Passage::Direct(self.part()?),
            Tag(2) => {
                let first = self.part()?;
                Passage::Pair(first, self.part()?)
            },
            Tag(3) => Passage::Cast(self.part()?),
            Tag(4) => Passage::Indirect(self.part()?),
            Tag(5) => Passage::OnStack(self.part()?),
            Tag(_) => return Err(Undecoded::Tag(at)),
        };
        let layout = self.layout()?;
        Ok(Operand { passage, layout })
    }

    /// The next layout.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the arms of an enum, growth within the length of the bytes
    fn layout(&mut self) -> Result<Layout, Undecoded>
    {
        let ty = TypeName::from(self.text()?);
        let size = self.size()?;
        let stride = self.size()?;
        let align = self.size()?;
        let at = self.offset();
        let niche = match self.tag()? {
            Tag(0) => Niche::None,
            Tag(1) => {
                let offset = self.size()?;
                let width = self.size()?;
                let available = Available::from(u128::from_le_bytes(self.take::<16>()?.0));
                Niche::At {
                    offset,
                    width,
                    available,
                }
            },
            Tag(_) => return Err(Undecoded::Tag(at)),
        };
        let at = self.offset();
        let shape = match self.tag()? {
            Tag(0) => Shape::Scalar,
            Tag(1) => Shape::Struct(self.fields()?),
            Tag(2) => {
                let at = self.offset();
                let discriminant = match self.tag()? {
                    Tag(0) => Discriminant::Unneeded,
                    Tag(1) => Discriminant::Niche {
                        offset: self.size()?,
                    },
                    Tag(2) => {
                        let offset = self.size()?;
                        Discriminant::Tag {
                            offset,
                            size: self.size()?,
                        }
                    },
                    Tag(_) => return Err(Undecoded::Tag(at)),
                };
                let count = self.count()?;
                let mut arms = Vec::new();
                for _ in 0 .. count.0 {
                    let name = VariantName::from(self.text()?);
                    arms.push(Arm {
                        name,
                        fields: self.fields()?,
                    });
                }
                Shape::Enum { discriminant, arms }
            },
            Tag(_) => return Err(Undecoded::Tag(at)),
        };
        Ok(Layout {
            ty,
            size,
            stride,
            align,
            niche,
            shape,
        })
    }

    /// The next list of fields.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the fields, growth within the length of the bytes
    fn fields(&mut self) -> Result<Vec<Field>, Undecoded>
    {
        let count = self.count()?;
        let mut fields = Vec::new();
        for _ in 0 .. count.0 {
            let name = FieldName::from(self.text()?);
            fields.push(Field {
                name,
                offset: self.size()?,
            });
        }
        Ok(fields)
    }

    /// The next refusal.
    ///
    /// # Specification
    /// trivial.
    fn refusal(&mut self) -> Result<Refusal, Undecoded>
    {
        let at = self.offset();
        match self.tag()? {
            Tag(0) => Ok(Refusal::Generic(FunctionPath::from(self.text()?))),
            Tag(1) => Ok(Refusal::NotPublic(FunctionPath::from(self.text()?))),
            Tag(2) => Ok(Refusal::Missing(FunctionPath::from(self.text()?))),
            Tag(3) => Ok(Refusal::Inlined(FunctionPath::from(self.text()?))),
            Tag(4) => {
                let function = FunctionPath::from(self.text()?);
                let ty = TypeName::from(self.text()?);
                let at = self.offset();
                let why = match self.tag()? {
                    Tag(0) => Unstatable::Unsized,
                    Tag(1) => Unstatable::Uninhabited,
                    Tag(2) => Unstatable::Array,
                    Tag(3) => Unstatable::Union,
                    Tag(4) => Unstatable::Passage,
                    Tag(_) => return Err(Undecoded::Tag(at)),
                };
                Ok(Refusal::Unstated { function, ty, why })
            },
            Tag(_) => Err(Undecoded::Tag(at)),
        }
    }
}
