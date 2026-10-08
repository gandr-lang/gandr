//! The fixture value, its codec, and the helpers the area suites share.

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::EmissionFault;
use gandr_storage_values::SeamDepth;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueProfile;

/// The fixture's leaf constructor tag.
pub const LEAF: u8 = 0x11_u8;
/// The fixture's pair constructor tag.
pub const PAIR: u8 = 0x12_u8;
/// The embedding fixture's constructor tag.
pub const EMBED: u8 = 0x13_u8;

/// The depth of a balanced fixture: zero is a single leaf.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Depth(pub u32);

/// The seed a fixture's leaf words are drawn from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Seed(pub u64);

/// The preorder index of a leaf among a fixture's leaves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LeafIndex(pub usize);

/// A number of leaves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LeafCount(pub usize);

/// One node of a fixture tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Node
{
    /// A leaf carrying one word.
    Leaf(CanonicalWord),
    /// A pair: the next two subtrees in preorder are its children.
    Pair,
}

/// A binary tree held flat in preorder, so neither its type nor its codec
/// recurses.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fixture(pub Vec<Node>);

impl Fixture
{
    /// Counts the leaves.
    ///
    /// # Specification
    /// trivial.
    pub fn leaves(&self) -> LeafCount
    {
        LeafCount(
            self.0
                .iter()
                .filter(|node| matches!(node, Node::Leaf(_)))
                .count(),
        )
    }
}

impl CanonicalValue for Fixture
{
    /// Walks the preorder list, closing each pair once its second subtree has.
    ///
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let mut owed: Vec<u8> = Vec::new();

        for node in &self.0 {
            match *node {
                | Node::Pair => {
                    sink.open(ConstructorTag::from(PAIR))?;
                    owed.push(2_u8);
                    continue;
                },
                | Node::Leaf(word) => {
                    sink.open(ConstructorTag::from(LEAF))?;
                    sink.word(word)?;
                    sink.close()?;
                },
            }
            while let Some(children) = owed.last_mut() {
                *children = children.checked_sub(1).expect("an open pair owes a child");
                if *children > 0 {
                    break;
                }
                owed.pop();
                sink.close()?;
            }
        }

        Ok(())
    }

    /// Reads one fixture.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        decode_observed(reader, &mut |_reader: &TokenReader<'_>| {})
    }
}

/// Reads one fixture, showing the reader to `observe` after every record.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the fixture's decode, with `observe` called after each record.
/// - provides: a decode a probe can watch the seams of.
/// - panics: none.
pub fn decode_observed<Observe>(
    reader: &mut TokenReader<'_>,
    observe: &mut Observe,
) -> Result<Fixture, ValueError>
where
    Observe: FnMut(&TokenReader<'_>),
{
    let mut nodes = Vec::new();
    let mut owed: Vec<u8> = Vec::new();

    loop {
        let tag = reader.read_tag()?;
        observe(reader);
        match u8::from(tag) {
            | PAIR => {
                nodes.push(Node::Pair);
                owed.push(2_u8);
                continue;
            },
            | LEAF => {
                let word = reader.read_word()?;
                observe(reader);
                reader.read_close()?;
                observe(reader);
                nodes.push(Node::Leaf(word));
            },
            | _ => {
                return Err(ValueError::UnexpectedConstructor {
                    found: tag,
                    position: reader.position(),
                });
            },
        }
        loop {
            let Some(children) = owed.last_mut()
            else {
                return Ok(Fixture(nodes));
            };
            *children = children.checked_sub(1).expect("an open pair owes a child");
            if *children > 0 {
                break;
            }
            owed.pop();
            reader.read_close()?;
            observe(reader);
        }
    }
}

/// A fixture decoded with the deepest seam the reader was inside.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Probed
{
    /// The fixture.
    pub value: Fixture,
    /// The most seams the reader was inside at once.
    pub deepest: SeamDepth,
}

impl CanonicalValue for Probed
{
    /// Emits the fixture.
    ///
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        self.value.emit_tokens(sink)
    }

    /// Decodes the fixture, recording the deepest seam.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let mut deepest = reader.seam_depth();
        let value = decode_observed(reader, &mut |reader: &TokenReader<'_>| {
            deepest = deepest.max(reader.seam_depth());
        })?;

        Ok(Self { value, deepest })
    }
}

/// What an embedding holds: a committed pointer when written, the value it
/// names when read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Inner
{
    /// A pointer to an already-committed fixture.
    Pointer(ContentPtr),
    /// The fixture itself.
    Value(Fixture),
}

/// A one-constructor value around an embedded fixture.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Embedding(pub Inner);

impl CanonicalValue for Embedding
{
    /// Emits the embedding constructor around a child record or the fixture.
    ///
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(EMBED))?;
        match self.0 {
            | Inner::Pointer(pointer) => sink.child_pointer(pointer)?,
            | Inner::Value(ref value) => value.emit_tokens(sink)?,
        }
        sink.close()
    }

    /// Reads the embedding with its fixture inline.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let tag = reader.read_tag()?;
        if u8::from(tag) != EMBED {
            return Err(ValueError::UnexpectedConstructor {
                found: tag,
                position: reader.position(),
            });
        }
        let value = Fixture::decode_tokens(reader)?;
        reader.read_close()?;

        Ok(Self(Inner::Value(value)))
    }
}

/// One step of a scripted emission.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step
{
    /// Open a leaf constructor.
    Open,
    /// Emit a zero word.
    Word,
    /// Close the innermost constructor.
    Close,
}

/// A value whose emission is a script, balanced or not.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Script(pub Vec<Step>);

impl CanonicalValue for Script
{
    /// Plays the script into the sink.
    ///
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        for step in &self.0 {
            match *step {
                | Step::Open => sink.open(ConstructorTag::from(LEAF))?,
                | Step::Word => sink.word(CanonicalWord::from(0_u64))?,
                | Step::Close => sink.close()?,
            }
        }

        Ok(())
    }

    /// Never decodes: a script is only ever emitted.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens(_reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        Err(ValueError::MalformedEmission {
            fault: EmissionFault::EmptyValue,
        })
    }
}

/// Builds a balanced fixture whose leaf words are drawn from `seed`.
///
/// # Specification
/// trivial.
pub fn balanced(
    depth: Depth,
    seed: Seed,
) -> Fixture
{
    let mut nodes = Vec::new();
    let mut pending = vec![depth.0];
    let mut state = seed.0;

    while let Some(remaining) = pending.pop() {
        if remaining == 0 {
            // SplitMix64, so neighbouring leaves carry unrelated words.
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut mixed = state;
            mixed = (mixed ^ (mixed >> 30_u32)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            mixed = (mixed ^ (mixed >> 27_u32)).wrapping_mul(0x94D0_49BB_1331_11EB);
            nodes.push(Node::Leaf(CanonicalWord::from(mixed ^ (mixed >> 31_u32))));
        }
        else {
            nodes.push(Node::Pair);
            let child = remaining
                .checked_sub(1)
                .expect("a pair sits above depth zero");
            pending.push(child);
            pending.push(child);
        }
    }

    Fixture(nodes)
}

/// Pairs two fixtures under one pair constructor.
///
/// # Specification
/// trivial.
pub fn pair(
    left: &Fixture,
    right: &Fixture,
) -> Fixture
{
    let mut nodes = vec![Node::Pair];
    nodes.extend_from_slice(&left.0);
    nodes.extend_from_slice(&right.0);

    Fixture(nodes)
}

/// Returns the fixture with one leaf's word inverted.
///
/// # Specification
/// trivial.
pub fn edit_leaf(
    value: &Fixture,
    index: LeafIndex,
) -> Fixture
{
    let mut nodes = value.0.clone();
    let leaf = nodes
        .iter_mut()
        .filter_map(|node| match *node {
            | Node::Leaf(ref mut word) => Some(word),
            | Node::Pair => None,
        })
        .nth(index.0)
        .expect("the fixture has that many leaves");
    *leaf = CanonicalWord::from(!u64::from(*leaf));

    Fixture(nodes)
}

/// The profile the suite commits under: kappa four, cap sixty-four.
///
/// # Specification
/// trivial.
pub fn profile(base: ChildIndexBase) -> ValueProfile
{
    let params = TypedChunkerParams::new(
        Kappa::try_from(4_u64).expect("kappa is nonzero"),
        TokenCap::try_from(64_u64).expect("the cap is nonzero"),
    );
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));

    ValueProfile::new(params, codec, base)
}

/// One record of a body, as the layout documents it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Scanned
{
    /// An open record.
    Open,
    /// A child record.
    Child(ContentPtr),
    /// A word, bytes or close record.
    Other,
}

/// Splits a body into its records by the documented layout, independently of
/// the crate's own reader.
///
/// # Specification
/// trivial.
pub fn scan(body: TokenBody<'_>) -> Vec<Scanned>
{
    let mut rest: &[u8] = body.into();
    let mut records = Vec::new();

    while let Some((&kind, after)) = rest.split_first() {
        let (record, length) = match kind {
            | 0x01 => (Scanned::Open, 1_usize),
            | 0x02 => (Scanned::Other, 8_usize),
            | 0x03 => {
                let declared = after.first_chunk::<8>().expect("a bytes length");
                let payload =
                    usize::try_from(u64::from_le_bytes(*declared)).expect("a fixture length");
                (
                    Scanned::Other,
                    payload.checked_add(8_usize).expect("a fixture length"),
                )
            },
            | 0x04 => {
                let digest = after.first_chunk::<32>().expect("a child digest");
                let offset = after
                    .get(32 ..)
                    .and_then(<[u8]>::first_chunk::<4>)
                    .expect("a child offset");
                let pointer = ContentPtr::new(
                    ChunkDigest::from(*digest),
                    TokenOffset::from(u32::from_le_bytes(*offset)),
                );
                (Scanned::Child(pointer), 36_usize)
            },
            | 0x05 => (Scanned::Other, 0_usize),
            | other => panic!("a fixture body holds no record kind {other:#04x}"),
        };
        records.push(record);
        rest = after.get(length ..).expect("a whole record");
    }

    records
}
