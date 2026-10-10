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
///
/// # Specification
/// - requires: nothing.
/// - ensures: the preorder nodes fill exactly one binary tree: every pair owes
///   two children, each leaf owes none, and no second root follows.
/// - provides: structural admission for the fixture codec.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes a leaf and an asymmetric tree from empty,
///   unfinished and multiple-root lists; codec goldens bind preorder to bytes.
/// - witness: `tests::common::fixture_refinements_reject_invalid_roots`
/// - witness: `tests::common::fixture_edits_preserve_preorder`
#[anodized::spec(maintains: self.0.iter().try_fold(1_usize, |owed, node| {
    let remaining = owed.checked_sub(1_usize)?;
    match *node {
        Node::Pair => remaining.checked_add(2_usize),
        Node::Leaf(_) => Some(remaining),
    }
}) == Some(0_usize))]
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fixture(pub Vec<Node>);

impl Fixture
{
    /// Counts the leaves.
    ///
    /// # Specification
    /// - requires: this is one complete fixture tree.
    /// - ensures: counts its leaf nodes; a full binary tree has one more leaf
    ///   than pair, so the result is half the node count rounded upward.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers a leaf, asymmetric three-leaf tree and balanced
    ///   depths zero through eight used by the locality witnesses.
    /// - witness: `tests::common::fixture_edits_preserve_preorder`
    /// - witness: `tests::common::fixture_refinements_reject_invalid_roots`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self),
        ensures: |ret| ret.0 == self.0.len().div_ceil(2_usize))]
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
    /// - requires: the preorder list is one complete fixture tree.
    /// - ensures: emits each pair open and its two subtrees, then its close;
    ///   each leaf emits its tag, word and close. Sink errors stop emission.
    /// - fails: propagates the first sink refusal.
    /// - panics: propagates a sink panic.
    ///
    /// # Errors
    /// The first error returned by the sink, without undoing earlier records.
    ///
    /// # Adequacy
    /// - hypothesis: L3 checks literal bytes for an asymmetric three-leaf tree
    ///   and the first, middle and last leaf edits. Bounded generated trees
    ///   additionally exercise nested closing through real flat and DAG codecs.
    /// - witness: `tests::common::fixture_edits_preserve_preorder`
    /// - witness: `tests::flat::a_flat_form_round_trips`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self))]
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
/// - requires: nothing; malformed input is admitted for refusal.
/// - ensures: on success returns one complete fixture and advances the reader;
///   invokes the observer after every successfully read record, including the
///   unexpected tag when a constructor is refused.
/// - provides: fixture decoding with observable seam transitions.
/// - fails: propagates reader errors or refuses an unknown fixture constructor.
/// - panics: propagates a panic from the observer.
///
/// # Errors
/// Reader errors and unexpected fixture constructor tags.
///
/// # Adequacy
/// - hypothesis: L3 observes all three leaf records through two nested seams,
///   including the final return to the outer source; literal asymmetric bytes
///   and flat prefix refusals distinguish codec order and premature completion.
/// - witness: `tests::common::record_observers_preserve_nested_seams`
/// - witness: `tests::common::fixture_edits_preserve_preorder`
/// - witness: `tests::flat::a_truncated_flat_form_is_refused`
#[anodized::spec(captures: spent = reader.spent(), ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|value| anodized::types::Spec::predicate(value)
        && reader.spent() > spent))]
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: the decoded fixture is complete. The deepest seam is historical
///   evidence, not reconstructible from the decoded tree alone.
/// - provides: a logical fixture with its observed maximum seam depth.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 a leaf under two pointer-only chunks preserves the fixture
///   while recording depth two rather than the final depth zero.
/// - witness: `tests::common::record_observers_preserve_nested_seams`
#[anodized::spec(maintains: anodized::types::Spec::predicate(&self.value))]
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
    /// - requires: input follows the fixture codec or is admitted for refusal.
    /// - ensures: returns a complete fixture and the greatest seam depth seen
    ///   at entry or after any record read while decoding it.
    /// - fails: propagates reader and fixture-codec errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Reader errors and unexpected fixture constructor tags.
    ///
    /// # Adequacy
    /// - hypothesis: L3 two nested seams reach depth two but finish at zero;
    ///   the observed maximum must survive the return to the outer source.
    /// - witness: `tests::common::record_observers_preserve_nested_seams`
    #[anodized::spec(captures: depth = reader.seam_depth(),
        ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|value|
            anodized::types::Spec::predicate(value) && value.deepest >= depth))]
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
    /// - requires: an inline fixture is complete; pointer claims are admitted
    ///   for the sink to accept or refuse.
    /// - ensures: emits an embedding open, then its child or inline fixture,
    ///   then the close, stopping at the first sink error.
    /// - fails: propagates the sink or inline fixture's first refusal.
    /// - panics: propagates a sink panic.
    ///
    /// # Errors
    /// Sink and inline fixture emission errors.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares an inline embedding with literal bytes and
    ///   refuses a pointer in a flat form; DAG reuse is covered by the bounded
    ///   generated histories, with zero through six prior values.
    /// - witness: `tests::common::fixture_edits_preserve_preorder`
    /// - witness: `tests::flat::a_child_record_is_refused_in_a_flat_form`
    #[anodized::spec(requires: match self.0 {
        Inner::Pointer(_) => true,
        Inner::Value(ref value) => anodized::types::Spec::predicate(value),
    })]
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
    /// - requires: malformed input is admitted for refusal.
    /// - ensures: reads the embedding tag, one complete fixture and the close;
    ///   returns the inline value variant, never a pointer representation.
    /// - fails: refuses another outer tag or propagates reader/fixture errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Reader errors and unexpected embedding or fixture constructor tags.
    ///
    /// # Adequacy
    /// - hypothesis: L3 literal inline embedding bytes recover the exact child;
    ///   replacing the outer tag refuses before decoding the child.
    /// - witness: `tests::common::fixture_edits_preserve_preorder`
    #[anodized::spec(captures: spent = reader.spent(), ensures: |ret| ret.is_err()
        || ret.as_ref().is_ok_and(|value| reader.spent() > spent && match value.0 {
            Inner::Value(ref fixture) => anodized::types::Spec::predicate(fixture),
            Inner::Pointer(_) => false,
        }))]
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
    /// - requires: nothing; deliberately malformed scripts are admitted.
    /// - ensures: attempts the scripted records in order, stopping at the first
    ///   sink error without undoing earlier effects. An empty script succeeds
    ///   without invoking the sink.
    /// - fails: propagates the first sink refusal.
    /// - panics: propagates a sink panic.
    ///
    /// # Errors
    /// The first error returned by the sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a valid leaf script has fixed bytes; six malformed
    ///   scripts, including the zero-step boundary, exercise real flat and
    ///   committing sinks rather than a mock. The postcondition checks the
    ///   empty script without replaying observable sink effects.
    /// - witness: `tests::common::fixture_edits_preserve_preorder`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    #[anodized::spec(ensures: |ret| !self.0.is_empty() || ret.is_ok())]
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
/// - requires: depth is below the host word width and the full tree fits in
///   available memory.
/// - ensures: returns a complete balanced tree with exactly two to the depth
///   leaves, drawing reproducible leaf words from the supplied seed.
/// - fails: never.
/// - panics: none within the admitted capacity.
///
/// # Adequacy
/// - hypothesis: L3 depths zero through eight cover leaf and branching shapes;
///   fixed-seed replay and a neighbouring seed distinguish ignored seed input.
/// - witness: `tests::common::fixture_refinements_reject_invalid_roots`
#[anodized::spec(requires: depth.0 < usize::BITS,
    ensures: |ret| anodized::types::Spec::predicate(&ret)
        && Some(ret.leaves().0) == 1_usize.checked_shl(depth.0))]
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
/// - requires: both children are complete fixture trees.
/// - ensures: the result is one pair followed by the left and right preorder
///   lists, preserving their order and payloads.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 pairing a leaf on the left and a pair on the right yields
///   literal asymmetric codec bytes, distinguishing swapped children.
/// - witness: `tests::common::fixture_edits_preserve_preorder`
#[anodized::spec(requires: anodized::types::Spec::predicate(left)
    && anodized::types::Spec::predicate(right),
    ensures: |ret| anodized::types::Spec::predicate(&ret)
        && ret.0.iter().eq(core::iter::once(&Node::Pair)
            .chain(left.0.iter()).chain(right.0.iter())))]
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
/// - requires: the fixture is complete and the leaf index is in bounds.
/// - ensures: preserves the preorder shape and every other payload, replacing
///   exactly the selected leaf word with its bitwise complement.
/// - fails: never.
/// - panics: when the leaf index is outside the admitted range.
///
/// # Adequacy
/// - hypothesis: L3 first, middle and last leaves of an asymmetric tree have
///   distinct words; exact edited fixtures distinguish node and leaf indexing.
/// - witness: `tests::common::fixture_edits_preserve_preorder`
#[anodized::spec(requires: anodized::types::Spec::predicate(value)
    && index.0 < value.leaves().0, ensures: |ret| {
        let mut leaf = 0_usize;
        ret.0.len() == value.0.len()
            && ret.0.iter().zip(&value.0).all(|(edited, original)| {
                match (*edited, *original) {
                    (Node::Pair, Node::Pair) => true,
                    (Node::Leaf(edited), Node::Leaf(original)) => {
                        let selected = leaf == index.0;
                        leaf = leaf.saturating_add(1_usize);
                        u64::from(edited) == if selected {
                            !u64::from(original)
                        } else {
                            u64::from(original)
                        }
                    },
                    _ => false,
                }
            })
    })]
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
/// - requires: bytes are whole records in the documented layout, with payload
///   lengths fitting the host word width.
/// - ensures: returns the record classes in order, preserving each child's
///   complete digest and little-endian offset; consumes the entire body.
/// - fails: never within the admitted byte language.
/// - panics: on an unknown kind, truncation or unrepresentable payload length.
///
/// # Adequacy
/// - hypothesis: L3 one literal body contains every record kind, a binary
///   payload, a nonzero child digest and an asymmetric multibyte offset.
/// - witness: `tests::common::the_reference_scanner_covers_each_wire_record`
#[anodized::spec(ensures: |ret| ret.iter().try_fold(<&[u8]>::from(body),
    |remaining, record| {
        let (&kind, after) = remaining.split_first()?;
        match (*record, kind) {
            (Scanned::Open, 0x01) => after.get(1 ..),
            (Scanned::Other, 0x02) => after.get(8 ..),
            (Scanned::Other, 0x03) => {
                let length = usize::try_from(u64::from_le_bytes(
                    *after.first_chunk::<8>()?)).ok()?;
                after.get(8_usize.checked_add(length)? ..)
            },
            (Scanned::Child(pointer), 0x04)
                if after.first_chunk::<32>().is_some_and(|digest|
                    pointer.digest() == ChunkDigest::from(*digest))
                && after.get(32 ..).and_then(<[u8]>::first_chunk::<4>)
                    .is_some_and(|offset| pointer.offset()
                        == TokenOffset::from(u32::from_le_bytes(*offset))) =>
            {
                after.get(36 ..)
            },
            (Scanned::Other, 0x05) => Some(after),
            _ => None,
        }
    }).is_some_and(<[u8]>::is_empty))]
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

/// A decoded fixture with a source position and seam depth after each record.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the fixture is complete and the trace has three entries per leaf
///   and two per pair; source positions may reset across seams.
/// - provides: observable callback history without changing the logical value.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 a literal leaf through two nested pointer-only chunks
///   yields exactly three distinct position/depth observations.
/// - witness: `tests::common::record_observers_preserve_nested_seams`
#[anodized::spec(maintains: anodized::types::Spec::predicate(&self.value)
    && self.value.0.iter().try_fold(0_usize, |count, node| {
        count.checked_add(match *node {
            Node::Leaf(_) => 3_usize,
            Node::Pair => 2_usize,
        })
    }) == Some(self.records.len()))]
#[derive(Debug, Eq, PartialEq)]
struct ObservedFixture
{
    /// The decoded logical value.
    value: Fixture,
    /// Metadata observed after each successful record read.
    records: Vec<(TokenOffset, SeamDepth)>,
}

impl CanonicalValue for ObservedFixture
{
    /// Emits the underlying fixture, excluding the observational metadata.
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

    /// Records source coordinates after each fixture record is consumed.
    ///
    /// # Specification
    /// - requires: malformed input is admitted for refusal.
    /// - ensures: returns a complete fixture and one observation per record;
    ///   the final observation is the reader's state on successful return.
    /// - fails: propagates reader and fixture-codec errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Reader errors and unexpected fixture constructor tags.
    ///
    /// # Adequacy
    /// - hypothesis: L3 two nested seams reset the final position to one and
    ///   depth to zero after leaf positions one and two at depth two.
    /// - witness: `tests::common::record_observers_preserve_nested_seams`
    #[anodized::spec(ensures: |ret| ret.is_err()
        || ret.as_ref().is_ok_and(|value| anodized::types::Spec::predicate(value)
            && value.records.last() == Some(&(reader.position(), reader.seam_depth()))))]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let mut records = Vec::new();
        let value = decode_observed(reader, &mut |reader: &TokenReader<'_>| {
            records.push((reader.position(), reader.seam_depth()));
        })?;
        Ok(Self { value, records })
    }
}

/// Structural admission rejects both missing children and early root endings.
#[test]
fn fixture_refinements_reject_invalid_roots()
{
    let leaf = Node::Leaf(CanonicalWord::from(7_u64));
    for nodes in [vec![], vec![Node::Pair], vec![Node::Pair, leaf], vec![
        leaf,
        Node::Pair,
        leaf,
    ]] {
        assert!(!anodized::types::Spec::predicate(&Fixture(nodes)));
    }
    for depth in 0_u32 ..= 8_u32 {
        let value = balanced(Depth(depth), Seed(5_u64));
        assert!(anodized::types::Spec::predicate(&value));
        assert_eq!(
            value.leaves(),
            LeafCount(1_usize.checked_shl(depth).expect("a bounded depth"))
        );
    }
    let value = balanced(Depth(2_u32), Seed(5_u64));
    assert!(
        value
            .0
            .iter()
            .map(|node| matches!(node, Node::Pair))
            .eq([true, true, false, false, true, false, false])
    );
    assert_eq!(value, balanced(Depth(2_u32), Seed(5_u64)));
    assert_ne!(value, balanced(Depth(2_u32), Seed(6_u64)));
}

/// Asymmetric codec goldens keep leaf edits separate from preorder node
/// indices.
#[test]
fn fixture_edits_preserve_preorder()
{
    let first = Fixture(vec![Node::Leaf(CanonicalWord::from(3_u64))]);
    let second = Fixture(vec![Node::Leaf(CanonicalWord::from(7_u64))]);
    let third = Fixture(vec![Node::Leaf(CanonicalWord::from(11_u64))]);
    let value = pair(&first, &pair(&second, &third));
    let flat = gandr_storage_values::encode_flat(&value).expect("the fixture encodes");
    let golden = [
        1_u8, 0x12, 1, 0x11, 2, 3, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0x12, 1, 0x11, 2, 7, 0, 0, 0, 0, 0,
        0, 0, 5, 1, 0x11, 2, 11, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5,
    ];
    assert_eq!(flat.as_ref(), golden);
    assert_eq!(
        gandr_storage_values::decode_flat::<Fixture>(TokenBody::from(golden.as_slice())),
        Ok(value.clone())
    );
    assert_eq!(value.leaves(), LeafCount(3_usize));
    for (index, words) in [
        (0_usize, [!3_u64, 7_u64, 11_u64]),
        (1_usize, [3_u64, !7_u64, 11_u64]),
        (2_usize, [3_u64, 7_u64, !11_u64]),
    ] {
        let [left, middle, right] = words;
        let edited = edit_leaf(&value, LeafIndex(index));
        assert_eq!(
            edited,
            Fixture(vec![
                Node::Pair,
                Node::Leaf(left.into()),
                Node::Pair,
                Node::Leaf(middle.into()),
                Node::Leaf(right.into())
            ])
        );
    }
    let embedding = Embedding(Inner::Value(first));
    let flat = gandr_storage_values::encode_flat(&embedding).expect("the embedding encodes");
    let mut golden = [1_u8, 0x13, 1, 0x11, 2, 3, 0, 0, 0, 0, 0, 0, 0, 5, 5];
    assert_eq!(flat.as_ref(), golden);
    assert_eq!(
        gandr_storage_values::decode_flat::<Embedding>(TokenBody::from(golden.as_slice())),
        Ok(embedding)
    );
    *golden.get_mut(1_usize).expect("the outer constructor tag") = 0xFE_u8;
    assert_eq!(
        gandr_storage_values::decode_flat::<Embedding>(TokenBody::from(golden.as_slice())),
        Err(ValueError::UnexpectedConstructor {
            found: ConstructorTag::from(0xFE_u8),
            position: TokenOffset::from(1_u32)
        })
    );
    let scripted =
        gandr_storage_values::encode_flat(&Script(vec![Step::Open, Step::Word, Step::Close]))
            .expect("the balanced script encodes");
    assert_eq!(scripted.as_ref(), [
        1_u8, 0x11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 5
    ]);
}

/// The independent scanner observes every wire kind and complete pointer
/// fields.
#[test]
fn the_reference_scanner_covers_each_wire_record()
{
    let mut bytes = vec![
        1_u8, 0x7F, 2, 7, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 4,
    ];
    bytes.extend_from_slice(&[0xA5_u8; 32]);
    bytes.extend_from_slice(&[4_u8, 3, 2, 1, 5]);
    assert_eq!(scan(TokenBody::from(bytes.as_slice())), vec![
        Scanned::Open,
        Scanned::Other,
        Scanned::Other,
        Scanned::Child(ContentPtr::new(
            ChunkDigest::from([0xA5_u8; 32]),
            TokenOffset::from(0x0102_0304_u32)
        )),
        Scanned::Other
    ]);
}

/// Nested pointer-only chunks restore the parent before the closing
/// observation.
#[test]
fn record_observers_preserve_nested_seams()
{
    let body = [1_u8, 0x11, 2, 7, 0, 0, 0, 0, 0, 0, 0, 5];
    let leaf =
        gandr_storage_values::frame_chunk(TokenBody::from(body.as_slice())).expect("a leaf chunk");
    let mut store = gandr_storage_values::InMemoryChunkStore::new();
    gandr_storage_values::ChunkStore::insert(&mut store, leaf.as_verified())
        .expect("the leaf stores");
    let mut middle_body = vec![4_u8];
    middle_body.extend_from_slice(leaf.digest().as_ref());
    middle_body.extend_from_slice(&[0_u8; 4]);
    let middle = gandr_storage_values::frame_chunk(TokenBody::from(middle_body.as_slice()))
        .expect("a pointer-only chunk");
    gandr_storage_values::ChunkStore::insert(&mut store, middle.as_verified())
        .expect("the middle stores");
    let mut outer_body = vec![4_u8];
    outer_body.extend_from_slice(middle.digest().as_ref());
    outer_body.extend_from_slice(&[0_u8; 4]);
    let outer = gandr_storage_values::frame_chunk(TokenBody::from(outer_body.as_slice()))
        .expect("an outer pointer-only chunk");
    gandr_storage_values::ChunkStore::insert(&mut store, outer.as_verified())
        .expect("the outer stores");
    let pointer = ContentPtr::new(outer.digest(), TokenOffset::ZERO);
    let observed: ObservedFixture =
        gandr_storage_values::cam_deref(&store, pointer).expect("nested seams decode");
    assert_eq!(
        observed.value,
        Fixture(vec![Node::Leaf(CanonicalWord::from(7_u64))])
    );
    assert_eq!(observed.records, vec![
        (TokenOffset::from(1_u32), SeamDepth::from(2_usize)),
        (TokenOffset::from(2_u32), SeamDepth::from(2_usize)),
        (TokenOffset::from(1_u32), SeamDepth::from(0_usize)),
    ]);
    assert!(anodized::types::Spec::predicate(&observed));
    let probed: Probed =
        gandr_storage_values::cam_deref(&store, pointer).expect("the probe decodes");
    assert_eq!(probed.value, observed.value);
    assert_eq!(probed.deepest, SeamDepth::from(2_usize));
}
