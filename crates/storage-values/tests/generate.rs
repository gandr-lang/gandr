//! Generated canonical values and typed profiles: the inputs the laws range
//! over.
//!
//! A generated value is a constructor tree over seven shapes, each its own
//! tag, held as its preorder records so neither its type nor its codec
//! recurses. Values are built bottom-up in an arena from generated steps, each
//! child naming an earlier node, so a node named twice becomes a repeated
//! subtree. The steps are biased toward deep spines, wide fans, repeated
//! subtrees and the empty-payload constructor; profiles toward kappa one,
//! powers of two, and caps at and below kappa.

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::EditDepth;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueProfile;
use proptest::prelude::Just;
#[cfg(test)]
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prelude::any;
#[cfg(test)]
use proptest::prop_assert_eq;
use proptest::prop_oneof;
#[cfg(test)]
use proptest::proptest;
use proptest::sample::Index;

/// The most records a generated value holds: a step whose node would pass it
/// builds a word leaf instead.
const RECORD_BUDGET: RecordCount = RecordCount(0x1000_u64);

/// The most children one fan step names.
const FAN_WIDTH: usize = 48;

/// The most constructors one spine step nests.
const SPINE_LENGTH: u32 = 96;

/// The most steps a generated value is built from after its first leaf.
const STEP_COUNT: usize = 40;

/// A generated constructor's shape: its tag, and the fields its decoder reads
/// after the open record.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Shape
{
    /// No payload and no children: the empty-payload constructor.
    Unit,
    /// One word.
    Word,
    /// One byte string.
    Bytes,
    /// Two children.
    Pair,
    /// A word, then one child: the spine former.
    Tagged,
    /// A child, a byte string, then a child: payload between children.
    Labelled,
    /// A word counting the children that follow it: the fan former.
    List,
}

impl Shape
{
    /// Every shape.
    const ALL: [Self; 7] = [
        Self::Unit,
        Self::Word,
        Self::Bytes,
        Self::Pair,
        Self::Tagged,
        Self::Labelled,
        Self::List,
    ];

    /// Returns the shape's constructor tag.
    ///
    /// # Specification
    /// trivial.
    pub fn tag(self) -> ConstructorTag
    {
        ConstructorTag::from(match self {
            | Self::Unit => 0x30_u8,
            | Self::Word => 0x31_u8,
            | Self::Bytes => 0x32_u8,
            | Self::Pair => 0x33_u8,
            | Self::Tagged => 0x34_u8,
            | Self::Labelled => 0x35_u8,
            | Self::List => 0x36_u8,
        })
    }

    /// Returns the fields the shape's decoder reads after its open record.
    ///
    /// # Specification
    /// trivial.
    const fn fields(self) -> &'static [Field]
    {
        match self {
            | Self::Unit => &[],
            | Self::Word => &[Field::Word],
            | Self::Bytes => &[Field::Bytes],
            | Self::Pair => &[Field::Child, Field::Child],
            | Self::Tagged => &[Field::Word, Field::Child],
            | Self::Labelled => &[Field::Child, Field::Bytes, Field::Child],
            | Self::List => &[Field::Count],
        }
    }

    /// Reads a tag as the shape carrying it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the shape whose tag is `tag`.
    /// - provides: the decoder's dispatch.
    /// - fails: `ValueError::UnexpectedConstructor` at the reader's position
    ///   for a tag no shape carries.
    /// - panics: none.
    ///
    /// # Errors
    /// An unknown tag, retaining its value and the reader's current position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 literal encodings cover all seven shapes; tags just
    ///   outside the assigned range are refused at the consumed open record.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(ensures: |ret| match ret {
        Ok(shape) => shape.tag() == tag,
        Err(error) => !Self::ALL.iter().any(|shape| shape.tag() == tag)
            && error == ValueError::UnexpectedConstructor { found: tag, position: reader.position() },
    })]
    fn of_tag(
        tag: ConstructorTag,
        reader: &TokenReader<'_>,
    ) -> Result<Self, ValueError>
    {
        Self::ALL
            .into_iter()
            .find(|shape| shape.tag() == tag)
            .ok_or_else(|| ValueError::UnexpectedConstructor {
                found: tag,
                position: reader.position(),
            })
    }
}

/// One field a constructor's decoder reads after its open record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Field
{
    /// A word.
    Word,
    /// A byte string.
    Bytes,
    /// A nested constructor.
    Child,
    /// A word counting the nested constructors that follow the fixed fields.
    Count,
}

/// What a decoder reads next.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Next
{
    /// A field of the innermost open constructor.
    Field(Field),
    /// The innermost open constructor's close.
    Close,
}

/// What an open constructor's decoder has yet to read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: fixed fields are a suffix of a supported constructor schema;
///   counted children are pending only after its fixed fields are exhausted.
/// - provides: the decoder's admissible pending-field states.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 fixed fields, a zero-child list, counted children at the
///   integer width and forged mixed/unknown field states separate transitions.
/// - witness: `tests::generate::generated_refinements_reject_impossible_states`
#[anodized::spec(maintains: self.fields.is_empty()
    || (self.children == 0_u64 && Shape::ALL.iter().any(|shape|
        shape.fields().ends_with(self.fields))))]
#[derive(Clone, Copy, Debug)]
struct Owed
{
    /// The fixed fields not yet read.
    fields: &'static [Field],
    /// The children a count announced and the decoder has not yet read.
    children: u64,
}

impl Owed
{
    /// Owes every field of `shape`.
    ///
    /// # Specification
    /// trivial.
    const fn new(shape: Shape) -> Self
    {
        Self {
            fields: shape.fields(),
            children: 0_u64,
        }
    }

    /// Takes what is read next: the next fixed field, then each counted child,
    /// then the close.
    ///
    /// # Specification
    /// - requires: this is an admissible pending-field state.
    /// - ensures: consumes one fixed field before counted children; otherwise
    ///   consumes one child, or returns close without changing an exhausted
    ///   state.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes ordered fixed fields, zero and two children,
    ///   repeated exhaustion and the maximum child count without wrapping.
    /// - witness: `tests::generate::generated_refinements_reject_impossible_states`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self),
        captures: [fields = self.fields, children = self.children],
        ensures: |ret| anodized::types::Spec::predicate(self)
            && match fields.split_first() {
                Some((&field, rest)) => ret == Next::Field(field)
                    && core::ptr::eq(core::ptr::from_ref(self.fields), core::ptr::from_ref(rest)) && self.children == children,
                None => self.fields.is_empty() && if children == 0_u64 {
                    ret == Next::Close && self.children == 0_u64
                } else {
                    ret == Next::Field(Field::Child)
                        && self.children.checked_add(1_u64) == Some(children)
                },
            })]
    fn take(&mut self) -> Next
    {
        if let Some((&field, rest)) = self.fields.split_first() {
            self.fields = rest;
            return Next::Field(field);
        }
        match self.children.checked_sub(1_u64) {
            | Some(left) => {
                self.children = left;
                Next::Field(Field::Child)
            },
            | None => Next::Close,
        }
    }
}

/// An inline byte string.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Payload(pub Vec<u8>);

/// One record of a generated value.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Item
{
    /// A constructor opens.
    Open(Shape),
    /// A word.
    Word(CanonicalWord),
    /// A byte string.
    Bytes(Payload),
    /// The innermost open constructor closes.
    Close,
}

/// An item's index in a generated value: also its record's index in the flat
/// form, one record per item.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ItemIndex(pub usize);

/// A constructor carrying a payload and no children, and where it sits.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the payload follows enough records to contain its leaf open and
///   every enclosing constructor; its exact location needs its tree.
/// - provides: a necessary bound on a leaf's index/depth evidence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinct root-child and nested leaves have exact indices
///   and depths; a zero index and depth reaching the payload index are refused.
/// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
/// - witness: `tests::generate::generated_refinements_reject_impossible_states`
#[anodized::spec(maintains: usize::try_from(u64::from(self.depth))
    .is_ok_and(|depth| depth < self.payload.0))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Leaf
{
    /// The payload's item.
    pub payload: ItemIndex,
    /// The constructors enclosing the leaf: zero for the root.
    pub depth: EditDepth,
}

/// A generated value: a constructor tree held as its preorder records.
///
/// # Specification
/// - requires: nothing.
/// - ensures: records form exactly one complete value of the seven-shape codec,
///   respecting fixed fields, counted children and all closes.
/// - provides: structural admission independent of a particular wire image.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 all seven shapes have literal wire evidence; malformed
///   roots, field kinds and child counts are rejected. The generator's 4096
///   record bound belongs to its producer, not to this codec's value type.
/// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
/// - witness: `tests::generate::generated_refinements_reject_impossible_states`
#[anodized::spec(maintains: {
    let mut open: Vec<Owed> = Vec::new();
    let mut next = Next::Field(Field::Child);
    let mut complete = false;
    let mut valid = true;
    for item in &self.0 {
        if complete {
            valid = false;
            break;
        }
        let matched = match (next, item) {
            (Next::Field(Field::Child), &Item::Open(shape)) => {
                open.push(Owed::new(shape));
                true
            },
            (Next::Field(Field::Word), &Item::Word(_))
                | (Next::Field(Field::Bytes), &Item::Bytes(_)) => true,
            (Next::Field(Field::Count), &Item::Word(count)) => {
                if let Some(owed) = open.last_mut() {
                    owed.children = u64::from(count);
                    true
                } else {
                    false
                }
            },
            (Next::Close, &Item::Close) => open.pop().is_some(),
            _ => false,
        };
        if !matched {
            valid = false;
            break;
        }
        if let Some(owed) = open.last_mut() {
            next = owed.take();
        } else {
            complete = true;
        }
    }
    valid && complete
})]
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tree(pub Vec<Item>);

impl Tree
{
    /// Lists every constructor's open record, in preorder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the indices carrying open records, strictly
    ///   increasing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a literal heterogeneous tree separates record indices
    ///   from constructor ordinals and payload byte offsets.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(ensures: |ret| ret.len()
        == self.0.iter().filter(|item| matches!(item, Item::Open(_))).count()
        && ret.iter().all(|index| matches!(self.0.get(index.0), Some(Item::Open(_))))
        && ret.windows(2).all(|pair| pair.first() < pair.get(1)))]
    pub fn opens(&self) -> Vec<ItemIndex>
    {
        self.0
            .iter()
            .enumerate()
            .filter(|&(_, item)| matches!(*item, Item::Open(_)))
            .map(|(index, _)| ItemIndex(index))
            .collect()
    }

    /// Lists every close but the root's: the records that end a boundary
    /// event's run.
    ///
    /// # Specification
    /// - requires: the records are a complete codec value.
    /// - ensures: exactly the close-record indices except the root's final
    ///   close, strictly increasing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 nested and empty constructors retain all inner exits
    ///   without treating the root's close as a boundary event.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self),
        ensures: |ret| ret.len() == self.0.iter().filter(|item|
            matches!(item, Item::Close)).count().saturating_sub(1_usize)
            && ret.iter().all(|index| self.0.get(index.0) == Some(&Item::Close)
                && index.0 < self.0.len().saturating_sub(1_usize))
            && ret.windows(2).all(|pair| pair.first() < pair.get(1)))]
    pub fn inner_closes(&self) -> Vec<ItemIndex>
    {
        let last = self.0.len().saturating_sub(1_usize);
        self.0
            .iter()
            .enumerate()
            .filter(|&(index, item)| *item == Item::Close && index < last)
            .map(|(index, _)| ItemIndex(index))
            .collect()
    }

    /// Returns the subtree whose open record is at `open`.
    ///
    /// # Specification
    /// - requires: `open` indexes an open record of this value.
    /// - ensures: the records from `open` through the close that matches it.
    /// - provides: a value that is a subtree of this one, for a store to hold
    ///   before this one is committed.
    /// - fails: never within the admitted domain.
    /// - panics: when `open` is not an open record of this value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 an interior tagged value retains its word and nested
    ///   word leaf while excluding the following sibling and outer close.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self)
        && matches!(self.0.get(open.0), Some(Item::Open(_))),
        ensures: |ret| anodized::types::Spec::predicate(&ret)
            && self.0.get(open.0 ..).is_some_and(|suffix| suffix.starts_with(&ret.0)))]
    pub fn subtree(
        &self,
        open: ItemIndex,
    ) -> Self
    {
        let mut depth = 0_usize;
        for (index, item) in self.0.iter().enumerate().skip(open.0) {
            match *item {
                | Item::Open(_) => depth = depth.checked_add(1_usize).expect("a value's depth"),
                | Item::Close => {
                    depth = depth
                        .checked_sub(1_usize)
                        .expect("a subtree starts at an open record");
                    if depth == 0_usize {
                        return Self(self.0[open.0 ..= index].to_vec());
                    }
                },
                | Item::Word(_) | Item::Bytes(_) => {},
            }
        }
        panic!("the open record at {open:?} is closed in a balanced value")
    }

    /// Lists every word and byte-string leaf with its depth, in preorder.
    ///
    /// # Specification
    /// - requires: the records are a complete codec value.
    /// - ensures: lists every word/bytes leaf's payload index and enclosing
    ///   depth in preorder; tagged words, counts and interleaved bytes are not
    ///   leaves.
    /// - fails: never.
    /// - panics: none within the admitted domain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 heterogeneous siblings and a nested word leaf have
    ///   exact indices and depths; nonleaf payload fields must be excluded.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self),
        ensures: |ret| {
            let mut depth = 0_u64;
            ret.iter().copied().eq(self.0.iter().enumerate().filter_map(|(index, item)| {
                match *item {
                    Item::Open(shape) => {
                        let enclosing = depth;
                        depth = depth.saturating_add(1_u64);
                        matches!(shape, Shape::Word | Shape::Bytes).then(|| Leaf {
                            payload: ItemIndex(index.saturating_add(1_usize)),
                            depth: EditDepth::from(enclosing),
                        })
                    },
                    Item::Close => { depth = depth.saturating_sub(1_u64); None },
                    Item::Word(_) | Item::Bytes(_) => None,
                }
            }))
        })]
    pub fn leaves(&self) -> Vec<Leaf>
    {
        let mut leaves = Vec::new();
        let mut depth = 0_u64;
        for (index, item) in self.0.iter().enumerate() {
            match *item {
                | Item::Open(shape) => {
                    if matches!(shape, Shape::Word | Shape::Bytes) {
                        leaves.push(Leaf {
                            payload: ItemIndex(index.checked_add(1_usize).expect("a record index")),
                            depth: EditDepth::from(depth),
                        });
                    }
                    depth = depth.checked_add(1_u64).expect("a value's depth");
                },
                | Item::Close => {
                    depth = depth
                        .checked_sub(1_u64)
                        .expect("a close ends an open constructor");
                },
                | Item::Word(_) | Item::Bytes(_) => {},
            }
        }
        leaves
    }

    /// Replaces one leaf's payload, in place, with a different one: a word by
    /// its complement, a byte string by its first byte complemented or, when
    /// empty, by one zero byte.
    ///
    /// # Specification
    /// - requires: `leaf` is one of [`Tree::leaves`].
    /// - ensures: the value differs from before in that payload alone.
    /// - provides: the edit every locality observation is made over.
    /// - fails: never within the admitted domain.
    /// - panics: when `leaf` names no payload of this value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 distinct word, binary and empty-byte leaves pin the
    ///   replacement and every untouched record, including a binary tail.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self)
        && leaf.payload.0 > 0_usize
        && matches!(self.0.get(leaf.payload.0.saturating_sub(1_usize)),
            Some(Item::Open(Shape::Word | Shape::Bytes)))
        && u64::from(leaf.depth) == self.0.iter()
            .take(leaf.payload.0.saturating_sub(1_usize)).fold(0_u64, |depth, item| match *item {
                Item::Open(_) => depth.saturating_add(1_u64),
                Item::Close => depth.saturating_sub(1_u64),
                Item::Word(_) | Item::Bytes(_) => depth,
            }),
        captures: [count = self.0.len(), before = match self.0.get(leaf.payload.0) {
            Some(&Item::Word(word)) => (Some(word), None),
            Some(&Item::Bytes(Payload(ref bytes))) => (None, Some((bytes.len(), bytes.first().copied()))),
            _ => (None, None),
        }],
        ensures: |ret| self.0.len() == count && anodized::types::Spec::predicate(self)
            && match (before, self.0.get(leaf.payload.0)) {
                ((Some(word), None), Some(&Item::Word(now))) => u64::from(now) == !u64::from(word),
                ((None, Some((length, first))), Some(&Item::Bytes(Payload(ref bytes)))) =>
                    bytes.len() == length.max(1_usize)
                        && bytes.first().copied() == Some(first.map_or(0_u8, |byte| !byte)),
                _ => false,
            })]
    pub fn edit(
        &mut self,
        leaf: Leaf,
    )
    {
        match self.0[leaf.payload.0] {
            | Item::Word(ref mut word) => *word = CanonicalWord::from(!u64::from(*word)),
            | Item::Bytes(Payload(ref mut bytes)) => match bytes.first_mut() {
                | Some(first) => *first = !*first,
                | None => bytes.push(0_u8),
            },
            | Item::Open(_) | Item::Close => panic!("{leaf:?} names no payload"),
        }
    }
}

impl CanonicalValue for Tree
{
    /// Replays the records.
    ///
    /// # Specification
    /// - requires: the records are a complete value of this codec.
    /// - ensures: sends each typed record to the corresponding sink operation
    ///   in order, stopping at the first refusal.
    /// - fails: propagates the first sink error without rollback.
    /// - panics: propagates a sink panic.
    ///
    /// # Errors
    /// The first sink refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 literal bytes cover all shapes, binary and empty
    ///   payloads, fixed fields and counted children; L2 generated round trips
    ///   are bounded by 4096 records, with repeated and deeply nested subtrees.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    /// - witness: `tests::laws::every_generated_value_round_trips_flat`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self))]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        for item in &self.0 {
            match *item {
                | Item::Open(shape) => sink.open(shape.tag())?,
                | Item::Word(word) => sink.word(word)?,
                | Item::Bytes(ref payload) => sink.bytes(TokenBytes::from(payload.0.as_slice()))?,
                | Item::Close => sink.close()?,
            }
        }

        Ok(())
    }

    /// Reads one value, each constructor's fields by its tag.
    ///
    /// # Specification
    /// - requires: malformed input is admitted for refusal.
    /// - ensures: returns exactly one complete value under this codec's field
    ///   grammar and advances the reader, copying byte payloads into the value.
    /// - fails: propagates reader errors or names an unknown constructor tag.
    /// - panics: none.
    ///
    /// # Errors
    /// Reader refusals and unknown constructor tags at their consumed position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 all seven shapes have literal byte evidence; unknown
    ///   tags and missing counted children are refused by kind and position.
    /// - witness: `tests::generate::generated_codec_preserves_schema_and_leaf_edits`
    #[anodized::spec(captures: spent = reader.spent(), ensures: |ret| ret.is_err()
        || ret.as_ref().is_ok_and(|value| anodized::types::Spec::predicate(value)
            && reader.spent() > spent))]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let mut items = Vec::new();
        let mut open: Vec<Owed> = Vec::new();
        let mut next = Next::Field(Field::Child);

        loop {
            match next {
                | Next::Field(Field::Child) => {
                    let tag = reader.read_tag()?;
                    let shape = Shape::of_tag(tag, reader)?;
                    items.push(Item::Open(shape));
                    open.push(Owed::new(shape));
                },
                | Next::Field(Field::Word) => {
                    let word = reader.read_word()?;
                    items.push(Item::Word(word));
                },
                | Next::Field(Field::Count) => {
                    let count = reader.read_word()?;
                    if let Some(owed) = open.last_mut() {
                        owed.children = u64::from(count);
                    }
                    items.push(Item::Word(count));
                },
                | Next::Field(Field::Bytes) => {
                    let bytes = reader.read_bytes()?;
                    items.push(Item::Bytes(Payload(<&[u8]>::from(bytes).to_vec())));
                },
                | Next::Close => {
                    reader.read_close()?;
                    items.push(Item::Close);
                    open.pop();
                },
            }
            let Some(owed) = open.last_mut()
            else {
                return Ok(Self(items));
            };
            next = owed.take();
        }
    }
}

/// A node's index in an arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeId(usize);

/// One field of a built node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Slot
{
    /// A word.
    Word(CanonicalWord),
    /// A byte string.
    Bytes(Payload),
    /// An earlier node, nested here.
    Child(NodeId),
}

/// A number of records.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RecordCount(u64);

/// One built node.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the slots follow the shape's fixed/counting grammar and the
///   cached record count includes an open and close. Child identities and the
///   exact cache value require the owning arena.
/// - provides: local structural admission for an arena node.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 repeated children, counted fans and mixed fields have exact
///   flattenings; malformed field and count claims are rejected.
/// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
/// - witness: `tests::generate::arena_refinements_reject_stale_metadata`
#[anodized::spec(maintains: self.records.0 >= 2_u64 && {
    let mut owed = Owed::new(self.shape);
    let mut valid = true;
    for slot in &self.slots {
        let matched = match (owed.take(), slot) {
            (Next::Field(Field::Child), &Slot::Child(_))
                | (Next::Field(Field::Word), &Slot::Word(_))
                | (Next::Field(Field::Bytes), &Slot::Bytes(_)) => true,
            (Next::Field(Field::Count), &Slot::Word(count)) => {
                owed.children = u64::from(count);
                true
            },
            _ => false,
        };
        if !matched {
            valid = false;
            break;
        }
    }
    valid && owed.take() == Next::Close
})]
#[derive(Clone, Debug)]
struct Node
{
    /// The node's shape.
    shape: Shape,
    /// The node's fields, in the order its decoder reads them.
    slots: Vec<Slot>,
    /// The expanded record count, saturated at the counter's width.
    records: RecordCount,
    /// Whether a later node nests this one.
    nested: Nested,
}

/// Whether a later node of an arena nests a node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Nested(bool);

/// One pending piece of a flattening.
#[derive(Clone, Debug)]
enum Task
{
    /// A node whose tree is still to be written.
    Node(NodeId),
    /// A record ready to be written.
    Item(Item),
}

/// Constructor trees built bottom-up, every child naming an earlier node.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each node has the declared slot grammar; child references point
///   strictly backward, caches are saturated expanded counts, and a node is
///   marked nested exactly when a later node references it.
/// - provides: acyclic construction and faithful frontier/cache metadata.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 repeated references count twice when flattened but mark one
///   existing node; forged forward edges, stale counts and wrong markers fail
///   independently. No bounded-value restriction is imposed on the arena.
/// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
/// - witness: `tests::generate::arena_refinements_reject_stale_metadata`
#[anodized::spec(maintains: self.0.iter().enumerate().all(|(index, node)|
    anodized::types::Spec::predicate(node)
        && node.slots.iter().all(|slot| match *slot {
            Slot::Child(child) => child.0 < index,
            Slot::Word(_) | Slot::Bytes(_) => true,
        })
        && node.slots.iter().try_fold(2_u64, |total, slot| Some(total.saturating_add(match *slot {
            Slot::Child(child) => self.0.get(child.0)?.records.0,
            Slot::Word(_) | Slot::Bytes(_) => 1_u64,
        }))) == Some(node.records.0)
        && node.nested.0 == self.0.iter().skip(index.saturating_add(1_usize))
            .any(|later| later.slots.iter().any(|slot|
                matches!(*slot, Slot::Child(child) if child.0 == index)))))]
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Arena(Vec<Node>);

impl Arena
{
    /// Counts the records a node with these fields flattens to.
    ///
    /// # Specification
    /// - requires: every child index names a node of this arena.
    /// - ensures: two envelope records plus one per payload field and each
    ///   child's cached expanded count, saturated at `u64::MAX`.
    /// - fails: never.
    /// - panics: on an out-of-range child index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 repeated children retain logical multiplicity; a
    ///   compact doubling DAG reaches the counter width without flattening.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: slots.iter().all(|slot| match *slot {
        Slot::Child(child) => child.0 < self.0.len(),
        Slot::Word(_) | Slot::Bytes(_) => true,
    }), ensures: |ret| slots.iter().try_fold(2_u128, |total, slot|
        Some(total.saturating_add(match *slot {
            Slot::Child(child) => u128::from(self.0.get(child.0)?.records.0),
            Slot::Word(_) | Slot::Bytes(_) => 1_u128,
        }))).is_some_and(|total| u128::from(ret.0) == total.min(u128::from(u64::MAX))))]
    fn records(
        &self,
        slots: &[Slot],
    ) -> RecordCount
    {
        RecordCount(slots.iter().fold(2_u64, |total, slot| {
            total.saturating_add(match *slot {
                | Slot::Child(child) => self.0[child.0].records.0,
                | Slot::Word(_) | Slot::Bytes(_) => 1_u64,
            })
        }))
    }

    /// Adds a node.
    ///
    /// # Specification
    /// - requires: `slots` are the fields `shape` reads, each child an earlier
    ///   node of this arena; a fan's count word equals its children.
    /// - ensures: the new node's id; each child is marked nested.
    /// - provides: the one way a node enters an arena.
    /// - fails: never within the admitted domain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 mixed fields and repeated child handles preserve their
    ///   exact flattening; only referenced children leave the frontier.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: slots.iter().all(|slot| match *slot {
        Slot::Child(child) => child.0 < self.0.len(),
        Slot::Word(_) | Slot::Bytes(_) => true,
    }), captures: [entry = self.0.len(), width = slots.len()],
        ensures: |ret| ret.0 == entry && self.0.len().checked_sub(entry) == Some(1_usize)
            && self.0.get(ret.0).is_some_and(|node| node.shape == shape
                && node.slots.len() == width && node.nested == Nested(false)
                && anodized::types::Spec::predicate(node)
                && node.records == self.records(&node.slots)
                && node.slots.iter().all(|slot| match *slot {
                    Slot::Child(child) => child.0 < ret.0
                        && self.0.get(child.0).is_some_and(|child| child.nested == Nested(true)),
                    Slot::Word(_) | Slot::Bytes(_) => true,
                })))]
    pub fn push(
        &mut self,
        shape: Shape,
        slots: Vec<Slot>,
    ) -> NodeId
    {
        let records = self.records(&slots);
        for slot in &slots {
            if let Slot::Child(child) = *slot {
                self.0[child.0].nested = Nested(true);
            }
        }
        self.0.push(Node {
            shape,
            slots,
            records,
            nested: Nested(false),
        });
        NodeId(self.0.len().saturating_sub(1_usize))
    }

    /// Lists the nodes no later node nests, oldest first.
    ///
    /// # Specification
    /// - requires: the nested markers reflect this arena's references.
    /// - ensures: every unmarked node exactly once in ascending index order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 an unused sibling remains a root while two references
    ///   to one child remove that child only once from the frontier.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(ensures: |ret| ret.len() == self.0.iter()
        .filter(|node| node.nested == Nested(false)).count()
        && ret.iter().all(|id| self.0.get(id.0).is_some_and(|node| node.nested == Nested(false)))
        && ret.windows(2).all(|pair| pair.first().zip(pair.get(1))
            .is_some_and(|(left, right)| left.0 < right.0)))]
    fn frontier(&self) -> Vec<NodeId>
    {
        self.0
            .iter()
            .enumerate()
            .filter(|&(_, node)| node.nested == Nested(false))
            .map(|(index, _)| NodeId(index))
            .collect()
    }

    /// Adds a fan over `children`, its count word first.
    ///
    /// # Specification
    /// - requires: every child names this arena; the count fits its wire word.
    /// - ensures: appends a list with the exact child count and references in
    ///   their supplied order, retaining repeated references.
    /// - fails: never.
    /// - panics: on an invalid child or unrepresentable count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 empty and repeated-child lists bind the count word and
    ///   flattened order; a wide fan reaches the record-budget boundary.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: u64::try_from(children.len()).is_ok()
        && children.iter().all(|child| child.0 < self.0.len()),
        captures: entry = self.0.len(), ensures: |ret| ret.0 == entry
            && self.0.len().checked_sub(entry) == Some(1_usize)
            && self.0.get(ret.0).is_some_and(|node| node.shape == Shape::List
                && anodized::types::Spec::predicate(node)
                && node.slots.len().checked_sub(1_usize) == Some(children.len())
                && node.slots.iter().skip(1_usize).zip(children).all(|(slot, child)|
                    matches!(*slot, Slot::Child(held) if held == *child))))]
    pub fn list(
        &mut self,
        children: &[NodeId],
    ) -> NodeId
    {
        self.push(Shape::List, fan(children))
    }

    /// Adds a node, or a word leaf when the node would pass the record budget.
    ///
    /// # Specification
    /// - requires: the slots match the shape and all child indices are valid.
    /// - ensures: appends the proposed node when its count is at most the
    ///   budget; otherwise appends a three-record all-ones word leaf, without
    ///   marking the discarded proposal's children as newly nested.
    /// - fails: never.
    /// - panics: on an invalid child index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 counts exactly 4096 and 4097 distinguish the admitted
    ///   boundary from replacement; repeated doubling also triggers fallback.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: slots.iter().all(|slot| match *slot {
        Slot::Child(child) => child.0 < self.0.len(),
        Slot::Word(_) | Slot::Bytes(_) => true,
    }), captures: [entry = self.0.len(), requested = self.records(&slots)],
        ensures: |ret| ret.0 == entry && self.0.len().checked_sub(entry) == Some(1_usize)
            && self.0.get(ret.0).is_some_and(|node| node.records <= RECORD_BUDGET
                && anodized::types::Spec::predicate(node) && if requested > RECORD_BUDGET {
                    node.shape == Shape::Word && node.records == RecordCount(3_u64)
                        && node.slots == [Slot::Word(CanonicalWord::from(u64::MAX))]
                } else { node.shape == shape && node.records == requested }))]
    fn within(
        &mut self,
        shape: Shape,
        slots: Vec<Slot>,
    ) -> NodeId
    {
        if self.records(&slots) > RECORD_BUDGET {
            return self.push(Shape::Word, vec![Slot::Word(CanonicalWord::from(u64::MAX))]);
        }
        self.push(shape, slots)
    }

    /// Names the node `back` places before the latest, wrapping.
    ///
    /// # Specification
    /// - requires: the arena holds a node.
    /// - ensures: an earlier node of this arena.
    /// - provides: a selector's resolution.
    /// - fails: never when the selector fits the host index width.
    /// - panics: on an empty arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 latest, oldest, wrapped and maximum-width selectors
    ///   have exact indices in a three-node arena.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: !self.0.is_empty() && usize::try_from(back.0).is_ok(),
        ensures: |ret| usize::try_from(back.0).ok()
            .and_then(|back| back.checked_rem(self.0.len()))
            .and_then(|back| self.0.len().checked_sub(1_usize)?.checked_sub(back)) == Some(ret.0))]
    fn pick(
        &self,
        back: Back,
    ) -> NodeId
    {
        let built = self.0.len();
        let back = usize::try_from(back.0)
            .expect("a selector fits an index")
            .checked_rem(built)
            .expect("an arena holds a node before a step names one");
        NodeId(
            built
                .checked_sub(1_usize)
                .and_then(|latest| latest.checked_sub(back))
                .expect("a selector reduced below the node count"),
        )
    }

    /// Builds one step's nodes and names the last of them.
    ///
    /// # Specification
    /// - requires: the arena holds a node, unless `step` is a leaf.
    /// - ensures: names the last new node, replacing an over-budget proposal by
    ///   a word leaf. A zero-length spine adds nothing and returns its selected
    ///   existing node, which need not be within the producer budget.
    /// - provides: a generated step's resolution.
    /// - fails: never within the admitted host-index and memory bounds.
    /// - panics: a step naming a child of an empty arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 repeated references, a zero-length spine and a
    ///   multi-level spine separate reuse from bounded new construction.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: !self.0.is_empty()
        || matches!(*step, Step::Unit | Step::Word(_) | Step::Bytes(_)),
        captures: entry = self.0.len(), ensures: |ret| if let Step::Spine(SpineLength(0_u32), _, back) = *step {
            self.0.len() == entry && ret == self.pick(back)
        } else {
            let added = if let Step::Spine(length, _, _) = *step {
                usize::try_from(length.0).ok()
            } else { Some(1_usize) };
            self.0.len().checked_sub(entry) == added
                && ret.0.checked_add(1_usize) == Some(self.0.len())
                && self.0.get(ret.0).is_some_and(|node| node.records <= RECORD_BUDGET
                    && anodized::types::Spec::predicate(node))
        })]
    fn step(
        &mut self,
        step: &Step,
    ) -> NodeId
    {
        match *step {
            | Step::Unit => self.within(Shape::Unit, Vec::new()),
            | Step::Word(word) => self.within(Shape::Word, vec![Slot::Word(word)]),
            | Step::Bytes(ref payload) => {
                self.within(Shape::Bytes, vec![Slot::Bytes(payload.clone())])
            },
            | Step::Pair(left, right) => {
                let left = self.pick(left);
                let right = self.pick(right);
                self.within(Shape::Pair, vec![Slot::Child(left), Slot::Child(right)])
            },
            | Step::Twice(back) => {
                let child = self.pick(back);
                self.within(Shape::Pair, vec![Slot::Child(child), Slot::Child(child)])
            },
            | Step::Tagged(word, back) => {
                let child = self.pick(back);
                self.within(Shape::Tagged, vec![Slot::Word(word), Slot::Child(child)])
            },
            | Step::Labelled(left, ref label, right) => {
                let left = self.pick(left);
                let right = self.pick(right);
                self.within(Shape::Labelled, vec![
                    Slot::Child(left),
                    Slot::Bytes(label.clone()),
                    Slot::Child(right),
                ])
            },
            | Step::Fan(ref backs) => {
                let children: Vec<NodeId> = backs.iter().map(|&back| self.pick(back)).collect();
                self.within(Shape::List, fan(&children))
            },
            | Step::Spine(length, word, back) => {
                let mut node = self.pick(back);
                for level in 0_u32 .. length.0 {
                    let word = CanonicalWord::from(u64::from(word).wrapping_add(u64::from(level)));
                    node = self.within(Shape::Tagged, vec![Slot::Word(word), Slot::Child(node)]);
                }
                node
            },
        }
    }

    /// Flattens one node's tree into its preorder records.
    ///
    /// # Specification
    /// - requires: `root` names a valid node and its expanded tree fits memory.
    /// - ensures: the records of `root`'s tree, a node named twice written
    ///   twice.
    /// - provides: the value an arena describes.
    /// - fails: never within the admitted domain.
    /// - panics: when `root` is not a node of this arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 repeated child identities produce repeated record
    ///   subsequences, while exact-budget and one-past values distinguish the
    ///   codec's unrestricted grammar from the bounded producer.
    /// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
    #[anodized::spec(requires: root.0 < self.0.len(),
        ensures: |ret| anodized::types::Spec::predicate(&ret)
            && self.0.get(root.0).is_some_and(|node|
                u64::try_from(ret.0.len()) == Ok(node.records.0)))]
    pub fn tree(
        &self,
        root: NodeId,
    ) -> Tree
    {
        let mut items = Vec::new();
        let mut pending = vec![Task::Node(root)];

        while let Some(task) = pending.pop() {
            match task {
                | Task::Item(item) => items.push(item),
                | Task::Node(id) => {
                    let node = &self.0[id.0];
                    items.push(Item::Open(node.shape));
                    pending.push(Task::Item(Item::Close));
                    for slot in node.slots.iter().rev() {
                        pending.push(match *slot {
                            | Slot::Word(word) => Task::Item(Item::Word(word)),
                            | Slot::Bytes(ref payload) => Task::Item(Item::Bytes(payload.clone())),
                            | Slot::Child(child) => Task::Node(child),
                        });
                    }
                },
            }
        }

        Tree(items)
    }
}

/// Returns a fan's fields: its count word, then its children.
///
/// # Specification
/// - requires: the child count fits a canonical word.
/// - ensures: one count word followed by exactly the supplied child handles, in
///   order and retaining repetitions.
/// - fails: never.
/// - panics: if the host slice count exceeds the canonical word width.
///
/// # Adequacy
/// - hypothesis: L3 empty and repeated-child fans flatten through the real
///   arena list constructor with exact counts and child order.
/// - witness: `tests::generate::arena_counts_and_bounds_keep_semantic_nodes`
#[anodized::spec(requires: u64::try_from(children.len()).is_ok(),
    ensures: |ret| ret.len().checked_sub(1_usize) == Some(children.len())
        && ret.first().is_some_and(|slot| match *slot {
            Slot::Word(count) => u64::try_from(children.len()) == Ok(u64::from(count)),
            Slot::Bytes(_) | Slot::Child(_) => false,
        })
        && ret.iter().skip(1_usize).zip(children).all(|(slot, child)|
            matches!(*slot, Slot::Child(held) if held == *child)))]
fn fan(children: &[NodeId]) -> Vec<Slot>
{
    let count = CanonicalWord::from(u64::try_from(children.len()).expect("a fan width"));
    core::iter::once(Slot::Word(count))
        .chain(children.iter().copied().map(Slot::Child))
        .collect()
}

/// A generated selector: how many nodes before the latest it names, wrapping.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Back(u32);

/// How many constructors a spine step nests.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct SpineLength(u32);

/// One generated build step.
#[derive(Clone, Debug)]
pub enum Step
{
    /// The empty-payload constructor.
    Unit,
    /// A word leaf.
    Word(CanonicalWord),
    /// A byte-string leaf.
    Bytes(Payload),
    /// A pair of two earlier nodes.
    Pair(Back, Back),
    /// A pair whose two children are one earlier node: a repeated subtree.
    Twice(Back),
    /// A word above an earlier node.
    Tagged(CanonicalWord, Back),
    /// A byte string between two earlier nodes.
    Labelled(Back, Payload, Back),
    /// A fan over earlier nodes.
    Fan(Vec<Back>),
    /// A run of tagged constructors nested above an earlier node, each with
    /// the word one past the last: a deep spine.
    Spine(SpineLength, CanonicalWord, Back),
}

/// Builds a value from its first leaf and the steps after it.
///
/// # Specification
/// - requires: `first` is a leaf step.
/// - ensures: the tree rooted at the one node no other nests, or else at a fan
///   over every such node, the oldest dropped until the fan fits the record
///   budget; every node a step built is in the value unless dropped.
/// - provides: a generated value's resolution.
/// - fails: never within the admitted memory and selector widths.
/// - panics: when `first` names a child.
///
/// # Adequacy
/// - hypothesis: L3 repeated-child steps preserve reuse and an over-budget
///   frontier drops exactly its oldest root; generated L2 consumers range over
///   at most forty steps, each spine of at most ninety-six constructors.
/// - witness: `tests::generate::builds_preserve_reuse_and_trim_oldest_roots`
/// - witness: `tests::laws::every_generated_value_commits_and_derefs_back_equal`
#[anodized::spec(requires: matches!(*first, Step::Unit | Step::Word(_) | Step::Bytes(_)),
    ensures: |ret| anodized::types::Spec::predicate(&ret)
        && u64::try_from(ret.0.len()).is_ok_and(|count| count <= RECORD_BUDGET.0))]
fn build(
    first: &Step,
    steps: &[Step],
) -> Tree
{
    let mut arena = Arena::default();
    let _first = arena.step(first);
    for step in steps {
        let _built = arena.step(step);
    }

    let mut frontier = arena.frontier();
    while frontier.len() > 1_usize && arena.records(&fan(&frontier)) > RECORD_BUDGET {
        frontier.remove(0_usize);
    }
    let root = match *frontier.as_slice() {
        | [only] => only,
        | _ => arena.list(&frontier),
    };

    arena.tree(root)
}

/// Generates a payload word, biased toward zero, the all-ones word and small
/// values, so equal payloads and so repeated subtrees are common.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples the full word domain, with extra weight on zero, the
///   all-ones word and zero through seven.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded generated values exercise payload encoding;
///   this is not a statistical frequency claim.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
fn word() -> impl Strategy<Value = CanonicalWord>
{
    prop_oneof![
        1 => Just(0_u64),
        1 => Just(u64::MAX),
        2 => 0_u64 .. 8_u64,
        2 => any::<u64>(),
    ]
    .prop_map(CanonicalWord::from)
}

/// Generates a byte string, biased toward the empty one.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples arbitrary binary payloads of zero through 300 bytes, with
///   extra weight on empty and short payloads.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded generated values exercise empty, short and
///   longer binary payloads without claiming exhaustive byte coverage.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
fn payload() -> impl Strategy<Value = Payload>
{
    prop_oneof![
        2 => Just(Vec::new()),
        3 => proptest::collection::vec(any::<u8>(), 1_usize ..= 8_usize),
        1 => proptest::collection::vec(any::<u8>(), 9_usize ..= 300_usize),
    ]
    .prop_map(Payload)
}

/// Generates a selector, biased toward the latest node so steps chain into
/// spines, and toward the few before it so subtrees repeat.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples the full selector width, with extra weight on the latest
///   node and the preceding three.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded values exercise wrapped references and sharing;
///   exact selector boundaries have a separate arena witness.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
fn back() -> impl Strategy<Value = Back>
{
    prop_oneof![
        4 => Just(0_u32),
        2 => 1_u32 ..= 3_u32,
        1 => any::<u32>(),
    ]
    .prop_map(Back)
}

/// Generates a leaf step, biased toward the empty-payload constructor.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples only unit, word and bytes steps, with unit twice the
///   weight of either payload-bearing branch.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded values start from a complete leaf before any
///   child-selection step.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
fn leaf() -> impl Strategy<Value = Step>
{
    prop_oneof![
        2 => Just(Step::Unit),
        1 => word().prop_map(Step::Word),
        1 => payload().prop_map(Step::Bytes),
    ]
}

/// Generates one build step.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples leaves, paired/repeated children, tagged and labelled
///   children, fans of at most 48 children and spines of one through 96
///   constructors.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 values use at most forty such steps; the per-step spine
///   bound is not an overall depth bound.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
fn step() -> impl Strategy<Value = Step>
{
    prop_oneof![
        3 => leaf(),
        2 => (back(), back()).prop_map(|(left, right)| Step::Pair(left, right)),
        1 => back().prop_map(Step::Twice),
        2 => (word(), back()).prop_map(|(word, child)| Step::Tagged(word, child)),
        1 => (back(), payload(), back())
            .prop_map(|(left, label, right)| Step::Labelled(left, label, right)),
        2 => proptest::collection::vec(back(), 0_usize ..= FAN_WIDTH).prop_map(Step::Fan),
        1 => (1_u32 ..= SPINE_LENGTH, word(), back())
            .prop_map(|(length, word, child)| Step::Spine(SpineLength(length), word, child)),
    ]
}

/// Generates a canonical value.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples complete seven-shape values with at most 4096 records,
///   built from a leaf and at most forty subsequent steps.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 cases check exact flat codec round trips within this
///   producer bound.
/// - witness: `tests::laws::every_generated_value_round_trips_flat`
pub fn tree() -> impl Strategy<Value = Tree>
{
    (
        leaf(),
        proptest::collection::vec(step(), 0_usize ..= STEP_COUNT),
    )
        .prop_map(|(first, steps)| build(&first, &steps))
}

/// Generates kappa: one, a power of two, a small odd-or-even value, or the
/// widest, under which divisibility almost never decides.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples one, powers of two from two through 65536, values three
///   through 99, and the widest nonzero parameter.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded cut cases compare the implementation with the
///   independent scanner across generated divisibility parameters.
/// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
pub fn kappa() -> impl Strategy<Value = Kappa>
{
    prop_oneof![
        2 => Just(1_u64),
        3 => (1_u32 ..= 16_u32)
            .prop_map(|exponent| 1_u64.checked_shl(exponent).expect("an exponent below the width")),
        1 => 3_u64 ..= 99_u64,
        1 => Just(u64::MAX),
    ]
    .prop_map(|raw| Kappa::try_from(raw).expect("kappa is nonzero"))
}

/// Generates a cap for `kappa`: at kappa, at or below it, one, small, or the
/// widest.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples the supplied kappa, positive values at or below it, one,
///   two through 24, or the maximum word; a cap need not be at most kappa.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded cut cases independently check cap and residue
///   decisions; scalar cap extremes also have fixed witnesses.
/// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
pub fn cap(kappa: Kappa) -> impl Strategy<Value = TokenCap>
{
    let kappa = u64::from(kappa);
    prop_oneof![
        2 => Just(kappa),
        2 => 1_u64 ..= kappa,
        1 => Just(1_u64),
        2 => 2_u64 ..= 24_u64,
        1 => Just(u64::MAX),
    ]
    .prop_map(|raw| TokenCap::try_from(raw).expect("the cap is nonzero"))
}

/// Generates a codec identity, which no chunking decision reads.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples both complete 16-bit identity components; these label the
///   profile without changing cut decisions.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded histories compare root identity before and
///   after prior commits under generated profiles.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
fn codec() -> impl Strategy<Value = CodecIdentity>
{
    (any::<u16>(), any::<u16>()).prop_map(|(id, version)| {
        CodecIdentity::new(CodecId::from(id), CodecVersion::from(version))
    })
}

/// Builds the profile a commit runs under.
///
/// # Specification
/// trivial.
pub fn profile_of(
    kappa: Kappa,
    cap: TokenCap,
    codec: CodecIdentity,
) -> ValueProfile
{
    ValueProfile::new(
        TypedChunkerParams::new(kappa, cap),
        codec,
        ChildIndexBase::Absolute,
    )
}

/// Generates a typed profile.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples supported absolute-index profiles with generated codec
///   identities and correlated nonzero kappa/cap choices.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded histories compare cold and populated stores
///   under these profiles.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
pub fn profile() -> impl Strategy<Value = ValueProfile>
{
    kappa()
        .prop_flat_map(|kappa| (Just(kappa), cap(kappa), codec()))
        .prop_map(|(kappa, cap, codec)| profile_of(kappa, cap, codec))
}

/// Generates a value and a cap at, or one record below, a selected pre-cut
/// boundary position; earlier cuts may reset the actual pending run.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples a bounded value and an absolute profile whose cap equals
///   the record index after a selected non-root close, or one less clamped to
///   one; values without such a close use one. Earlier cuts can reset the
///   actual run before that event.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 cut cases compare actual decisions with the independent
///   scanner, rather than assuming the selected event is the first cut.
/// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
fn value_at_a_cap() -> impl Strategy<Value = (Tree, ValueProfile)>
{
    tree()
        .prop_flat_map(|value| (Just(value), kappa(), any::<Index>(), any::<bool>(), codec()))
        .prop_map(|(value, kappa, event, past, codec)| {
            // Before the first cut every record counts, so the run through an
            // event ends at the record after its close.
            let closes = value.inner_closes();
            let reach = closes
                .get(event.index(closes.len().max(1_usize)))
                .map_or(1_u64, |close| {
                    u64::try_from(close.0)
                        .expect("a record index")
                        .saturating_add(1_u64)
                });
            let raw = if past {
                reach.saturating_sub(1_u64).max(1_u64)
            }
            else {
                reach
            };
            let cap = TokenCap::try_from(raw).expect("the cap is nonzero");
            (value, profile_of(kappa, cap, codec))
        })
}

/// Generates cut inputs from equally weighted event-targeted and independent
/// value/profile branches.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: equally weights pre-cut event-targeted caps and independently
///   generated value/profile pairs.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded cases compare actual cuts, including cap and
///   residue interactions, against a separate scanner.
/// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
pub fn cut_case() -> impl Strategy<Value = (Tree, ValueProfile)>
{
    prop_oneof![value_at_a_cap(), (tree(), profile())]
}

/// Where a value committed before the law's own value comes from.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh recipe contains a complete value; relative recipes defer
///   their source and selection to the supplied main value.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 bounded histories resolve fresh and relative recipes before
///   real commits; subtree and leaf selection have literal oracles.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
/// - witness: `tests::generate::prior_recipes_select_only_tree_values`
#[anodized::spec(maintains: match *self {
    Self::Fresh(ref value) => anodized::types::Spec::predicate(value),
    Self::Subtree(_) | Self::Edited(_) | Self::Itself => true,
})]
#[derive(Clone, Debug)]
pub enum PriorValue
{
    /// An unrelated generated value.
    Fresh(Tree),
    /// One of the law's value's subtrees.
    Subtree(Index),
    /// The law's value with one leaf edited.
    Edited(Index),
    /// The law's value itself.
    Itself,
}

impl PriorValue
{
    /// Resolves the prior value against the law's own.
    ///
    /// # Specification
    /// - requires: a fresh recipe holds a complete value; relative recipes
    ///   receive a complete main value.
    /// - ensures: returns the exact fresh or main value, the indexed complete
    ///   subtree, or the main value with only the indexed leaf payload edited.
    ///   A value without payload leaves remains unchanged by an edit recipe.
    /// - fails: never.
    /// - panics: none within the admitted domain.
    ///
    /// # Adequacy
    /// - hypothesis: L2 selectors have literal subtree and edit oracles; tagged
    ///   words and interleaved labels are not payload leaves, and a leafless
    ///   value admits the edit recipe without selecting from empty.
    /// - witness: `tests::generate::prior_recipes_select_only_tree_values`
    /// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
    #[anodized::spec(requires: anodized::types::Spec::predicate(self)
        && (matches!(*self, Self::Fresh(_)) || anodized::types::Spec::predicate(main)),
        ensures: |ret| anodized::types::Spec::predicate(&ret) && match *self {
            Self::Fresh(ref value) => ret == *value,
            Self::Itself => ret == *main,
            Self::Subtree(index) => {
                let count = main.0.iter().filter(|item| matches!(item, Item::Open(_))).count();
                count > 0_usize && main.0.iter().enumerate()
                    .filter_map(|(at, item)| matches!(item, Item::Open(_)).then_some(at))
                    .nth(index.index(count)).is_some_and(|at|
                        at.checked_add(ret.0.len()).and_then(|end| main.0.get(at..end))
                            .is_some_and(|items| ret.0.as_slice() == items))
            },
            Self::Edited(index) => {
                let count = main.0.windows(2_usize).filter(|records| matches!(records,
                    [Item::Open(Shape::Word), Item::Word(_)]
                        | [Item::Open(Shape::Bytes), Item::Bytes(_)])).count();
                if count == 0_usize { ret == *main } else {
                    main.0.windows(2_usize).enumerate().filter_map(|(at, records)|
                        if matches!(records, [Item::Open(Shape::Word), Item::Word(_)]
                            | [Item::Open(Shape::Bytes), Item::Bytes(_)]) {
                            at.checked_add(1_usize)
                        } else { None }).nth(index.index(count)).is_some_and(|payload|
                            main.0.len() == ret.0.len()
                                && main.0.iter().zip(&ret.0).enumerate().all(|(at, (before, after))|
                                    if at == payload { match (before, after) {
                                        (&Item::Word(before), &Item::Word(after)) => u64::from(after) == !u64::from(before),
                                        (&Item::Bytes(Payload(ref before)), &Item::Bytes(Payload(ref after))) =>
                                            before.split_first().map_or_else(|| after.as_slice() == [0_u8],
                                                |(head, tail)| after.split_first().is_some_and(|(changed, rest)|
                                                    *changed == !*head && rest == tail)),
                                        _ => false,
                                    }} else { before == after }))
                }
            },
        })]
    pub fn resolve(
        &self,
        main: &Tree,
    ) -> Tree
    {
        match *self {
            | Self::Fresh(ref value) => value.clone(),
            | Self::Subtree(index) => {
                let opens = main.opens();
                main.subtree(opens[index.index(opens.len())])
            },
            | Self::Edited(index) => {
                let mut edited = main.clone();
                let leaves = main.leaves();
                if !leaves.is_empty() {
                    edited.edit(leaves[index.index(leaves.len())]);
                }
                edited
            },
            | Self::Itself => main.clone(),
        }
    }
}

/// Which profile a prior value is committed under.
#[derive(Clone, Debug)]
pub enum PriorProfile
{
    /// The law's own.
    Same,
    /// Another generated profile.
    Other(ValueProfile),
}

impl PriorProfile
{
    /// Resolves the prior profile against the law's own.
    ///
    /// # Specification
    /// trivial.
    pub fn resolve(
        &self,
        main: &ValueProfile,
    ) -> ValueProfile
    {
        match *self {
            | Self::Same => *main,
            | Self::Other(other) => other,
        }
    }
}

/// A value a store holds before the law's own, and its profile.
#[derive(Clone, Debug)]
pub struct Prior
{
    /// The value.
    pub value: PriorValue,
    /// The profile it was committed under.
    pub profile: PriorProfile,
}

/// Generates where a prior value comes from, biased toward sharing the law's
/// value.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: weights unrelated fresh trees, selected subtrees, single-leaf
///   edits and the main value itself in the ratio one to two to two to one.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded histories exercise prior commits drawn from
///   these recipes; no frequency assertion substitutes for root equality.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
fn prior_value() -> impl Strategy<Value = PriorValue>
{
    prop_oneof![
        1 => tree().prop_map(PriorValue::Fresh),
        2 => any::<Index>().prop_map(PriorValue::Subtree),
        2 => any::<Index>().prop_map(PriorValue::Edited),
        1 => Just(PriorValue::Itself),
    ]
}

/// Generates a prior value's profile, biased toward the law's own, under
/// which shared subtrees can share chunks.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: weights the main profile three to one against an independently
///   generated supported profile.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 bounded histories distinguish compatible sharing from
///   changed profile identities through exact root equality.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
fn prior_profile() -> impl Strategy<Value = PriorProfile>
{
    prop_oneof![
        3 => Just(PriorProfile::Same),
        1 => profile().prop_map(PriorProfile::Other),
    ]
}

/// Generates a value, its profile, and the values a store holds before it.
///
/// # Specification
/// - requires: nothing beyond the typed arguments.
/// - ensures: samples a bounded main value, its supported absolute profile and
///   zero through six prior value/profile recipes.
/// - fails: never.
/// - panics: none within the bounded generation domain.
/// - executable: none — the opaque strategy exposes no pure observer of its
///   possible samples; drawing a sample advances a runner.
///
/// # Adequacy
/// - hypothesis: L2 256 cases compare the same main commit in an empty store
///   and a store populated by the resolved prior recipes.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
pub fn history() -> impl Strategy<Value = (Tree, ValueProfile, Vec<Prior>)>
{
    (
        tree(),
        profile(),
        proptest::collection::vec(
            (prior_value(), prior_profile()).prop_map(|(value, profile)| Prior { value, profile }),
            0_usize ..= 6_usize,
        ),
    )
}

/// Literal heterogeneous bytes separate schema fields, leaf locations and
/// edits.
#[test]
fn generated_codec_preserves_schema_and_leaf_edits()
{
    let image = [
        1_u8, 0x36, 2, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0x30, 5, 1, 0x31, 2, 8, 7, 6, 5, 4, 3, 2, 1, 5,
        1, 0x32, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 5, 1, 0x33, 1, 0x30, 5, 1, 0x30, 5, 5, 1,
        0x34, 2, 7, 0, 0, 0, 0, 0, 0, 0, 1, 0x31, 2, 11, 0, 0, 0, 0, 0, 0, 0, 5, 5, 1, 0x35, 1,
        0x30, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x30, 5, 5, 1, 0x36, 2, 0, 0, 0, 0, 0, 0, 0, 0, 5,
        1, 0x32, 3, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5,
    ];
    let high = CanonicalWord::from(0x0102_0304_0506_0708_u64);
    let expected = Tree(vec![
        Item::Open(Shape::List),
        Item::Word(8_u64.into()),
        Item::Open(Shape::Unit),
        Item::Close,
        Item::Open(Shape::Word),
        Item::Word(high),
        Item::Close,
        Item::Open(Shape::Bytes),
        Item::Bytes(Payload(vec![0_u8, 0xFF])),
        Item::Close,
        Item::Open(Shape::Pair),
        Item::Open(Shape::Unit),
        Item::Close,
        Item::Open(Shape::Unit),
        Item::Close,
        Item::Close,
        Item::Open(Shape::Tagged),
        Item::Word(7_u64.into()),
        Item::Open(Shape::Word),
        Item::Word(11_u64.into()),
        Item::Close,
        Item::Close,
        Item::Open(Shape::Labelled),
        Item::Open(Shape::Unit),
        Item::Close,
        Item::Bytes(Payload(Vec::new())),
        Item::Open(Shape::Unit),
        Item::Close,
        Item::Close,
        Item::Open(Shape::List),
        Item::Word(0_u64.into()),
        Item::Close,
        Item::Open(Shape::Bytes),
        Item::Bytes(Payload(Vec::new())),
        Item::Close,
        Item::Close,
    ]);
    let decoded = gandr_storage_values::decode_flat::<Tree>(gandr_storage_values::TokenBody::from(
        image.as_slice(),
    ))
    .expect("the literal seven-shape image decodes");
    assert_eq!(decoded, expected);
    assert_eq!(
        gandr_storage_values::encode_flat(&decoded)
            .expect("the value encodes")
            .as_ref(),
        image
    );
    assert!(anodized::types::Spec::predicate(&decoded));
    assert!(
        decoded
            .opens()
            .iter()
            .map(|index| index.0)
            .eq([0_usize, 2, 4, 7, 10, 11, 13, 16, 18, 22, 23, 26, 29, 32])
    );
    assert!(
        decoded
            .inner_closes()
            .iter()
            .map(|index| index.0)
            .eq([3_usize, 6, 9, 12, 14, 15, 20, 21, 24, 27, 28, 31, 34])
    );
    let leaves = [
        Leaf {
            payload: ItemIndex(5_usize),
            depth: EditDepth::from(1_u64),
        },
        Leaf {
            payload: ItemIndex(8_usize),
            depth: EditDepth::from(1_u64),
        },
        Leaf {
            payload: ItemIndex(19_usize),
            depth: EditDepth::from(2_u64),
        },
        Leaf {
            payload: ItemIndex(33_usize),
            depth: EditDepth::from(1_u64),
        },
    ];
    assert_eq!(decoded.leaves(), leaves);
    assert!(leaves.iter().all(anodized::types::Spec::predicate));
    assert_eq!(
        decoded.subtree(ItemIndex(16_usize)),
        Tree(vec![
            Item::Open(Shape::Tagged),
            Item::Word(7_u64.into()),
            Item::Open(Shape::Word),
            Item::Word(11_u64.into()),
            Item::Close,
            Item::Close
        ])
    );
    for (leaf, replacement) in [
        (leaves[0], Item::Word(CanonicalWord::from(!u64::from(high)))),
        (leaves[1], Item::Bytes(Payload(vec![0xFF_u8, 0xFF_u8]))),
        (leaves[3], Item::Bytes(Payload(vec![0_u8]))),
    ] {
        let mut edited = decoded.clone();
        edited.edit(leaf);
        assert!(
            edited
                .0
                .iter()
                .eq(decoded
                    .0
                    .iter()
                    .enumerate()
                    .map(|(index, item)| if index == leaf.payload.0 {
                        &replacement
                    }
                    else {
                        item
                    }))
        );
    }
    for tag in [0x2F_u8, 0x37_u8] {
        let unknown = [1_u8, tag, 5];
        assert_eq!(
            gandr_storage_values::decode_flat::<Tree>(gandr_storage_values::TokenBody::from(
                unknown.as_slice()
            )),
            Err(ValueError::UnexpectedConstructor {
                found: ConstructorTag::from(tag),
                position: gandr_storage_values::TokenOffset::from(1_u32)
            })
        );
    }
    let missing_child = [1_u8, 0x36, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0x30, 5, 5];
    assert_eq!(
        gandr_storage_values::decode_flat::<Tree>(gandr_storage_values::TokenBody::from(
            missing_child.as_slice()
        )),
        Err(ValueError::UnexpectedToken {
            expected: gandr_storage_values::TokenKind::Open,
            found: gandr_storage_values::TokenKind::Close,
            position: gandr_storage_values::TokenOffset::from(4_u32)
        })
    );
}

/// Field state and complete-value admission reject impossible transitions.
#[test]
fn generated_refinements_reject_impossible_states()
{
    let mut fixed = Owed::new(Shape::Labelled);
    for expected in [
        Next::Field(Field::Child),
        Next::Field(Field::Bytes),
        Next::Field(Field::Child),
        Next::Close,
        Next::Close,
    ] {
        assert_eq!(fixed.take(), expected);
    }
    let mut counted = Owed {
        fields: &[],
        children: 2_u64,
    };
    assert_eq!(counted.take(), Next::Field(Field::Child));
    assert_eq!(counted.children, 1_u64);
    assert_eq!(counted.take(), Next::Field(Field::Child));
    assert_eq!(counted.children, 0_u64);
    assert_eq!(counted.take(), Next::Close);
    let mut widest = Owed {
        fields: &[],
        children: u64::MAX,
    };
    assert_eq!(widest.take(), Next::Field(Field::Child));
    assert_eq!(widest.children, u64::MAX.saturating_sub(1_u64));
    assert!(!anodized::types::Spec::predicate(&Owed {
        fields: &[Field::Word],
        children: 1_u64
    }));
    assert!(!anodized::types::Spec::predicate(&Owed {
        fields: &[Field::Word, Field::Word],
        children: 0_u64
    }));
    for leaf in [
        Leaf {
            payload: ItemIndex(0_usize),
            depth: EditDepth::from(0_u64),
        },
        Leaf {
            payload: ItemIndex(1_usize),
            depth: EditDepth::from(1_u64),
        },
    ] {
        assert!(!anodized::types::Spec::predicate(&leaf));
    }
    for items in [
        vec![],
        vec![Item::Close],
        vec![Item::Open(Shape::Unit)],
        vec![
            Item::Open(Shape::Word),
            Item::Bytes(Payload(Vec::new())),
            Item::Close,
        ],
        vec![
            Item::Open(Shape::List),
            Item::Word(2_u64.into()),
            Item::Open(Shape::Unit),
            Item::Close,
            Item::Close,
        ],
        vec![
            Item::Open(Shape::Unit),
            Item::Close,
            Item::Open(Shape::Unit),
            Item::Close,
        ],
    ] {
        assert!(!anodized::types::Spec::predicate(&Tree(items)));
    }
}

/// Reused nodes retain multiplicity; bounded insertion does not constrain
/// decoding.
#[test]
fn arena_counts_and_bounds_keep_semantic_nodes()
{
    let mut arena = Arena::default();
    let word = arena.push(Shape::Word, vec![Slot::Word(7_u64.into())]);
    let unit = arena.push(Shape::Unit, Vec::new());
    let pair = arena.push(Shape::Pair, vec![Slot::Child(word), Slot::Child(word)]);
    let pair_items = vec![
        Item::Open(Shape::Pair),
        Item::Open(Shape::Word),
        Item::Word(7_u64.into()),
        Item::Close,
        Item::Open(Shape::Word),
        Item::Word(7_u64.into()),
        Item::Close,
        Item::Close,
    ];
    assert_eq!(arena.tree(pair).0, pair_items);
    assert_eq!(arena.frontier(), vec![unit, pair]);
    assert_eq!(arena.pick(Back(0_u32)), pair);
    assert_eq!(arena.pick(Back(2_u32)), word);
    assert_eq!(arena.pick(Back(3_u32)), pair);
    assert_eq!(arena.pick(Back(u32::MAX)), pair);
    assert_eq!(
        arena.step(&Step::Spine(SpineLength(0_u32), 99_u64.into(), Back(0_u32))),
        pair
    );
    assert_eq!(arena.frontier(), vec![unit, pair]);
    let spine = arena.step(&Step::Spine(
        SpineLength(2_u32),
        u64::MAX.into(),
        Back(0_u32),
    ));
    let mut spine_items = vec![
        Item::Open(Shape::Tagged),
        Item::Word(0_u64.into()),
        Item::Open(Shape::Tagged),
        Item::Word(u64::MAX.into()),
    ];
    spine_items.extend(pair_items);
    spine_items.extend([Item::Close, Item::Close]);
    assert_eq!(arena.tree(spine).0, spine_items);
    let empty = arena.list(&[]);
    assert_eq!(arena.tree(empty).0, vec![
        Item::Open(Shape::List),
        Item::Word(0_u64.into()),
        Item::Close
    ]);
    let list = arena.list(&[word, unit, word]);
    assert_eq!(arena.tree(list).0, vec![
        Item::Open(Shape::List),
        Item::Word(3_u64.into()),
        Item::Open(Shape::Word),
        Item::Word(7_u64.into()),
        Item::Close,
        Item::Open(Shape::Unit),
        Item::Close,
        Item::Open(Shape::Word),
        Item::Word(7_u64.into()),
        Item::Close,
        Item::Close
    ]);
    assert_eq!(arena.frontier(), vec![spine, empty, list]);
    assert!(anodized::types::Spec::predicate(&arena));

    let mut boundary = Arena::default();
    let unit = boundary.push(Shape::Unit, Vec::new());
    let wide = boundary.list(&vec![unit; 2044_usize]);
    let word = boundary.push(Shape::Word, vec![Slot::Word(7_u64.into())]);
    let edge = boundary.within(Shape::Pair, vec![Slot::Child(word), Slot::Child(wide)]);
    assert_eq!(boundary.tree(edge).0.len(), 4096_usize);
    let unused = boundary.push(Shape::Word, vec![Slot::Word(17_u64.into())]);
    let replaced = boundary.within(Shape::Labelled, vec![
        Slot::Child(unused),
        Slot::Bytes(Payload(Vec::new())),
        Slot::Child(wide),
    ]);
    assert_eq!(boundary.tree(replaced).0, vec![
        Item::Open(Shape::Word),
        Item::Word(u64::MAX.into()),
        Item::Close
    ]);
    assert_eq!(boundary.frontier(), vec![edge, unused, replaced]);
    let unbounded = boundary.push(Shape::Labelled, vec![
        Slot::Child(unused),
        Slot::Bytes(Payload(Vec::new())),
        Slot::Child(wide),
    ]);
    let expanded = boundary.tree(unbounded);
    assert_eq!(expanded.0.len(), 4097_usize);
    assert!(anodized::types::Spec::predicate(&expanded));
    assert_eq!(
        boundary.step(&Step::Spine(SpineLength(0_u32), 0_u64.into(), Back(0_u32))),
        unbounded
    );
    assert!(anodized::types::Spec::predicate(&boundary));

    let mut bounded = Arena::default();
    let mut root = bounded.push(Shape::Word, vec![Slot::Word(7_u64.into())]);
    for _ in 0_u32 .. 9_u32 {
        root = bounded.step(&Step::Twice(Back(0_u32)));
    }
    assert_eq!(bounded.tree(root).0.len(), 2558_usize);
    root = bounded.step(&Step::Twice(Back(0_u32)));
    assert_eq!(bounded.tree(root).0, vec![
        Item::Open(Shape::Word),
        Item::Word(u64::MAX.into()),
        Item::Close
    ]);

    let mut saturated = Arena::default();
    let mut root = saturated.push(Shape::Word, vec![Slot::Word(7_u64.into())]);
    for level in 1_u32 ..= 63_u32 {
        root = saturated.push(Shape::Pair, vec![Slot::Child(root), Slot::Child(root)]);
        let exact = 5_u128
            .checked_shl(level)
            .expect("bounded shift")
            .checked_sub(2_u128)
            .expect("envelope subtraction");
        assert_eq!(
            saturated.0.get(root.0).expect("new node").records.0,
            u64::try_from(exact).unwrap_or(u64::MAX)
        );
    }
    assert!(anodized::types::Spec::predicate(&saturated));
}

/// Local grammar and cross-node metadata reject distinct forged claims.
#[test]
fn arena_refinements_reject_stale_metadata()
{
    for node in [
        Node {
            shape: Shape::Unit,
            slots: Vec::new(),
            records: RecordCount(1_u64),
            nested: Nested(false),
        },
        Node {
            shape: Shape::Word,
            slots: vec![Slot::Bytes(Payload(Vec::new()))],
            records: RecordCount(3_u64),
            nested: Nested(false),
        },
        Node {
            shape: Shape::List,
            slots: vec![Slot::Word(2_u64.into()), Slot::Child(NodeId(0_usize))],
            records: RecordCount(5_u64),
            nested: Nested(false),
        },
    ] {
        assert!(!anodized::types::Spec::predicate(&node));
    }
    let mut arena = Arena::default();
    let word = arena.push(Shape::Word, vec![Slot::Word(7_u64.into())]);
    let unit = arena.push(Shape::Unit, Vec::new());
    let pair = arena.push(Shape::Pair, vec![Slot::Child(word), Slot::Child(unit)]);
    assert!(anodized::types::Spec::predicate(&arena));
    arena.0.get_mut(pair.0).expect("pair").records = RecordCount(6_u64);
    assert!(!anodized::types::Spec::predicate(&arena));
    arena.0.get_mut(pair.0).expect("pair").records = RecordCount(7_u64);
    arena.0.get_mut(word.0).expect("word").nested = Nested(false);
    assert!(!anodized::types::Spec::predicate(&arena));
    arena.0.get_mut(word.0).expect("word").nested = Nested(true);
    arena.0.get_mut(pair.0).expect("pair").nested = Nested(true);
    assert!(!anodized::types::Spec::predicate(&arena));
    arena.0.get_mut(pair.0).expect("pair").nested = Nested(false);
    *arena
        .0
        .get_mut(pair.0)
        .expect("pair")
        .slots
        .first_mut()
        .expect("child") = Slot::Child(pair);
    assert!(!anodized::types::Spec::predicate(&arena));
    *arena
        .0
        .get_mut(pair.0)
        .expect("pair")
        .slots
        .first_mut()
        .expect("child") = Slot::Child(word);
    assert!(anodized::types::Spec::predicate(&arena));
}

/// Root trimming preserves all retained values and only discards the oldest
/// roots.
#[test]
fn builds_preserve_reuse_and_trim_oldest_roots()
{
    let reused = build(&Step::Word(1_u64.into()), &[
        Step::Word(2_u64.into()),
        Step::Pair(Back(0_u32), Back(1_u32)),
    ]);
    assert_eq!(reused.0, vec![
        Item::Open(Shape::Pair),
        Item::Open(Shape::Word),
        Item::Word(2_u64.into()),
        Item::Close,
        Item::Open(Shape::Word),
        Item::Word(1_u64.into()),
        Item::Close,
        Item::Close
    ]);
    let steps: Vec<_> = (1_u64 ..= 1364_u64)
        .map(|word| Step::Word(word.into()))
        .collect();
    let trimmed = build(&Step::Word(0_u64.into()), &steps);
    assert_eq!(trimmed.0.len(), 4095_usize);
    assert_eq!(trimmed.0.first(), Some(&Item::Open(Shape::List)));
    assert_eq!(trimmed.0.get(1_usize), Some(&Item::Word(1364_u64.into())));
    assert!(
        trimmed
            .0
            .iter()
            .skip(2_usize)
            .filter_map(|item| match *item {
                | Item::Word(word) => Some(u64::from(word)),
                | Item::Open(_) | Item::Bytes(_) | Item::Close => None,
            })
            .eq(1_u64 ..= 1364_u64)
    );
    assert!(anodized::types::Spec::predicate(&trimmed));
}

#[cfg(test)]
proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]
    /// Relative recipes select complete subtrees and only genuine payload leaves.
    #[test]
    fn prior_recipes_select_only_tree_values(index in any::<Index>()) {
        let main = Tree(vec![Item::Open(Shape::Labelled), Item::Open(Shape::Tagged),
            Item::Word(0x55_u64.into()), Item::Open(Shape::Word), Item::Word(7_u64.into()),
            Item::Close, Item::Close, Item::Bytes(Payload(vec![0xAA_u8])),
            Item::Open(Shape::Bytes), Item::Bytes(Payload(vec![0_u8, 0xFF_u8])),
            Item::Close, Item::Close]);
        let expected_subtree = [main.0.as_slice(), main.0.get(1_usize..7_usize).expect("tagged child"),
            main.0.get(3_usize..6_usize).expect("word child"), main.0.get(8_usize..11_usize).expect("bytes child")];
        let subtree = PriorValue::Subtree(index).resolve(&main);
        prop_assert_eq!(subtree.0.as_slice(), expected_subtree[index.index(4_usize)]);
        let mut expected_edit = main.clone();
        if index.index(2_usize) == 0_usize {
            *expected_edit.0.get_mut(4_usize).expect("word payload") = Item::Word((!7_u64).into());
        } else {
            *expected_edit.0.get_mut(9_usize).expect("bytes payload") = Item::Bytes(Payload(vec![0xFF_u8, 0xFF_u8]));
        }
        prop_assert_eq!(PriorValue::Edited(index).resolve(&main), expected_edit);
        let empty_pair = Tree(vec![Item::Open(Shape::Pair), Item::Open(Shape::Bytes),
            Item::Bytes(Payload(Vec::new())), Item::Close, Item::Open(Shape::Bytes),
            Item::Bytes(Payload(Vec::new())), Item::Close, Item::Close]);
        let mut expected_growth = empty_pair.clone();
        let payload = if index.index(2_usize) == 0_usize { 2_usize } else { 5_usize };
        *expected_growth.0.get_mut(payload).expect("selected empty payload") = Item::Bytes(Payload(vec![0_u8]));
        prop_assert_eq!(PriorValue::Edited(index).resolve(&empty_pair), expected_growth);
        let leafless = Tree(vec![Item::Open(Shape::Unit), Item::Close]);
        prop_assert_eq!(PriorValue::Edited(index).resolve(&leafless), leafless);
    }
}
