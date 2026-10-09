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
use proptest::prelude::Strategy;
use proptest::prelude::any;
use proptest::prop_oneof;
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
    /// trivial.
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Leaf
{
    /// The payload's item.
    pub payload: ItemIndex,
    /// The constructors enclosing the leaf: zero for the root.
    pub depth: EditDepth,
}

/// A generated value: a constructor tree held as its preorder records.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tree(pub Vec<Item>);

impl Tree
{
    /// Lists every constructor's open record, in preorder.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
    /// - panics: when `open` is not an open record of this value.
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
    /// trivial.
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
    /// - panics: when `leaf` names no payload of this value.
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
    /// trivial.
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
    /// trivial.
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
#[derive(Clone, Debug)]
struct Node
{
    /// The node's shape.
    shape: Shape,
    /// The node's fields, in the order its decoder reads them.
    slots: Vec<Slot>,
    /// The records the node's tree flattens to.
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
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Arena(Vec<Node>);

impl Arena
{
    /// Counts the records a node with these fields flattens to.
    ///
    /// # Specification
    /// trivial.
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
    /// - panics: none.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// - panics: on an empty arena.
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
    /// - ensures: the node the step built last; a node that would pass the
    ///   record budget is built as a word leaf instead.
    /// - provides: a generated step's resolution.
    /// - panics: a step naming a child of an empty arena.
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
    /// - requires: `root` is a node of this arena.
    /// - ensures: the records of `root`'s tree, a node named twice written
    ///   twice.
    /// - provides: the value an arena describes.
    /// - panics: when `root` is not a node of this arena.
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
/// trivial.
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
/// - panics: when `first` names a child.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
pub fn profile() -> impl Strategy<Value = ValueProfile>
{
    kappa()
        .prop_flat_map(|kappa| (Just(kappa), cap(kappa), codec()))
        .prop_map(|(kappa, cap, codec)| profile_of(kappa, cap, codec))
}

/// Generates a value with a profile whose cap a run reaches exactly at one of
/// the value's boundary events, or passes by one record there.
///
/// # Specification
/// trivial.
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

/// Generates the cut rule's inputs: half with a cap at a boundary event, half
/// with any profile.
///
/// # Specification
/// trivial.
pub fn cut_case() -> impl Strategy<Value = (Tree, ValueProfile)>
{
    prop_oneof![value_at_a_cap(), (tree(), profile())]
}

/// Where a value committed before the law's own value comes from.
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
    /// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
