//! A command's image over the named programs: each program reads back from
//! its bytes, checks, and runs as its first command runs. A node that names
//! a core annotation is refused by name, and bytes with a fault are refused
//! by name.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::NodeAddress;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_runtime_emitter::image::Annotated;
use gandr_runtime_emitter::image::ImageRefusal;
use gandr_runtime_emitter::image::Uncodable;
use gandr_runtime_emitter::image::encode;
use gandr_runtime_emitter::image::read;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::DecodeWork;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::encode_flat;

use crate::support::Label;
use crate::support::agree;
use crate::support::focus;
use crate::support::named;

/// Each named program that reaches no core annotation writes its image,
/// reads it back into a fresh arena that checks, and answers on both tiers
/// what its first command answers. Its image read back writes the same
/// bytes. Each other program is refused by the kind of annotation that it
/// reaches, and the counts are stated.
#[test]
fn each_named_program_reads_back_and_runs_alike()
{
    let definitions = Definitions::new();
    let mut written = 0_usize;
    let mut refused = Vec::new();
    for named in named() {
        let name = named.program.name;
        let (arena, root) = focus(&named.program);
        let bytes = match encode(&arena, &definitions, root) {
            Ok(bytes) => bytes,
            Err(ImageRefusal::Uncodable {
                form: Uncodable::Annotation(kind),
                ..
            }) => {
                refused.push(kind);
                continue;
            },
            Err(refusal) => panic!("{name}: the image writes: {refusal}"),
        };
        let back = read(bytes.as_body())
            .unwrap_or_else(|refusal| panic!("{name}: the bytes read back: {refusal}"));
        assert_eq!(
            agree(Label(name), &arena, &definitions, root),
            agree(Label(name), &back.arena, &back.definitions, back.root),
            "{name}: the read command answers as the first"
        );
        assert_eq!(
            encode(&back.arena, &back.definitions, back.root).as_ref(),
            Ok(&bytes),
            "{name}: the read command writes the same bytes"
        );
        written = written.saturating_add(1);
    }
    assert_eq!(
        (written, refused),
        (29, vec![
            Annotated::Fold,
            Annotated::Handle,
            Annotated::Handle,
            Annotated::Handle
        ])
    );
}

/// Two focuses of each named program, each into an arena of its own, give
/// equal bytes.
#[test]
fn two_focuses_give_equal_bytes()
{
    let definitions = Definitions::new();
    for named in named() {
        let (first, first_root) = focus(&named.program);
        let (second, second_root) = focus(&named.program);
        assert_eq!(
            encode(&first, &definitions, first_root),
            encode(&second, &definitions, second_root),
            "{}",
            named.program.name
        );
    }
}

/// A command with a code is refused by name, with the code's address.
#[test]
fn an_annotation_is_refused_by_name()
{
    let mut arena = CommandArena::new();
    let annotations = arena.annotations_mut();
    let unit = annotations.value_type_unit();
    let quoted = annotations.value_quote(unit);
    let code = arena
        .mint_producer(ProducerNode::Code(quoted))
        .expect("a code mints");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("the top mints");
    let root = arena
        .mint_cut(gandr_theory_cell_complexes::Polarity::Positive, code, top)
        .expect("a cut mints");
    assert_eq!(
        encode(&arena, &Definitions::new(), root),
        Err(ImageRefusal::Uncodable {
            node: NodeAddress::Producer(code),
            form: Uncodable::Annotation(Annotated::Code),
        })
    );
}

/// One record of a hand-written image.
#[derive(Clone, Copy, Debug)]
enum Record
{
    /// A constructor opens.
    Open(u8),
    /// A word.
    Word(u64),
    /// The innermost constructor closes.
    Close,
}

/// A value that writes `records` as they stand.
#[repr(transparent)]
struct Script(&'static [Record]);

impl CanonicalValue for Script
{
    /// Write each record.
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
        self.0.iter().try_for_each(|&record| match record {
            Record::Open(tag) => sink.open(ConstructorTag::from(tag)),
            Record::Word(word) => sink.word(CanonicalWord::from(word)),
            Record::Close => sink.close(),
        })
    }

    /// A script is written, never read.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens<Store>(_reader: &mut TokenReader<'_, Store>) -> Result<Self, ValueError>
    where
        Store: gandr_storage_values::ChunkStore,
    {
        Err(ValueError::TruncatedStream {
            position: TokenOffset::ZERO,
        })
    }
}

/// The read of `records`.
///
/// # Specification
/// trivial.
fn read_script(records: &'static [Record]) -> Result<CommandId, ImageRefusal>
{
    let bytes = encode_flat(&Script(records)).map_err(ImageRefusal::Plane)?;
    read(bytes.as_body()).map(|back| back.root)
}

/// The image's open and counts: one producer, one consumer, one command, no
/// definition, the root at command zero.
const HEAD: [Record; 6] = [
    Record::Open(0x01),
    Record::Word(1),
    Record::Word(1),
    Record::Word(1),
    Record::Word(0),
    Record::Word(0),
];

/// A tag that no node has, a child that stands after its parent, a count
/// past the ceiling and bytes after the image are each refused by name.
#[test]
fn each_fault_of_the_bytes_is_refused_by_name()
{
    static UNKNOWN: [Record; 9] = [
        HEAD[0],
        HEAD[1],
        HEAD[2],
        HEAD[3],
        HEAD[4],
        HEAD[5],
        Record::Open(0x7f),
        Record::Close,
        Record::Close,
    ];
    // The cut stands before the unit and the top that it names.
    static FORWARD: [Record; 18] = [
        HEAD[0],
        HEAD[1],
        HEAD[2],
        HEAD[3],
        HEAD[4],
        HEAD[5],
        Record::Open(0x64),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Close,
        Record::Open(0x26),
        Record::Open(0x10),
        Record::Word(0),
        Record::Close,
        Record::Word(0),
        Record::Word(0),
        Record::Close,
    ];
    static ORDERED: [Record; 21] = [
        HEAD[0],
        HEAD[1],
        HEAD[2],
        HEAD[3],
        HEAD[4],
        HEAD[5],
        Record::Open(0x26),
        Record::Open(0x10),
        Record::Word(0),
        Record::Close,
        Record::Word(0),
        Record::Word(0),
        Record::Close,
        Record::Open(0x47),
        Record::Close,
        Record::Open(0x64),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Close,
        Record::Close,
    ];
    static PAST: [Record; 7] = [
        Record::Open(0x01),
        Record::Word((1 << 24) + 1),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Close,
    ];
    assert_eq!(
        read_script(&UNKNOWN),
        Err(ImageRefusal::Plane(ValueError::UnexpectedConstructor {
            found: ConstructorTag::from(0x7f),
            position: TokenOffset::from(6_u32),
        })),
        "a tag that no node has"
    );
    assert_eq!(
        read_script(&ORDERED),
        Ok(CommandId::from(0_u32)),
        "the unit sent to the top"
    );
    let forward: Vec<Record> = FORWARD
        .iter()
        .copied()
        .chain([Record::Open(0x47), Record::Close, Record::Close])
        .collect();
    let forward: &'static [Record] = Vec::leak(forward);
    assert_eq!(
        read_script(forward),
        Err(ImageRefusal::Mint(
            gandr_core_sequent::MintRefusal::DanglingProducer(ProducerId::from(0_u32))
        )),
        "a child after its parent"
    );
    assert_eq!(
        read_script(&PAST),
        Err(ImageRefusal::Plane(ValueError::DecodeBudgetExceeded {
            spent: DecodeWork::from((1_u64 << 24_u32) + 1_u64),
            ceiling: DecodeWork::from(1_u64 << 24_u32),
        })),
        "a count past the ceiling"
    );
    let (commands, root) = focus(&named().swap_remove(0).program);
    let image = encode(&commands, &Definitions::new(), root).expect("a named program writes");
    let tail = encode_flat(&Script(&[Record::Open(0x47), Record::Close])).expect("a script writes");
    let mut trailing = image.as_body().as_ref().to_vec();
    trailing.extend_from_slice(tail.as_body().as_ref());
    let records = read(TokenBody::from(trailing.as_slice()));
    assert!(
        matches!(
            records,
            Err(ImageRefusal::Plane(ValueError::TrailingTokens { .. }))
        ),
        "bytes after the image: {records:?}"
    );
}
