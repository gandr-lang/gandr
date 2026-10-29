//! A value committed out of one store and dereferenced into another: the
//! round trip over every crossing head and literal kind, one root however a
//! value is stored, sharing unfolded, the refusals by name.

use alloc::sync::Arc;

use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConstructorTag as Head;
use gandr_core_sequent::Environment;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::Store;
use gandr_core_term::CoreArena;
use gandr_core_term::FieldLabel;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::CharacterLiteral;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Float64Literal;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_runtime_emitter::crossing::CrossingRefusal;
use gandr_runtime_emitter::crossing::Uncrossable;
use gandr_runtime_emitter::crossing::commit;
use gandr_runtime_emitter::crossing::deref;
use gandr_runtime_emitter::crossing::profile;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::EmissionFault;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ProfileField;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::cam_commit;

/// The chunker's constants these witnesses commit under.
///
/// # Specification
/// trivial.
fn params() -> TypedChunkerParams
{
    TypedChunkerParams::new(
        Kappa::try_from(4_u64).expect("nonzero kappa"),
        TokenCap::try_from(64_u64).expect("nonzero cap"),
    )
}

/// Allocate `value` in `store`.
///
/// # Specification
/// trivial.
fn put(
    store: &mut Store,
    value: HeapValue,
) -> HeapValueId
{
    store.allocate(value).expect("room")
}

/// The integer `digits`, of `sign`.
///
/// # Specification
/// trivial.
fn integer(
    sign: Sign,
    digits: String,
) -> Literal
{
    Literal::Integer(IntegerLiteral::new(
        sign,
        Magnitude::from_decimal_text(digits).expect("decimal digits"),
    ))
}

/// The literal `literal` in `store`.
///
/// # Specification
/// trivial.
fn literal(
    store: &mut Store,
    literal: Literal,
) -> HeapValueId
{
    put(store, HeapValue::Literal(literal))
}

/// The constructed value `tag` over `fields` in `store`.
///
/// # Specification
/// trivial.
fn constructed(
    store: &mut Store,
    tag: Head,
    fields: &[HeapValueId],
) -> HeapValueId
{
    put(store, HeapValue::Constructed {
        tag,
        fields: fields.into(),
    })
}

/// The tuple of `fields` in `store`.
///
/// # Specification
/// trivial.
fn tuple(
    store: &mut Store,
    fields: &[HeapValueId],
) -> HeapValueId
{
    constructed(
        store,
        Head::Tuple(ProducerArity::from(fields.len())),
        fields,
    )
}

/// The thunk suspending command `body` over `captures`, innermost first, in
/// `store`.
///
/// # Specification
/// trivial.
fn thunk(
    store: &mut Store,
    body: CommandId,
    captures: &[HeapValueId],
) -> HeapValueId
{
    let environment = captures
        .iter()
        .rev()
        .try_fold(Environment::EMPTY, |environment, &value| {
            store.bind_value(environment, value)
        })
        .expect("the store binds");
    put(store, HeapValue::Thunk { body, environment })
}

/// Assert the value `left` binds at `here` and the one `right` binds at
/// `there` are equal as trees, wherever and however each is stored.
///
/// # Specification
/// trivial.
///
/// # Panics
/// At the first two values that differ, naming both.
fn assert_same(
    (left, here): (&Store, HeapValueId),
    (right, there): (&Store, HeapValueId),
)
{
    let mut pending = vec![(here, there)];
    while let Some((here, there)) = pending.pop() {
        match (left.value(here), right.value(there)) {
            (Some(&HeapValue::Literal(ref ours)), Some(&HeapValue::Literal(ref theirs)))
                if ours == theirs => {},
            (
                Some(&HeapValue::Constructed {
                    tag: ref ours,
                    fields: ref our_fields,
                }),
                Some(&HeapValue::Constructed {
                    tag: ref theirs,
                    fields: ref their_fields,
                }),
            ) if ours == theirs && our_fields.len() == their_fields.len() => {
                pending.extend(our_fields.iter().copied().zip(their_fields.iter().copied()));
            },
            (
                Some(&HeapValue::Thunk {
                    body: ours,
                    environment: our_environment,
                }),
                Some(&HeapValue::Thunk {
                    body: theirs,
                    environment: their_environment,
                }),
            ) if ours == theirs => {
                let our_captures: Vec<HeapValueId> = left.bound_values(our_environment).collect();
                let their_captures: Vec<HeapValueId> =
                    right.bound_values(their_environment).collect();
                assert_eq!(
                    our_captures.len(),
                    their_captures.len(),
                    "{here:?} and {there:?} capture alike"
                );
                pending.extend(our_captures.into_iter().zip(their_captures));
            },
            (ours, theirs) => panic!("{here:?} is {ours:?} where {there:?} is {theirs:?}"),
        }
    }
}

/// Every address the value `store` binds at `root` reaches, once per
/// occurrence.
///
/// # Specification
/// trivial.
fn reached(
    store: &Store,
    root: HeapValueId,
) -> Vec<HeapValueId>
{
    let mut seen = Vec::new();
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        seen.push(id);
        match store.value(id) {
            Some(&HeapValue::Constructed { ref fields, .. }) => {
                pending.extend(fields.iter().copied());
            },
            Some(&HeapValue::Thunk { environment, .. }) => {
                pending.extend(store.bound_values(environment));
            },
            _ => {},
        }
    }
    seen
}

/// One value of every crossing head and every literal kind, the heads at
/// their edges: the unit, the record of no labels, a lift at a join of two
/// atoms, a family named and not, a thunk over no capture and over several in
/// their order, its body's index up to the widest.
///
/// # Specification
/// trivial.
fn every_head(store: &mut Store) -> Vec<HeapValueId>
{
    let mut values = Vec::new();
    for literal in [
        integer(Sign::NonNegative, "0".into()),
        integer(Sign::Negative, "123456789012345678901234567890".into()),
        Literal::Text(StringLiteral::new(String::new())),
        Literal::Text(StringLiteral::new("a\0é".into())),
        Literal::Numeric(NumericLiteral::new(
            Sign::Negative,
            Magnitude::from_decimal_text("12".into()).expect("digits"),
            FractionDigits::from_decimal_text("034".into()).expect("digits"),
        )),
        Literal::Character(CharacterLiteral::from('é')),
        Literal::Character(CharacterLiteral::from('\u{10FFFF}')),
        Literal::Float64(Float64Literal::from(0.5_f64)),
        Literal::Float64(Float64Literal::from(-0.0_f64)),
        Literal::Float64(Float64Literal::from(f64::NAN)),
        Literal::Fixed(FixedInteger::U32(u32::MAX)),
        Literal::Fixed(FixedInteger::U64(7)),
        Literal::Fixed(FixedInteger::I32(-1)),
        Literal::Fixed(FixedInteger::I64(i64::MIN)),
    ] {
        values.push(self::literal(store, literal));
    }
    let one = literal(store, integer(Sign::NonNegative, "1".into()));
    let text = literal(store, Literal::Text(StringLiteral::new("two".into())));
    values.push(tuple(store, &[]));
    values.push(tuple(store, &[one, text, one]));
    values.push(constructed(store, Head::Record(Arc::from([])), &[]));
    let labels: Arc<[FieldLabel]> =
        Arc::from([FieldLabel::from(String::from("a")), "b".to_owned().into()]);
    values.push(constructed(store, Head::Record(labels), &[one, text]));
    let nil = constructed(store, Head::ListNil, &[]);
    values.push(nil);
    values.push(constructed(store, Head::ListCons, &[one, nil]));
    values.push(constructed(
        store,
        Head::Injection(Summand::from(1_usize)),
        &[text],
    ));
    values.push(constructed(store, Head::Lift(Level::zero()), &[one]));
    let atom = |index: u32| Level::var(LevelVar::new(LevelVarIndex::from(index)));
    let join = Level::constant(LevelConstant::from(1_u64))
        .max(
            &atom(0)
                .succ()
                .and_then(|level| level.succ())
                .expect("a level"),
        )
        .max(&atom(3));
    values.push(constructed(store, Head::Lift(join), &[one]));
    for family in [None, Some(ConstantIndex::from(7_usize))] {
        values.push(constructed(
            store,
            Head::Data {
                tag: gandr_kernel_term::ConstructorTag::from(0_usize),
                arity: ProducerArity::from(0_usize),
                family,
            },
            &[],
        ));
        values.push(constructed(
            store,
            Head::Data {
                tag: gandr_kernel_term::ConstructorTag::from(2_usize),
                arity: ProducerArity::from(2_usize),
                family,
            },
            &[one, nil],
        ));
    }
    values.push(thunk(store, CommandId::from(0_u32), &[]));
    values.push(thunk(store, CommandId::from(9_u32), &[one, text]));
    values.push(thunk(store, CommandId::from(u32::MAX), &[text, one, nil]));
    let nested = values.clone();
    values.push(tuple(store, &nested));
    values
}

/// Every crossing head, every literal kind and a tuple of them all commit
/// from one store and deref back equal into another, empty or already
/// holding values, at addresses fresh there.
#[test]
fn every_crossing_head_commits_and_derefs_back_equal()
{
    let mut source = Store::new();
    let values = every_head(&mut source);
    let mut held = Store::new();
    let earlier = every_head(&mut held);
    let floor = earlier
        .iter()
        .copied()
        .map(u32::from)
        .max()
        .expect("held values");
    for value in values {
        let mut chunks = InMemoryChunkStore::new();
        let manifest = commit(&source, value, params(), &mut chunks).expect("crosses");
        let mut empty = Store::new();
        let there = deref(&manifest, params(), &chunks, &mut empty).expect("derefs");
        assert_same((&source, value), (&empty, there));
        let there = deref(&manifest, params(), &chunks, &mut held).expect("derefs");
        assert_same((&source, value), (&held, there));
        assert!(
            reached(&held, there)
                .into_iter()
                .all(|id| u32::from(id) > floor),
            "a deref lays every value fresh: {:?}",
            source.value(value)
        );
    }
}

/// A value read under constants other than those it was committed under is
/// refused naming the chunker's commitment, before its chunks are read.
#[test]
fn a_value_read_under_other_constants_is_refused()
{
    let mut store = Store::new();
    let one = literal(&mut store, integer(Sign::NonNegative, "1".into()));
    let pair = tuple(&mut store, &[one, one]);
    let mut chunks = InMemoryChunkStore::new();
    let manifest = commit(&store, pair, params(), &mut chunks).expect("crosses");
    let other = TypedChunkerParams::new(
        Kappa::try_from(8_u64).expect("nonzero kappa"),
        TokenCap::try_from(64_u64).expect("nonzero cap"),
    );
    assert_eq!(
        deref(
            &manifest,
            other,
            &InMemoryChunkStore::new(),
            &mut Store::new()
        ),
        Err(CrossingRefusal::Plane(ValueError::IncompatibleProfile {
            field: ProfileField::ChunkerCommitment,
        }))
    );
}

/// One value commits to one root wherever it stands and however it shares:
/// `((1, 2), (1, 2))` built with its pair twice, and after other values with
/// its pair once and held by both fields.
#[test]
fn one_value_commits_to_one_root_from_any_store()
{
    let mut apart = Store::new();
    let one = literal(&mut apart, integer(Sign::NonNegative, "1".into()));
    let two = literal(&mut apart, integer(Sign::NonNegative, "2".into()));
    let left = tuple(&mut apart, &[one, two]);
    let one = literal(&mut apart, integer(Sign::NonNegative, "1".into()));
    let two = literal(&mut apart, integer(Sign::NonNegative, "2".into()));
    let right = tuple(&mut apart, &[one, two]);
    let unshared = tuple(&mut apart, &[left, right]);

    let mut shared = Store::new();
    let _earlier = every_head(&mut shared);
    let one = literal(&mut shared, integer(Sign::NonNegative, "1".into()));
    let two = literal(&mut shared, integer(Sign::NonNegative, "2".into()));
    let pair = tuple(&mut shared, &[one, two]);
    let twice = tuple(&mut shared, &[pair, pair]);

    let mut chunks = InMemoryChunkStore::new();
    let first = commit(&apart, unshared, params(), &mut chunks).expect("crosses");
    let second = commit(&shared, twice, params(), &mut chunks).expect("crosses");
    assert_eq!(first.root(), second.root());
    assert_eq!(first.identity(), second.identity());
}

/// A value two fields share derefs as two equal values, one per field:
/// `(p, p)` for `p = (1, "two")`.
#[test]
fn a_shared_value_derefs_unshared_and_equal()
{
    let mut store = Store::new();
    let one = literal(&mut store, integer(Sign::NonNegative, "1".into()));
    let text = literal(&mut store, Literal::Text(StringLiteral::new("two".into())));
    let pair = tuple(&mut store, &[one, text]);
    let shared = tuple(&mut store, &[pair, pair]);
    let mut chunks = InMemoryChunkStore::new();
    let manifest = commit(&store, shared, params(), &mut chunks).expect("crosses");
    let mut there = Store::new();
    let root = deref(&manifest, params(), &chunks, &mut there).expect("derefs");
    let Some(&HeapValue::Constructed { ref fields, .. }) = there.value(root)
    else {
        panic!("a tuple");
    };
    let &[left, right] = &**fields
    else {
        panic!("two fields");
    };
    assert_ne!(left, right, "the shared pair is laid twice");
    assert_same((&store, pair), (&there, left));
    assert_same((&store, pair), (&there, right));
    let mut ids = reached(&there, root);
    let count = ids.len();
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), count, "the deref lays a tree");
}

/// A list of fifty thousand cells, nested as deep as it is long, crosses
/// whole.
#[test]
fn a_long_list_crosses()
{
    let mut store = Store::new();
    let mut list = constructed(&mut store, Head::ListNil, &[]);
    for index in 0_u32 .. 50_000_u32 {
        let element = literal(&mut store, integer(Sign::NonNegative, index.to_string()));
        list = constructed(&mut store, Head::ListCons, &[element, list]);
    }
    let mut chunks = InMemoryChunkStore::new();
    let manifest = commit(&store, list, params(), &mut chunks).expect("crosses");
    let mut there = Store::new();
    let root = deref(&manifest, params(), &chunks, &mut there).expect("derefs");
    assert_same((&store, list), (&there, root));
}

/// Each value that does not cross, held in a tuple's second field after an
/// integer, is refused naming its address and what it is, and nothing is
/// written; so is a capability a thunk there captures, though the thunk itself
/// crosses.
#[test]
fn a_value_that_does_not_cross_is_refused_by_name_and_writes_nothing()
{
    let mut core = CoreArena::new();
    let code = core.value_literal(integer(Sign::NonNegative, "0".into()));
    let cases = [
        (
            HeapValue::Stack {
                frames: Box::new([]),
            },
            Uncrossable::Stack,
        ),
        (
            HeapValue::Fixpoint {
                body: CommandId::from(0_u32),
                environment: Environment::EMPTY,
                evidence: FixpointEvidence::Partial,
            },
            Uncrossable::Fixpoint,
        ),
        (
            HeapValue::Closure {
                producer: ProducerId::from(0_u32),
                environment: Environment::EMPTY,
            },
            Uncrossable::Closure,
        ),
        (
            HeapValue::Opaque(ConstantIndex::from(0_usize)),
            Uncrossable::Opaque,
        ),
        (HeapValue::Code(code), Uncrossable::Code),
        (HeapValue::Capability, Uncrossable::Capability),
        (
            HeapValue::Free {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            },
            Uncrossable::Accumulator,
        ),
        (
            HeapValue::Constructed {
                tag: Head::Recorded(Arc::from([])),
                fields: Box::new([]),
            },
            Uncrossable::Recorded,
        ),
        (
            HeapValue::Constructed {
                tag: Head::Dialogue(Arc::from([])),
                fields: Box::new([]),
            },
            Uncrossable::Dialogue,
        ),
        (
            HeapValue::Constructed {
                tag: Head::Web(Arc::from([])),
                fields: Box::new([]),
            },
            Uncrossable::Web,
        ),
    ];
    for (refused, head) in cases {
        let mut store = Store::new();
        let one = literal(&mut store, integer(Sign::NonNegative, "1".into()));
        let value = put(&mut store, refused);
        let pair = tuple(&mut store, &[one, value]);
        let mut chunks = InMemoryChunkStore::new();
        assert_eq!(
            commit(&store, pair, params(), &mut chunks).map(|manifest| manifest.root()),
            Err(CrossingRefusal::Uncrossable { value, head })
        );
        assert_eq!(
            usize::from(chunks.chunk_count()),
            0_usize,
            "{head:?} wrote nothing"
        );
    }
    let mut store = Store::new();
    let one = literal(&mut store, integer(Sign::NonNegative, "1".into()));
    let capability = put(&mut store, HeapValue::Capability);
    let suspended = thunk(&mut store, CommandId::from(0_u32), &[one, capability]);
    let pair = tuple(&mut store, &[one, suspended]);
    let mut chunks = InMemoryChunkStore::new();
    assert_eq!(
        commit(&store, pair, params(), &mut chunks).map(|manifest| manifest.root()),
        Err(CrossingRefusal::Uncrossable {
            value: capability,
            head: Uncrossable::Capability,
        })
    );
    assert_eq!(
        usize::from(chunks.chunk_count()),
        0_usize,
        "a thunk's capture wrote nothing"
    );
}

/// One record of a hand-written emission.
#[derive(Clone, Copy, Debug)]
enum Step
{
    /// An open with this tag.
    Open(u8),
    /// A word.
    Word(u64),
    /// A byte string.
    Bytes(&'static [u8]),
    /// A close.
    Close,
}

/// A hand-written emission, committed as it is written.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Written(&'static [Step]);

impl CanonicalValue for Written
{
    /// Emit the steps in order.
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
        for step in self.0 {
            match *step {
                Step::Open(tag) => sink.open(ConstructorTag::from(tag))?,
                Step::Word(word) => sink.word(CanonicalWord::from(word))?,
                Step::Bytes(bytes) => sink.bytes(TokenBytes::from(bytes))?,
                Step::Close => sink.close()?,
            }
        }
        Ok(())
    }

    /// Never read: a witness reads what it wrote through the codec.
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

/// Each payload the codec does not write refuses its constructor at its open
/// record, as a tag the codec does not write does; a constructor nested under
/// a tuple's open and arity stands at record 2. The tags are the codec's wire
/// layout: an integer `0x01`, text `0x02`, a numeric `0x03`, a character
/// `0x04`, a width integer `0x06`, a tuple `0x10`, a record `0x11`.
#[test]
fn a_payload_the_codec_does_not_write_refuses_its_constructor()
{
    use Step::Bytes;
    use Step::Close;
    use Step::Open;
    use Step::Word;
    let cases: [(&'static [Step], u8, u32); 11] = [
        (&[Open(0x01), Word(0), Bytes(b"1x"), Close], 0x01, 0),
        (&[Open(0x01), Word(0), Bytes(b""), Close], 0x01, 0),
        (&[Open(0x01), Word(2), Bytes(b"1"), Close], 0x01, 0),
        (&[Open(0x02), Bytes(&[0xFF]), Close], 0x02, 0),
        (
            &[Open(0x03), Word(0), Bytes(b"1"), Bytes(b"5x"), Close],
            0x03,
            0,
        ),
        (&[Open(0x04), Word(0xD800), Close], 0x04, 0),
        (&[Open(0x06), Word(4), Word(0), Close], 0x06, 0),
        (&[Open(0x06), Word(0), Word(1 << 32), Close], 0x06, 0),
        (
            &[Open(0x11), Word(2), Bytes(b"b"), Bytes(b"a"), Close],
            0x11,
            0,
        ),
        (&[Open(0x7F), Close], 0x7F, 0),
        (
            &[
                Open(0x10),
                Word(1),
                Open(0x01),
                Word(0),
                Bytes(b"-1"),
                Close,
                Close,
            ],
            0x01,
            2,
        ),
    ];
    for (steps, tag, at) in cases {
        let mut chunks = InMemoryChunkStore::new();
        let manifest = cam_commit(&mut chunks, &profile(params()), &Written(steps))
            .expect("the emission commits");
        assert_eq!(
            deref(&manifest, params(), &chunks, &mut Store::new()),
            Err(CrossingRefusal::Plane(ValueError::UnexpectedConstructor {
                found: ConstructorTag::from(tag),
                position: TokenOffset::from(at),
            })),
            "{steps:?}"
        );
    }
}
