//! Alias and boundary constructors: under a tagged classification a commit
//! cuts only at boundaries and reads back, or refuses an alias region the
//! classification leaves unbounded; a seam at an alias is refused by name.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::BoundaryClassification;
use gandr_storage_values::BoundaryTags;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkStore as _;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorClass;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use gandr_storage_values::encode_flat;
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prop_assert;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;

use crate::common::Fixture;
use crate::common::LEAF;
use crate::common::Node;
use crate::common::PAIR;
use crate::generate::Item;
use crate::generate::Shape;
use crate::generate::Tree;
use crate::generate::profile;
use crate::generate::tree;
use crate::reference::Kind;
use crate::reference::records;
use crate::reference::reference_cuts;
use crate::reference::splice;

/// A set of the generated shapes, one bit per shape in [`Shape::ALL`] order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ShapeMask(u8);

impl ShapeMask
{
    /// What `shape` is under the mask: a boundary when the mask names it.
    ///
    /// # Specification
    /// trivial.
    fn class(
        self,
        shape: Shape,
    ) -> ConstructorClass
    {
        let named = Shape::ALL
            .iter()
            .position(|&each| each == shape)
            .is_some_and(|bit| self.0 & (1_u8 << bit) != 0_u8);
        if named {
            ConstructorClass::Boundary
        }
        else {
            ConstructorClass::Alias
        }
    }

    /// The boundary set naming the masked shapes' tags.
    ///
    /// # Specification
    /// trivial.
    fn boundaries(self) -> BoundaryTags
    {
        Shape::ALL
            .into_iter()
            .filter(|&shape| self.class(shape) == ConstructorClass::Boundary)
            .fold(BoundaryTags::EMPTY, |tags, shape| tags.with(shape.tag()))
    }
}

/// The masks a classification is drawn from: any set of shapes, every
/// container a boundary with the leaves drawn, or one container an alias.
///
/// # Specification
/// trivial.
fn mask() -> impl Strategy<Value = ShapeMask>
{
    // Unit, Word and Bytes are bits zero to two; Pair, Tagged, Labelled and
    // List three to six.
    let containers = 0x78_u8;
    prop_oneof![
        (0_u8 .. 0x80_u8).prop_map(ShapeMask),
        (0_u8 .. 0x08_u8).prop_map(move |leaves| ShapeMask(leaves | containers)),
        (0_u8 .. 0x08_u8, 3_u8 .. 7_u8).prop_map(move |(leaves, alias)| {
            ShapeMask(leaves | (containers & !(1_u8 << alias)))
        }),
    ]
}

/// The open a commit under `mask` refuses as a recursive alias, read off the
/// value's items alone: the first alias open whose shape is already open as an
/// alias since the innermost open boundary.
///
/// # Specification
/// trivial.
fn first_recursive_alias(
    value: &Tree,
    mask: ShapeMask,
) -> Option<ValueError>
{
    let mut outside: Vec<BTreeSet<Shape>> = Vec::new();
    let mut region = BTreeSet::new();
    for (index, item) in value.0.iter().enumerate() {
        match *item {
            Item::Open(shape) => {
                let enclosing = core::mem::take(&mut region);
                if mask.class(shape) == ConstructorClass::Alias {
                    if enclosing.contains(&shape) {
                        return Some(ValueError::RecursiveAlias {
                            tag: shape.tag(),
                            position: TokenCount::from(u64::try_from(index).expect("an index")),
                        });
                    }
                    region.clone_from(&enclosing);
                    let _added = region.insert(shape);
                }
                outside.push(enclosing);
            },
            Item::Close => region = outside.pop().unwrap_or_default(),
            Item::Word(_) | Item::Bytes(_) => {},
        }
    }

    None
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Under a generated tagged classification a generated value either
    /// commits — and then derefs back equal, its cuts are the ones a reference
    /// scanner finds when only boundary exits are events, and its closure
    /// passes — or is refused as a recursive alias exactly where a reading of
    /// its items alone finds one.
    #[test]
    fn a_tagged_commit_reads_back_or_refuses_an_unbounded_alias(
        value in tree(),
        profile in profile(),
        mask in mask(),
    ) {
        let classification = BoundaryClassification::Tagged(mask.boundaries());
        let profile = profile.classified(classification);
        let refused = first_recursive_alias(&value, mask);
        let mut store = InMemoryChunkStore::new();
        match cam_commit(&mut store, &profile, &value) {
            Ok(manifest) => {
                prop_assert_eq!(refused, None);
                let back: Tree = cam_deref(&store, manifest.root()).expect("its root derefs");
                prop_assert_eq!(&back, &value);
                let flat = encode_flat(&value).expect("a generated value encodes flat");
                let expected = reference_cuts(flat.as_body(), &profile.params(), classification);
                prop_assert_eq!(splice(&store, manifest.root()).chunk_starts, expected);
                prop_assert!(manifest.closure(&store).is_ok());
            },
            Err(error) => prop_assert_eq!(Some(error), refused),
        }
    }
}

/// A pair of two leaves committed at kappa one, so each leaf stands in a chunk
/// of its own, is refused by a closure under a classification that keeps the
/// pair a boundary and makes the leaf an alias, naming the leaf's tag and the
/// first leaf's chunk; under the classification it was committed with, the
/// closure passes.
#[test]
fn a_seam_at_an_alias_is_refused_by_name()
{
    let value = Fixture(vec![
        Node::Pair,
        Node::Leaf(CanonicalWord::from(7_u64)),
        Node::Leaf(CanonicalWord::from(11_u64)),
    ]);
    let profile = ValueProfile::new(
        TypedChunkerParams::new(
            Kappa::try_from(1_u64).expect("nonzero kappa"),
            TokenCap::try_from(64_u64).expect("a nonzero cap"),
        ),
        CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16)),
        ChildIndexBase::Absolute,
    );
    let mut store = InMemoryChunkStore::new();
    let committed = cam_commit(&mut store, &profile, &value).expect("the pair commits");
    assert!(committed.closure(&store).is_ok());

    let root = store
        .load(committed.root().digest())
        .expect("the root chunk is stored");
    let first_child = records(root.body())
        .into_iter()
        .find_map(|record| match record.kind {
            Kind::Child(pointer) => Some(pointer.digest()),
            Kind::Open | Kind::Word | Kind::Bytes | Kind::Close => None,
        })
        .expect("kappa one cuts the first leaf");
    let leaf_an_alias = ValueManifest::new(
        profile.classified(BoundaryClassification::Tagged(
            BoundaryTags::EMPTY.with(ConstructorTag::from(PAIR)),
        )),
        committed.root(),
        committed.token_count(),
    );

    assert_eq!(
        leaf_an_alias.closure(&store),
        Err(ValueError::AliasSeam {
            tag: ConstructorTag::from(LEAF),
            digest: first_child,
        })
    );
}
