//! The value plane's laws: property differentials over generated values and
//! profiles, and two fixed witnesses — the adversarial ceiling at kappa one,
//! and the snapshot clause of exclusivity.

use alloc::collections::BTreeSet;

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::FlatBytes;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use gandr_storage_values::decode_flat;
use gandr_storage_values::encode_flat;
use gandr_storage_values::measure_edit;
use proptest::prelude::ProptestConfig;
use proptest::prop_assert_eq;
use proptest::proptest;

use crate::generate::Arena;
use crate::generate::NodeId;
use crate::generate::Payload;
use crate::generate::Shape;
use crate::generate::Slot;
use crate::generate::Tree;
use crate::generate::cut_case;
use crate::generate::history;
use crate::generate::profile;
use crate::generate::profile_of;
use crate::generate::tree;
use crate::reference::Ledger;
use crate::reference::RecordIndex;
use crate::reference::records;
use crate::reference::reference_cuts;
use crate::reference::splice;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Decoding a generated value's flat bytes returns the generated value.
    #[test]
    fn every_generated_value_round_trips_flat(value in tree()) {
        let flat = encode_flat(&value).expect("a generated value encodes flat");
        let back: Tree = decode_flat(flat.as_body()).expect("its flat form decodes");

        prop_assert_eq!(back, value);
    }

    /// Under every generated profile, the root pointer derefs to the
    /// generated value, and the manifest carries the profile.
    #[test]
    fn every_generated_value_commits_and_derefs_back_equal(
        value in tree(),
        profile in profile(),
    ) {
        let mut store = InMemoryChunkStore::new();
        let manifest = cam_commit(&mut store, &profile, &value)
            .expect("a generated value commits");
        let back: Tree = cam_deref(&store, manifest.root()).expect("its root derefs");

        prop_assert_eq!(manifest.profile(), &profile);
        prop_assert_eq!(back, value);
    }

    /// The flat bytes of the dereffed value are the original's, byte for byte;
    /// splicing every chunk back where its child record stands rebuilds the
    /// same bytes; and the manifest counts the flat form's records.
    #[test]
    fn chunking_is_invisible_to_the_flat_form(value in tree(), profile in profile()) {
        let flat = encode_flat(&value).expect("a generated value encodes flat");
        let mut store = InMemoryChunkStore::new();
        let manifest = cam_commit(&mut store, &profile, &value)
            .expect("a generated value commits");
        let back: Tree = cam_deref(&store, manifest.root()).expect("its root derefs");
        let again = encode_flat(&back).expect("the dereffed value encodes flat");
        let spliced = splice(&store, manifest.root());

        prop_assert_eq!(again.as_body(), flat.as_body());
        prop_assert_eq!(spliced.flat.as_slice(), flat.as_ref());
        prop_assert_eq!(
            u64::from(manifest.token_count()),
            u64::try_from(records(flat.as_body()).len()).expect("a record count")
        );
    }

    /// Committing into a store already holding generated values, some sharing
    /// the value's subtrees and some under other profiles, returns the
    /// manifest the empty store returns, and the store ends holding exactly
    /// what it held and what the empty store came to hold.
    #[test]
    fn a_root_pointer_does_not_depend_on_what_the_store_holds(
        (value, profile, priors) in history(),
    ) {
        let mut alone = Ledger::default();
        let expected = cam_commit(&mut alone, &profile, &value)
            .expect("the value commits alone");

        let mut store = Ledger::default();
        for prior in &priors {
            let prior_profile = prior.profile.resolve(&profile);
            let prior_value = prior.value.resolve(&value);
            let _committed = cam_commit(&mut store, &prior_profile, &prior_value)
                .expect("a prior value commits");
        }
        let held = store.held().clone();
        let manifest = cam_commit(&mut store, &profile, &value)
            .expect("the value commits after its priors");

        prop_assert_eq!(manifest, expected);
        let union: BTreeSet<ChunkDigest> = held.union(alone.held()).copied().collect();
        prop_assert_eq!(store.held(), &union);
    }

    /// The constructors a commit cut, read off the stored chunk DAG, are the
    /// ones a reference scanner finds from the flat form alone.
    #[test]
    fn the_cuts_agree_with_a_reference_scanner((value, profile) in cut_case()) {
        let flat = encode_flat(&value).expect("a generated value encodes flat");
        let expected = reference_cuts(flat.as_body(), &profile.params());
        let mut store = InMemoryChunkStore::new();
        let root = cam_commit(&mut store, &profile, &value)
            .expect("a generated value commits")
            .root();
        let spliced = splice(&store, root);

        prop_assert_eq!(spliced.flat.as_slice(), flat.as_ref());
        prop_assert_eq!(spliced.chunk_starts, expected);
    }
}

/// A value of every shape whose subtrees are pairwise distinct: an eight-deep
/// spine over a word, a pair of byte strings one of them empty, a byte string
/// between the empty-payload constructor and a word, and a fan of four words,
/// under a fan.
///
/// # Specification
/// trivial.
fn distinct_value() -> Tree
{
    let mut arena = Arena::default();

    let mut spine = arena.push(Shape::Word, vec![Slot::Word(CanonicalWord::from(1_u64))]);
    for level in 0x10_u64 .. 0x18_u64 {
        spine = arena.push(Shape::Tagged, vec![
            Slot::Word(CanonicalWord::from(level)),
            Slot::Child(spine),
        ]);
    }

    let named = arena.push(Shape::Bytes, vec![Slot::Bytes(Payload(b"alpha".to_vec()))]);
    let empty = arena.push(Shape::Bytes, vec![Slot::Bytes(Payload(Vec::new()))]);
    let pair = arena.push(Shape::Pair, vec![Slot::Child(named), Slot::Child(empty)]);

    let unit = arena.push(Shape::Unit, Vec::new());
    let tail = arena.push(Shape::Word, vec![Slot::Word(CanonicalWord::from(2_u64))]);
    let labelled = arena.push(Shape::Labelled, vec![
        Slot::Child(unit),
        Slot::Bytes(Payload(b"label".to_vec())),
        Slot::Child(tail),
    ]);

    let words: Vec<NodeId> = (3_u64 ..= 6_u64)
        .map(|word| arena.push(Shape::Word, vec![Slot::Word(CanonicalWord::from(word))]))
        .collect();
    let fan = arena.list(&words);

    let root = arena.list(&[spine, pair, labelled, fan]);
    arena.tree(root)
}

/// At kappa one every residue is a multiple of kappa, so whatever the cap
/// every constructor below the root is its own chunk, and a leaf edit affects
/// exactly the chunks of the constructors on its root path and shares every
/// other.
#[test]
fn an_edit_under_every_cut_affects_exactly_its_path()
{
    let value = distinct_value();
    let opens = value.opens();
    let constructors = opens.len();
    let distinct: BTreeSet<FlatBytes> = opens
        .iter()
        .map(|&open| encode_flat(&value.subtree(open)).expect("a subtree encodes flat"))
        .collect();
    assert_eq!(
        distinct.len(),
        constructors,
        "no subtree of the witness repeats, so no two constructors share a chunk"
    );
    let below_root: Vec<RecordIndex> = opens
        .iter()
        .skip(1_usize)
        .map(|open| RecordIndex(open.0))
        .collect();
    let leaves = value.leaves();
    assert!(
        leaves.len() > 1_usize,
        "the witness edits more than one leaf"
    );

    let kappa = Kappa::try_from(1_u64).expect("kappa is nonzero");
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));
    for cap in [1_u64, 2_u64, 3_u64, 64_u64, u64::MAX] {
        let profile = profile_of(
            kappa,
            TokenCap::try_from(cap).expect("the cap is nonzero"),
            codec,
        );
        let mut store = InMemoryChunkStore::new();
        let before = cam_commit(&mut store, &profile, &value)
            .expect("the witness commits")
            .root();
        assert_eq!(
            usize::from(store.chunk_count()),
            constructors,
            "cap {cap}: one chunk per constructor"
        );
        assert_eq!(
            splice(&store, before).chunk_starts,
            below_root,
            "cap {cap}: every constructor below the root begins a chunk"
        );

        for &leaf in &leaves {
            let mut edited = value.clone();
            edited.edit(leaf);
            let mut grown = store.clone();
            let after = cam_commit(&mut grown, &profile, &edited)
                .expect("the edit commits")
                .root();
            let measured =
                measure_edit(&grown, before, after, leaf.depth).expect("the edit measures");

            let path = usize::try_from(u64::from(leaf.depth))
                .expect("a witness depth")
                .checked_add(1_usize)
                .expect("a witness path");
            let others = constructors
                .checked_sub(path)
                .expect("a path within the value");
            assert_eq!(
                usize::from(measured.chunks_affected),
                path,
                "cap {cap}, {leaf:?}: the edit affects the chunks on its path"
            );
            assert_eq!(
                usize::from(measured.chunks_shared),
                others,
                "cap {cap}, {leaf:?}: the edit shares every other chunk"
            );
            assert_eq!(
                usize::from(grown.chunk_count()).checked_sub(constructors),
                Some(path),
                "cap {cap}, {leaf:?}: the store grows by the path alone"
            );
        }
    }
}

/// A value committed, mutated in place through an exclusive borrow, then
/// committed again: the two roots differ, the first still derefs to the value
/// as committed and the second to the mutated value, and the store grew by
/// exactly the chunks the edit affected.
#[test]
fn a_value_mutated_after_commit_commits_anew_and_the_old_pointer_still_reads_the_old_value()
{
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));
    for (kappa, cap) in [(1_u64, 1_u64), (4_u64, 64_u64), (u64::MAX, u64::MAX)] {
        let profile = profile_of(
            Kappa::try_from(kappa).expect("kappa is nonzero"),
            TokenCap::try_from(cap).expect("the cap is nonzero"),
            codec,
        );
        let mut value = distinct_value();
        let committed = value.clone();
        let mut store = InMemoryChunkStore::new();
        let first = cam_commit(&mut store, &profile, &value)
            .expect("the value commits")
            .root();
        let held = usize::from(store.chunk_count());

        let deepest = value
            .leaves()
            .into_iter()
            .max_by_key(|leaf| leaf.depth)
            .expect("the witness has a leaf");
        value.edit(deepest);
        assert_ne!(value, committed, "the value changed in place");

        let second = cam_commit(&mut store, &profile, &value)
            .expect("the mutated value commits")
            .root();
        assert_ne!(
            first, second,
            "kappa {kappa}, cap {cap}: the mutated value commits anew"
        );
        assert_eq!(
            cam_deref::<Tree>(&store, first),
            Ok(committed),
            "kappa {kappa}, cap {cap}: the old pointer reads the value as committed"
        );
        assert_eq!(
            cam_deref::<Tree>(&store, second),
            Ok(value),
            "kappa {kappa}, cap {cap}: the new pointer reads the mutated value"
        );

        let measured =
            measure_edit(&store, first, second, deepest.depth).expect("the edit measures");
        assert_eq!(
            usize::from(store.chunk_count()).checked_sub(held),
            Some(usize::from(measured.chunks_affected)),
            "kappa {kappa}, cap {cap}: the store grew by exactly the chunks the edit affected"
        );
    }
}
