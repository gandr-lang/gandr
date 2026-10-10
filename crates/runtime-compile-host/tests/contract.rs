//! Rust-side ABI and wire conformance against independent version-one goldens.

use gandr_runtime_compile_host::boundary::ABI_VERSION;
use gandr_runtime_compile_host::boundary::AbiVersion;
use gandr_runtime_compile_host::boundary::HostError;
use gandr_runtime_compile_host::boundary::RawOutcome;
use gandr_runtime_compile_host::boundary::require_version;
use gandr_runtime_compile_host::image::CtorTag;
use gandr_runtime_compile_host::image::IMAGE_WIRE_VERSION;
use gandr_runtime_compile_host::image::Image;
use gandr_runtime_compile_host::image::MAX_IMAGE_NODES;
use gandr_runtime_compile_host::image::Node;
use gandr_runtime_compile_host::image::NodeKind;

#[test]
fn the_wire_numbering_matches_this_crates_mirror()
{
    for (kind, expected) in [
        (NodeKind::Lit, 0),
        (NodeKind::Var, 1),
        (NodeKind::Ctor, 2),
        (NodeKind::Dup, 3),
        (NodeKind::Drop, 4),
        (NodeKind::Bind, 5),
        (NodeKind::Case, 6),
        (NodeKind::Cut, 7),
    ] {
        let mut image = Image::new();
        image.push(crate::image::leaf(kind)).expect("kind");
        assert_eq!(image.encode().as_ref().get(3), Some(&expected));
    }
    for (tag, expected) in [
        (CtorTag::Unit, 0),
        (CtorTag::Pair, 1),
        (CtorTag::Inl, 2),
        (CtorTag::Inr, 3),
    ] {
        let mut image = Image::new();
        image
            .push(Node {
                tag,
                ..crate::image::leaf(NodeKind::Ctor)
            })
            .expect("tag");
        assert_eq!(image.encode().as_ref().get(4), Some(&expected));
    }
}
#[test]
fn the_constructor_arities_match_this_crates_mirror()
{
    for (tag, count) in [
        (CtorTag::Unit, 0),
        (CtorTag::Pair, 2),
        (CtorTag::Inl, 1),
        (CtorTag::Inr, 1),
    ] {
        assert_eq!(usize::from(tag.arity()), count);
    }
}
#[test]
fn the_wire_version_and_arena_bound_are_unchanged()
{
    assert_eq!(IMAGE_WIRE_VERSION, 1);
    assert_eq!(MAX_IMAGE_NODES, 4096);
    let mut image = Image::new();
    for _ in 0_usize .. 4096_usize {
        image
            .push(crate::image::leaf(NodeKind::Lit))
            .expect("version one ceiling");
    }
    assert_eq!(
        image.encode().as_ref().get(.. 3),
        Some([1_u8, 0, 16].as_slice())
    );
}
#[test]
fn the_boundary_version_and_statuses_are_unchanged()
{
    assert_eq!(u32::from(ABI_VERSION), 1);
    assert_eq!(require_version(AbiVersion::from(1_u32)), Ok(()));
    for version in [0, 2, u32::MAX] {
        let found = AbiVersion::from(version);
        assert_eq!(
            require_version(found),
            Err(HostError::VersionMismatch {
                found,
                expected: ABI_VERSION
            })
        );
    }
}
#[test]
fn the_boundary_struct_layout_is_unchanged()
{
    assert_eq!(core::mem::offset_of!(RawOutcome, status), 0);
    let wide = core::mem::align_of::<i64>();
    let first = 4_usize.next_multiple_of(wide);
    assert_eq!(core::mem::offset_of!(RawOutcome, duplications), first);
    assert_eq!(
        core::mem::offset_of!(RawOutcome, discards),
        first.saturating_add(8)
    );
    assert_eq!(
        core::mem::offset_of!(RawOutcome, allocated_words),
        first.saturating_add(16)
    );
    assert_eq!(
        core::mem::offset_of!(RawOutcome, text),
        first.saturating_add(24)
    );
    let record = RawOutcome::default();
    assert_eq!(core::mem::size_of_val(&record.status), 4);
    assert_eq!(core::mem::size_of_val(&record.duplications), 8);
    assert_eq!(core::mem::size_of_val(&record.discards), 8);
    assert_eq!(core::mem::size_of_val(&record.allocated_words), 8);
}
