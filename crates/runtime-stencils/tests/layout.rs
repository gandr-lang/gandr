//! The heap object header: each field's width is where its refusal starts,
//! and a header built from the widest values reads every field back.

use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::FieldOverflow;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Tag;

/// The largest family position the field holds: stored plus one, it is
/// 2³² − 1.
const LAST_FAMILY: usize = 0xFFFF_FFFE;

/// Each field accepts its widest value and refuses the next: a tag below
/// 2¹², an arity below 2¹⁶, a family position whose successor fits 32 bits.
#[test]
fn the_header_fields_refuse_values_past_their_width()
{
    assert!(Tag::try_from(0xFFF_usize).is_ok(), "2¹² − 1 is a tag");
    assert_eq!(
        Err(FieldOverflow::Tag),
        Tag::try_from(0x1000_usize),
        "2¹² is not"
    );
    assert!(Arity::try_from(0xFFFF_usize).is_ok(), "2¹⁶ − 1 is an arity");
    assert_eq!(
        Err(FieldOverflow::Arity),
        Arity::try_from(0x1_0000_usize),
        "2¹⁶ is not"
    );
    let first = Family::try_from(0_usize).expect("position 0");
    assert_eq!(Ok(0), usize::try_from(first), "position 0 reads back");
    let last = Family::try_from(LAST_FAMILY).expect("the last position");
    assert_eq!(
        Ok(LAST_FAMILY),
        usize::try_from(last),
        "the last position reads back"
    );
    assert_eq!(
        Err(FieldOverflow::Family),
        Family::try_from(LAST_FAMILY.saturating_add(1)),
        "its successor does not fit"
    );
    assert!(
        usize::try_from(Family::UNNAMED).is_err(),
        "an unnamed family has no position"
    );
}

/// Every kind with the widest tag, arity and family reads each field back,
/// so no field overlaps its neighbour; the matched bits drop the family
/// alone.
#[test]
fn a_header_reads_back_every_field()
{
    let tag = Tag::try_from(0xFFF_usize).expect("the widest tag");
    let arity = Arity::try_from(0xFFFF_usize).expect("the widest arity");
    let family = Family::try_from(LAST_FAMILY).expect("the last family");
    for kind in [
        Kind::Integer,
        Kind::Tuple,
        Kind::Injection,
        Kind::Data,
        Kind::Closure,
        Kind::Code,
    ] {
        let header = Header::new(kind, tag, arity, family);
        assert_eq!(Ok(kind), header.kind(), "{kind:?}: the kind");
        assert_eq!(tag, header.tag(), "{kind:?}: the tag");
        assert_eq!(arity, header.arity(), "{kind:?}: the arity");
        assert_eq!(family, header.family(), "{kind:?}: the family");
        let unnamed = Header::new(kind, tag, arity, Family::UNNAMED);
        assert_eq!(
            unnamed.word(),
            header.matched(),
            "{kind:?}: the matched bits"
        );
    }
    let small = Header::new(
        Kind::Injection,
        Tag::try_from(1_usize).expect("tag 1"),
        Arity::try_from(1_usize).expect("arity 1"),
        Family::UNNAMED,
    );
    assert_eq!(
        Tag::try_from(1_usize),
        Ok(small.tag()),
        "a narrow tag beside zero fields"
    );
    assert_eq!(Family::UNNAMED, small.family(), "no family stays none");
}
