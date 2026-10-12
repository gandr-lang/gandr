//! Borrowed structural fields of a certificate step, independent of storage.
//!
//! The v1 field order is lhs, rhs, orientation, provenance, metadata and
//! position. Names retain their spelling; no alpha quotient is taken. The
//! storage tier owns integer widths, byte framing, hashing and durable IDs.
//!
//! # Certificate fields
//!
//! `transport::step_fields` borrows a sequent cell and its application
//! position. It yields structural fields in v1 order: left face, right face,
//! orientation, provenance, metadata, then position. Faces use pre-order tags,
//! names and arities. Names retain their spelling; metadata follows first
//! occurrence. The immutable contractum-use classification is recoverable from
//! the encoded faces and carries no redundant field.
//!
//! The iterator walks flat producer and consumer tables without allocation or
//! recursive calls. Storage owns checked widths, byte framing and BLAKE3
//! identities through `gandr_storage_artifact::transport`. This
//! direction keeps theory independent of storage. A buffered byte image would
//! allocate per hash; a sink trait would add an abstraction with one
//! implementation. Reconsider the field boundary when a second alphabet
//! supplies its canonical encoding.
//!
//! A consumer is encoded node by node in pre-order. An operation frame with
//! one continuation keeps the v1 tag, so every single-output certificate is
//! unchanged; a frame with another continuation count takes its own tag and
//! states the count, which is what a decoder needs to know where each
//! continuation's fields end.

use anodized::spec;
use gandr_theory_cell_complexes::Cat;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellVariance;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsHead;
use gandr_theory_cell_complexes::ContinuationCount;
use gandr_theory_cell_complexes::EtaKind;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::Pos;
use gandr_theory_cell_complexes::ProdHead;
use gandr_theory_cell_complexes::ProdPat;

/// A structural field awaiting the storage tier's canonical framing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificateField<'cell>
{
    /// A variant tag or flag, encoded as a big-endian u64.
    Tag(u64),
    /// A count or position index, checked into a big-endian u64.
    Count(usize),
    /// A name's UTF-8 bytes, prefixed by its checked u64 byte length.
    Bytes(&'cell [u8]),
}

/// Borrow a step's complete structural field stream without allocating.
///
/// Metadata is derived and immutable. Contractum use is determined by the
/// encoded faces, so it needs no redundant field in the v1 image.
///
/// # Specification
/// - ensures: fields occur in v1 order: both faces in pre-order, orientation,
///   provenance, metadata in first-occurrence order, then position length and
///   indices. Equal cell content and positions yield equal fields regardless of
///   allocation or store insertion order.
/// - panics: none.
/// - executable: none — instrumentation cannot return an opaque iterator from
///   its wrapper closure.
///
/// # Adequacy
/// - hypothesis: L2 — a literal field sequence for a frame-defining cell fixes
///   ordering, names and metadata. L3 — nested constructors, operations and a
///   terminal separate omitted arguments and reversed traversal.
/// - witness: `transport::tests::frame_fields_match_the_v1_sequence`
/// - witness: `transport::tests::nested_fields_keep_preorder_and_position`
#[inline]
pub fn step_fields<'cell>(
    cell: &'cell Cell,
    at: &'cell Pos,
) -> impl Iterator<Item = CertificateField<'cell>>
{
    let orient = match cell.orient() {
        | Orientation::PolarityDerived => 0,
        | Orientation::CompletionDerived => 1,
    };
    let provenance = match cell.provenance() {
        | CellProvenance::SurfaceRule => 0,
        | CellProvenance::MuMuTilde => 1,
        | CellProvenance::FrameDefining => 2,
        | CellProvenance::Eta(EtaKind::Data) => 3,
        | CellProvenance::Eta(EtaKind::Codata) => 4,
        | CellProvenance::DerivedByCompletion => 5,
    };
    command_fields(cell.lhs())
        .chain(command_fields(cell.rhs()))
        .chain([
            CertificateField::Tag(orient),
            CertificateField::Tag(provenance),
            CertificateField::Count(cell.meta().vars().len()),
        ])
        .chain(cell.meta().vars().iter().flat_map(|var| {
            let variance = match var.variance() {
                | CellVariance::Producer => 0,
                | CellVariance::Consumer => 1,
                | CellVariance::Mixed => 2,
            };
            let [name, category] = variable_fields(var.var());
            [
                name,
                category,
                CertificateField::Tag(variance),
                CertificateField::Tag(u64::from(bool::from(var.linear()))),
            ]
        }))
        .chain([
            CertificateField::Tag(u64::from(bool::from(cell.meta().invertible()))),
            CertificateField::Count(at.steps().len()),
        ])
        .chain(
            at.steps()
                .iter()
                .map(|step| CertificateField::Count(usize::from(*step))),
        )
}

/// Project a metavariable's spelling and category.
///
/// # Specification
/// - ensures: the name precedes category zero for producers, one for consumers.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the frame sequence distinguishes both categories and
///   their names; swapping them changes the literal sequence.
/// - witness: `transport::tests::frame_fields_match_the_v1_sequence`
#[spec(ensures: |output| output == [CertificateField::Bytes(var.hole().as_ref().as_bytes()),
    CertificateField::Tag(match var.cat() { Cat::Producer => 0, Cat::Consumer => 1 })])]
fn variable_fields(var: &MetaVar) -> [CertificateField<'_>; 2]
{
    [
        CertificateField::Bytes(var.hole().as_ref().as_bytes()),
        CertificateField::Tag(match var.cat() {
            | Cat::Producer => 0,
            | Cat::Consumer => 1,
        }),
    ]
}

/// Project producer nodes in their flat table's pre-order.
///
/// # Specification
/// - ensures: each node contributes its tag, name and category or arity.
/// - panics: none.
/// - executable: none — the return is an opaque iterator.
///
/// # Adequacy
/// - hypothesis: L2 — nested fields distinguish node order and arities.
/// - witness: `transport::tests::nested_fields_keep_preorder_and_position`
fn producer_fields(prod: &ProdPat) -> impl Iterator<Item = CertificateField<'_>>
{
    prod.to_ref()
        .preorder()
        .flat_map(|entry| match *entry.head() {
            | ProdHead::Meta(ref var) => {
                let [name, category] = variable_fields(var);
                [CertificateField::Tag(0), name, category]
            },
            | ProdHead::Ctor(ref name, count) => [
                CertificateField::Tag(1),
                CertificateField::Bytes(name.as_ref().as_bytes()),
                CertificateField::Count(usize::from(count)),
            ],
        })
}

/// Project one consumer node and its producer arguments.
///
/// # Specification
/// - ensures: the node's tag precedes its name and counts, then its producer
///   arguments: an operation frame with one continuation is tag 1, its name and
///   argument count; with another count, tag 4, its name, argument count and
///   continuation count; a constructor frame is tag 2 and its name; a hole tag
///   0, its name and category; the terminal tag 3.
/// - panics: none.
/// - executable: none — the return is an opaque iterator.
///
/// # Adequacy
/// - hypothesis: L2 — frame, nested-operation and two-continuation sequences
///   distinguish tags, argument omission, continuation counts and order.
/// - witness: `transport::tests::frame_fields_match_the_v1_sequence`
/// - witness: `transport::tests::nested_fields_keep_preorder_and_position`
/// - witness: `transport::tests::a_many_continuation_frame_states_its_count_and_ports_in_order`
fn consumer_fields(head: &ConsHead) -> impl Iterator<Item = CertificateField<'_>>
{
    let prefix = match *head {
        | ConsHead::Op {
            ref op,
            ref args,
            rets,
        } => [
            Some(CertificateField::Tag(if rets == ContinuationCount::ONE {
                1
            }
            else {
                4
            })),
            Some(CertificateField::Bytes(op.as_ref().as_bytes())),
            Some(CertificateField::Count(args.len())),
            (rets != ContinuationCount::ONE).then_some(CertificateField::Count(usize::from(rets))),
        ],
        | ConsHead::Frame(ref name) => [
            Some(CertificateField::Tag(2)),
            Some(CertificateField::Bytes(name.as_ref().as_bytes())),
            None,
            None,
        ],
        | ConsHead::Meta(ref var) => {
            let [name, category] = variable_fields(var);
            [
                Some(CertificateField::Tag(0)),
                Some(name),
                Some(category),
                None,
            ]
        },
        | ConsHead::Top => [Some(CertificateField::Tag(3)), None, None, None],
    };
    prefix
        .into_iter()
        .flatten()
        .chain(head.args().iter().flat_map(producer_fields))
}

/// Project one cut, traversing each producer table and the consumer table
/// once.
///
/// # Specification
/// - ensures: cut tag and polarity precede producer and consumer fields;
///   consumer nodes run in pre-order, each frame before its continuations,
///   which run in port order and end in a hole or terminal tag.
/// - panics: none.
/// - executable: none — the return is an opaque iterator.
///
/// # Adequacy
/// - hypothesis: L2 — literal sequences separate cut polarity, traversal order,
///   the two consumer endings and continuation order.
/// - witness: `transport::tests::frame_fields_match_the_v1_sequence`
/// - witness: `transport::tests::nested_fields_keep_preorder_and_position`
/// - witness: `transport::tests::a_many_continuation_frame_states_its_count_and_ports_in_order`
fn command_fields(cmd: &CmdPat) -> impl Iterator<Item = CertificateField<'_>>
{
    [
        CertificateField::Tag(0),
        CertificateField::Tag(match cmd.polarity() {
            | Polarity::Positive => 0,
            | Polarity::Negative => 1,
        }),
    ]
    .into_iter()
    .chain(producer_fields(cmd.producer()))
    .chain(cmd.consumer().to_ref().preorder().flat_map(consumer_fields))
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;

    use super::CertificateField::Bytes as B;
    use super::CertificateField::Count as C;
    use super::CertificateField::Tag as T;
    use super::*;

    #[test]
    fn frame_fields_match_the_v1_sequence()
    {
        let cell = frame_defining_cell(&Sym::new("Succ"));
        let at = Pos::root();
        let fields: Vec<_> = step_fields(&cell, &at).collect();
        assert_eq!(fields, [
            T(0),
            T(0),
            T(0),
            B(b"v"),
            T(0),
            T(2),
            B(b"Succ"),
            T(0),
            B(b"beta"),
            T(1),
            T(0),
            T(0),
            T(1),
            B(b"Succ"),
            C(1),
            T(0),
            B(b"v"),
            T(0),
            T(0),
            B(b"beta"),
            T(1),
            T(0),
            T(2),
            C(2),
            B(b"v"),
            T(0),
            T(0),
            T(1),
            B(b"beta"),
            T(1),
            T(1),
            T(1),
            T(0),
            C(0)
        ]);
    }

    #[test]
    fn nested_fields_keep_preorder_and_position()
    {
        let cmd = CmdPat::cut(
            Polarity::Negative,
            ProdPat::ctor("Pair", [ProdPat::ctor("Z", []), ProdPat::meta("x")]),
            ConsPat::op(
                "f",
                [ProdPat::meta("y")],
                ConsPat::frame("S", ConsPat::top()),
            ),
        );
        let fields: Vec<_> = command_fields(&cmd).collect();
        assert_eq!(fields, [
            T(0),
            T(1),
            T(1),
            B(b"Pair"),
            C(2),
            T(1),
            B(b"Z"),
            C(0),
            T(0),
            B(b"x"),
            T(0),
            T(1),
            B(b"f"),
            C(1),
            T(0),
            B(b"y"),
            T(0),
            T(2),
            B(b"S"),
            T(3)
        ]);
        let cell = Cell::new(
            cmd.clone(),
            cmd,
            Orientation::CompletionDerived,
            CellProvenance::DerivedByCompletion,
        );
        let at = Pos::root().child(0_usize.into()).child(2_usize.into());
        let fields: Vec<_> = step_fields(&cell, &at).collect();
        assert_eq!(&fields[fields.len() - 3 ..], &[C(2), C(0), C(2)]);
    }

    #[test]
    fn a_many_continuation_frame_states_its_count_and_ports_in_order()
    {
        let cmd = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::operation("divmod", [ProdPat::meta("n")], [
                ConsPat::meta("q"),
                ConsPat::frame("S", ConsPat::meta("r")),
            ]),
        );
        let fields: Vec<_> = command_fields(&cmd).collect();
        assert_eq!(fields, [
            T(0),
            T(0),
            T(0),
            B(b"m"),
            T(0),
            T(4),
            B(b"divmod"),
            C(1),
            C(2),
            T(0),
            B(b"n"),
            T(0),
            T(0),
            B(b"q"),
            T(1),
            T(2),
            B(b"S"),
            T(0),
            B(b"r"),
            T(1)
        ]);
    }
}
