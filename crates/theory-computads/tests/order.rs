//! The reduction order measured against cells a description produces.
//!
//! A size-only order leaves equal-size critical pairs as obstructions; the
//! path order orients more. These suites measure that over the cells the
//! description route elaborates from written rules, rather than over probes
//! shaped to give an answer.
//!
//! - `the_path_order_orients_pairs_the_size_order_left_as_obstructions` counts
//!   the equal-size face pairs a real corpus contains and how many of them the
//!   order orients.
//! - `completion_derives_the_fusion_cell_the_size_order_could_not_orient`
//!   carries the measurement to the engine: the worked deforestation cell is an
//!   equal-size divergence, and completion emits it with a replayable
//!   certificate.

use core::cmp::Ordering;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::ConsView;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::reduction_cmp;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionOutcome;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_computads::elaborate_data_desc;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::SortRef;
use quenchant_shape::shape::Maybe;

use crate::fixture::Ungraded;
use crate::fixture::face;

#[test]
fn the_path_order_orients_pairs_the_size_order_left_as_obstructions()
{
    // Every face of every cell a real description elaborates, paired with
    // every other: the pairs whose sizes agree are exactly the ones a
    // size-only order reports `Equal`, and the count says how many of those
    // the path order decides.
    let faces = store_faces(&description_route_store());
    assert!(
        faces.len() >= 8,
        "the corpus carries several real rule faces, not one probe"
    );
    let mut equal_size = 0_usize;
    let mut oriented = 0_usize;
    for left in &faces {
        for right in &faces {
            if left.size() != right.size() || left == right {
                continue;
            }
            equal_size = equal_size.saturating_add(1);
            if reduction_cmp(left, right) != Ordering::Equal {
                oriented = oriented.saturating_add(1);
            }
        }
    }
    assert!(
        equal_size > 0,
        "a real corpus contains equal-size pairs, which is why the measurement exists"
    );
    assert_eq!(
        14_usize, oriented,
        "measured and pinned: of {equal_size} equal-size ordered face pairs a size-only order \
         leaves as obstructions, the path order orients this many"
    );
    for left in &faces {
        for right in &faces {
            assert_eq!(
                reduction_cmp(left, right),
                reduction_cmp(right, left).reverse(),
                "an orientation is antisymmetric, and an obstruction is one from either side"
            );
        }
    }
}

#[test]
fn completion_derives_the_fusion_cell_the_size_order_could_not_orient()
{
    // `⟨v | Succ⁻(add(n; α))⟩` and `⟨v | add(n; Succ⁻(α))⟩` are the two faces
    // of the worked deforestation cell, of one size: fusing moves a frame
    // rather than removing one. A store whose two cells reduce one command to
    // those two faces is an equal-size divergence.
    let mut store = CellStore::new();
    store.insert(diverging_cell(fusion_before()));
    store.insert(diverging_cell(fusion_after()));
    let outcome = complete(
        store,
        CompletionBudget::new(
            CompletionStepBudget::from(64_usize),
            CompletionCellBudget::from(16_usize),
            NormalizationBudget::from(64_usize),
        ),
    );
    let CompletionOutcome::Completed {
        ref store,
        ref derived,
        ref certificates,
    } = outcome
    else {
        panic!("the two-cell system completes within budget: {outcome:?}");
    };
    let Some(&first) = derived.first()
    else {
        panic!("completion derives a cell from the equal-size divergence");
    };
    let Maybe::Present(derived_cell) = store.get(first)
    else {
        panic!("the derived cell is in the returned store");
    };
    // Overlap enumeration renames the right cell's holes apart, so what is
    // asserted is the shape and the direction rather than the hole names.
    assert_eq!(
        (
            FaceShape::FrameOutsideOperation,
            FaceShape::OperationOutsideFrame
        ),
        (shape(derived_cell.lhs()), shape(derived_cell.rhs())),
        "the derived cell rewrites the unfused face to the fused one: deforestation, in the \
         direction the design writes it"
    );
    assert_eq!(
        Ordering::Greater,
        reduction_cmp(derived_cell.lhs(), derived_cell.rhs()),
        "and the orientation is the order's"
    );
    for certificate in certificates {
        assert!(
            bool::from(certificate.replay(store)),
            "every certificate completion emits replays"
        );
    }
}

/// The consumer shape of a fusion face.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FaceShape
{
    /// A constructor frame directly wrapping an operation frame: unfused.
    FrameOutsideOperation,
    /// An operation frame whose continuation is a constructor frame: fused.
    OperationOutsideFrame,
    /// Neither.
    Other,
}

/// The consumer shape of `cmd`.
///
/// # Specification
/// trivial.
fn shape(cmd: &CmdPat) -> FaceShape
{
    match cmd.consumer().view() {
        | ConsView::Frame { ret, .. } if matches!(ret.view(), ConsView::Op { .. }) => {
            FaceShape::FrameOutsideOperation
        },
        | ConsView::Op { ret, .. } if matches!(ret.view(), ConsView::Frame { .. }) => {
            FaceShape::OperationOutsideFrame
        },
        | ConsView::Frame { .. } | ConsView::Op { .. } | ConsView::Meta(_) | ConsView::Top => {
            FaceShape::Other
        },
    }
}

/// The worked fusion cell's left face, `⟨v | Succ⁻(add(n; a))⟩`.
///
/// # Specification
/// trivial.
fn fusion_before() -> CmdPat
{
    CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("v"),
        ConsPat::frame(
            "Succ",
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("a")),
        ),
    )
}

/// The worked fusion cell's right face, `⟨v | add(n; Succ⁻(a))⟩`.
///
/// # Specification
/// trivial.
fn fusion_after() -> CmdPat
{
    CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("v"),
        ConsPat::op(
            "add",
            [ProdPat::meta("n")],
            ConsPat::frame("Succ", ConsPat::meta("a")),
        ),
    )
}

/// A cell reducing one shared redex to `face`, so two of them present
/// completion with a divergent critical pair at the root.
///
/// # Specification
/// trivial.
fn diverging_cell(face: CmdPat) -> Cell
{
    Cell::new(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("v"),
            ConsPat::op("seed", [ProdPat::meta("n")], ConsPat::meta("a")),
        ),
        face,
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    )
}

/// Both faces of every cell in a store, in insertion order.
///
/// # Specification
/// trivial.
fn store_faces(store: &CellStore) -> Vec<CmdPat>
{
    store
        .iter()
        .flat_map(|(_, cell)| [cell.lhs().clone(), cell.rhs().clone()])
        .collect()
}

/// The store a real `Nat` description elaborates: two constructors, `add`
/// and `double`, and their four written faces.
///
/// # Specification
/// - panics: when the description does not elaborate whole, which is a fixture
///   defect.
fn description_route_store() -> CellStore
{
    let operation = |name: &str, inputs: &[&str]| {
        OperDesc::new(
            name,
            BridgeArity::single_output(
                inputs
                    .iter()
                    .map(|&input| SortRef::new(input, "Nat"))
                    .collect::<Vec<_>>(),
                SortRef::new("out", "Nat"),
            ),
            Attrs::empty(),
        )
    };
    let desc: SignDesc<Ungraded> = SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Nat"),
        Vec::new(),
        [
            CtorDesc::new("Zero", Code::unit(), "Nat", Attrs::empty()),
            CtorDesc::new("Succ", Code::var("Nat"), "Nat", Attrs::empty()),
        ],
        [operation("add", &["m", "n"]), operation("double", &["m"])],
        [
            face(
                FreeTerm::op("add", [FreeTerm::ctor("Zero", []), FreeTerm::var("n")]),
                FreeTerm::var("n"),
            ),
            face(
                FreeTerm::op("add", [
                    FreeTerm::ctor("Succ", [FreeTerm::var("m")]),
                    FreeTerm::var("n"),
                ]),
                FreeTerm::ctor("Succ", [FreeTerm::op("add", [
                    FreeTerm::var("m"),
                    FreeTerm::var("n"),
                ])]),
            ),
            face(
                FreeTerm::op("double", [FreeTerm::ctor("Zero", [])]),
                FreeTerm::ctor("Zero", []),
            ),
            face(
                FreeTerm::op("double", [FreeTerm::ctor("Succ", [FreeTerm::var("m")])]),
                FreeTerm::ctor("Succ", [FreeTerm::ctor("Succ", [FreeTerm::op(
                    "double",
                    [FreeTerm::var("m")],
                )])]),
            ),
        ],
        DeclPolarity::Data,
        Attrs::empty(),
    );
    let elaborated = elaborate_data_desc(&desc);
    assert!(
        elaborated.declined_faces.is_empty() && elaborated.declined_opers.is_empty(),
        "the corpus description elaborates whole, so the measurement runs over real rules"
    );
    elaborated.store
}
