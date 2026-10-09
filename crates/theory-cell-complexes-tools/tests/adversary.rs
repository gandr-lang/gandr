//! Each adversary lies about exactly one thing.
//!
//! These witnesses hold the fixture itself rather than any engine above it: an
//! adversary that drifted into lying about a second law would silently change
//! what every adversarial test over it measures, and nothing else in the tree
//! would notice.

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::AlphabetLie;
use gandr_theory_cell_complexes_tools::CollidingAddresses;
use gandr_theory_cell_complexes_tools::IncomparablePositions;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::NonLocalSplice;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToyOrient;
use gandr_theory_cell_complexes_tools::ToyPos;
use gandr_theory_cell_complexes_tools::WithheldConvexity;
use gandr_theory_cell_complexes_tools::lying_cell;
use gandr_theory_cell_complexes_tools::reoriented_lying_cell;
use gandr_theory_cell_complexes_tools::toy_cell;

/// The toy position of `path`.
///
/// # Specification
/// trivial.
fn at(path: &[PositionStep]) -> ToyPos
{
    ToyAlphabet::position_at_path(path)
}

/// Every byte a value's [`core::hash::Hash`] writes, kept in order, so two
/// values' hash inputs compare exactly rather than through a digest.
#[repr(transparent)]
#[derive(Debug, Default, Eq, PartialEq)]
struct Written(Vec<u8>);

impl core::hash::Hasher for Written
{
    /// No digest: the bytes themselves are the observation.
    ///
    /// # Specification
    /// trivial.
    fn finish(&self) -> u64
    {
        0
    }

    /// Appends the bytes.
    ///
    /// # Specification
    /// trivial.
    fn write(
        &mut self,
        bytes: &[u8],
    )
    {
        self.0.extend_from_slice(bytes);
    }
}

/// The bytes `value` writes when hashed.
///
/// # Specification
/// trivial.
fn written<T>(value: &T) -> Written
where
    T: core::hash::Hash,
{
    let mut state = Written::default();
    value.hash(&mut state);
    state
}

/// The delegating wrapper differs from the honest alphabet on the one law it
/// is built to break, and on nothing else asked here.
#[test]
fn the_incomparable_wrapper_breaks_the_position_order_and_keeps_the_match()
{
    let outer = at(&[]);
    let inner = at(&[PositionStep::from(0_usize)]);
    assert_eq!(
        PositionOrder::Encloses,
        ToyAlphabet::position_order(&outer, &inner),
        "the honest alphabet orders a nesting pair"
    );
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&outer, &inner),
        "the wrapper calls the same pair incomparable, which is its whole lie"
    );
    let pattern = Toy::add(Toy::var("x"), Toy::zero());
    let ground = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let mut lying = <Lying<IncomparablePositions> as CellAlphabet>::Subst::default();
    assert!(bool::from(
        <Lying<IncomparablePositions> as CellAlphabet>::match_cmd(&pattern, &ground, &mut lying)
    ));
    assert_eq!(
        ground,
        <Lying<IncomparablePositions> as CellAlphabet>::apply_subst(&lying, &pattern)
    );
}

/// The non-local splice resets a binary root's other child and nothing else:
/// a unary root has no sibling to disturb, and reading is the honest read.
#[test]
fn the_non_local_splice_wrapper_breaks_the_splice_and_keeps_the_read()
{
    let left = at(&[PositionStep::from(0_usize)]);
    let binary = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    assert_eq!(
        Ok(Toy::add(Toy::zero(), Toy::succ(Toy::zero()))),
        ToyAlphabet::splice_cmd_at(&binary, &left, Toy::zero()),
        "the honest splice touches only the position it was given"
    );
    assert_eq!(
        Ok(Toy::add(Toy::zero(), Toy::add(Toy::zero(), Toy::zero()))),
        <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(&binary, &left, Toy::zero()),
        "the wrapper also resets the sibling, which is its whole lie"
    );
    let unary = Toy::succ(Toy::succ(Toy::zero()));
    assert_eq!(
        Ok(Toy::succ(Toy::zero())),
        <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(&unary, &left, Toy::zero()),
        "a unary root has no sibling, so the two splices agree there"
    );
    assert_eq!(
        quenchant_shape::shape::Maybe::Present(Toy::succ(Toy::zero())),
        <Lying<NonLocalSplice> as CellAlphabet>::subterm_cmd_at(&binary, &left),
        "and the read at the spliced position is the honest one"
    );
}

/// The withheld warrant is the wrapper's one answer apart from the toy's: the
/// toy store carries the warrant, and matching through the wrapper is honest.
#[test]
fn the_withheld_convexity_wrapper_withholds_the_warrant_and_keeps_the_match()
{
    let mut honest_store = CellStore::<ToyAlphabet>::new();
    honest_store.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
    let mut lying_store = CellStore::<Lying<WithheldConvexity>>::new();
    lying_store.insert(lying_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        ToyAlphabet::convexity_discharge(&honest_store),
        "the honest alphabet carries the warrant"
    );
    assert_eq!(
        ConvexityDischarge::ReCheckRequired,
        <Lying<WithheldConvexity> as CellAlphabet>::convexity_discharge(&lying_store),
        "the wrapper withholds it, which is its whole lie"
    );
    let pattern = Toy::add(Toy::var("x"), Toy::zero());
    let ground = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let mut lying = <Lying<WithheldConvexity> as CellAlphabet>::Subst::default();
    assert!(bool::from(
        <Lying<WithheldConvexity> as CellAlphabet>::match_cmd(&pattern, &ground, &mut lying)
    ));
    assert_eq!(
        ground,
        <Lying<WithheldConvexity> as CellAlphabet>::apply_subst(&lying, &pattern)
    );
}

/// Two cells differing only in orientation hash alike through the wrapper and
/// stay two cells: the store keeps both, and each keeps its own tag.
#[test]
fn the_colliding_addresses_wrapper_hides_the_orientation_and_keeps_the_cell()
{
    let lhs = Toy::succ(Toy::var("x"));
    let rhs = Toy::var("x");
    let given = lying_cell::<CollidingAddresses>(lhs.clone(), rhs.clone());
    let derived = reoriented_lying_cell::<CollidingAddresses>(lhs.clone(), rhs.clone());
    assert_ne!(given, derived, "the two cells differ in orientation");
    assert_eq!(
        written(&given),
        written(&derived),
        "and hash alike through the wrapper, which is its whole lie"
    );
    let honest_given = lying_cell::<WithheldConvexity>(lhs.clone(), rhs.clone());
    let honest_derived = reoriented_lying_cell::<WithheldConvexity>(lhs.clone(), rhs.clone());
    assert_ne!(
        written(&honest_given),
        written(&honest_derived),
        "a wrapper that does not lie about the tag hashes the two apart"
    );
    assert_eq!(
        written(&toy_cell(lhs, rhs)),
        written(&honest_given),
        "and hashes a cell exactly as the toy cell with the same fields"
    );
    let mut store = CellStore::new();
    let given_id = store.insert(given.clone());
    let derived_id = store.insert(derived.clone());
    assert_ne!(given_id, derived_id, "the store keeps both cells");
    assert_eq!(
        (given.lhs(), given.rhs(), given.provenance()),
        (derived.lhs(), derived.rhs(), derived.provenance()),
        "which share their faces and provenance"
    );
    assert_eq!(
        (ToyOrient::Given, ToyOrient::Derived),
        (
            ToyOrient::from(given.orient()),
            ToyOrient::from(derived.orient())
        ),
        "and keep their own orientation tags"
    );
}

#[test]
fn default_answers_and_adversarial_boundaries_stay_distinct()
{
    use core::hash::Hasher as _;

    let root = at(&[]);
    let left = at(&[PositionStep::from(0_usize)]);
    let right = at(&[PositionStep::from(1_usize)]);
    for (a, b, expected) in [
        (&root, &root, PositionOrder::Same),
        (&root, &left, PositionOrder::Encloses),
        (&left, &root, PositionOrder::EnclosedBy),
        (&left, &right, PositionOrder::Incomparable),
    ] {
        assert_eq!(
            expected,
            <WithheldConvexity as AlphabetLie>::position_order(a, b)
        );
        assert_eq!(
            PositionOrder::Incomparable,
            <IncomparablePositions as AlphabetLie>::position_order(a, b)
        );
    }
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        <IncomparablePositions as AlphabetLie>::convexity_discharge()
    );
    assert_eq!(
        ConvexityDischarge::ReCheckRequired,
        <WithheldConvexity as AlphabetLie>::convexity_discharge()
    );
    let branch = Toy::succ(Toy::zero());
    let binary = Toy::add(branch.clone(), branch.clone());
    let replacement = Toy::var("new");
    assert_eq!(
        Ok(Toy::add(replacement.clone(), branch.clone())),
        <Lying<WithheldConvexity> as CellAlphabet>::splice_cmd_at(
            &binary,
            &left,
            replacement.clone()
        )
    );
    let reset = Toy::add(Toy::zero(), Toy::zero());
    for (pos, expected) in [
        (root, replacement.clone()),
        (left, Toy::add(replacement.clone(), reset.clone())),
        (right, Toy::add(reset, replacement.clone())),
        (
            at(&[PositionStep::from(0_usize), PositionStep::from(0_usize)]),
            Toy::add(Toy::succ(replacement.clone()), branch.clone()),
        ),
    ] {
        assert_eq!(
            Ok(expected),
            <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(
                &binary,
                &pos,
                replacement.clone()
            )
        );
    }
    assert_eq!(
        Ok(Toy::succ(replacement.clone())),
        <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(
            &Toy::succ(branch),
            &at(&[PositionStep::from(0_usize)]),
            replacement.clone()
        )
    );
    let outside = at(&[PositionStep::from(2_usize)]);
    assert_eq!(
        Err(gandr_theory_cell_complexes::CommandSpliceRefusal::OffTerm),
        <Lying<NonLocalSplice> as CellAlphabet>::splice_cmd_at(
            &binary,
            &outside,
            replacement.clone()
        )
    );
    assert_eq!(
        Err(gandr_theory_cell_complexes::CommandSpliceRefusal::OffTerm),
        <Lying<WithheldConvexity> as CellAlphabet>::splice_cmd_at(&binary, &outside, replacement)
    );
    for orientation in [ToyOrient::Given, ToyOrient::Derived] {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        hasher.write(b"prior contents");
        let before = hasher.finish();
        <CollidingAddresses as AlphabetLie>::hash_orientation(orientation, &mut hasher);
        assert_eq!(before, hasher.finish());
        let mut bytes = Written(vec![1, 2, 3]);
        <CollidingAddresses as AlphabetLie>::hash_orientation(orientation, &mut bytes);
        assert_eq!(Written(vec![1, 2, 3]), bytes);
    }
}
