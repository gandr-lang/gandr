//! The carried footprint against an independent walk of the arena.
//!
//! The walk reads the source program's arena and its items' keys, never the
//! content table, its formers or its supports, so a reference the table
//! drops, invents or files in the wrong position disagrees with it.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::DeclarationContent;
use gandr_core_incremental::HoleMark;
use gandr_core_incremental::Occurrence;
use gandr_core_incremental::Opacity;
use gandr_core_incremental::Program;
use gandr_core_incremental::Reference;
use gandr_core_incremental::check_program;
use gandr_core_incremental::footprint_of;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use proptest::prelude::ProptestConfig;
use proptest::proptest;
use quenchant_shape::shape::Maybe;

use crate::common::lower;
use crate::generate::CASES;
use crate::generate::apply;
use crate::generate::program_and_edits;

/// An arena node, named without the content table's formers.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// Whether a path from a root has crossed a signature or a type former.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Position
{
    /// Only term formers enclose the node.
    Term,
    /// A signature or a type former encloses the node.
    Type,
}

/// The reference the position `position` of `program` names, found by
/// scanning its items rather than through the layout's maps.
///
/// # Specification
/// - ensures: the key and the count of earlier equal keys of the item at
///   `position`; the unoccupied reference when no item sits there.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated shadowing, reordering and dangling references
///   compare this linear resolution with the table's indexed one.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
#[spec(ensures: |ret| match ret {
    Reference::Unoccupied => program.items().iter().all(|item| item.declaration().constant() != position),
    Reference::Item { ref key, occurrence } => program.items().iter().enumerate().any(|(ordinal, item)|
        item.declaration().constant() == position && item.key() == key
            && usize::from(occurrence) == program.items().iter().take(ordinal).filter(|earlier| earlier.key() == key).count()),
})]
fn reference(
    program: &Program,
    position: ConstantIndex,
) -> Reference
{
    let Some((ordinal, item)) = program
        .items()
        .iter()
        .enumerate()
        .find(|&(_, item)| item.declaration().constant() == position)
    else {
        return Reference::Unoccupied;
    };
    let occurrence = program
        .items()
        .iter()
        .take(ordinal)
        .filter(|earlier| earlier.key() == item.key())
        .count();
    Reference::Item {
        key: item.key().clone(),
        occurrence: Occurrence::from(occurrence),
    }
}

/// The reads, type reads and opacity a walk of `program`'s arena finds from
/// the roots `signature` and `body`.
///
/// # Specification
/// - requires: the roots are built from the generator's vocabulary: literals,
///   constants, holes, thunks of returns, base types, thunk and returner types
///   and codes.
/// - ensures: every constant and abstract type beneath a root is read; those
///   beneath the signature or a type former are type reads; an id the arena
///   does not hold makes the item opaque.
/// - panics: a former outside the generator's vocabulary, which this walk does
///   not claim.
/// - executable: none — the walk is the oracle; its only checker is the table
///   it is compared with.
///
/// # Adequacy
/// - hypothesis: L2 — the walk and the table share no code; they agree on
///   generated programs and every edited intermediate.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
fn walk(
    program: &Program,
    signature: Maybe<ValueTypeId, gandr_core_checker::signature::Absent>,
    body: Maybe<ValueId, gandr_core_checker::body::Absent>,
) -> (BTreeSet<Reference>, BTreeSet<Reference>, Opacity)
{
    let mut work = Vec::new();
    if let Maybe::Present(root) = signature {
        work.push((Node::ValueType(root), Position::Type));
    }
    if let Maybe::Present(root) = body {
        work.push((Node::Value(root), Position::Term));
    }
    let mut seen = BTreeSet::new();
    let mut reads = BTreeSet::new();
    let mut type_reads = BTreeSet::new();
    let mut opacity = Opacity::Transparent;
    while let Some((node, position)) = work.pop() {
        if !seen.insert((node, position)) {
            continue;
        }
        let mut read = |constant: ConstantIndex, position: Position| {
            let named = reference(program, constant);
            let _fresh = reads.insert(named.clone());
            if position == Position::Type {
                let _fresh = type_reads.insert(named);
            }
        };
        match node {
            Node::Value(id) => match program.arena().value(id) {
                Some(&Value::Variable { .. } | &Value::Literal(_) | &Value::Hole(_)) => {},
                Some(&Value::Constant(constant)) => read(constant, position),
                Some(&Value::Thunk(suspended)) => {
                    work.push((Node::Computation(suspended), position));
                },
                Some(other) => panic!("the generator builds no {other:?}"),
                None => opacity = Opacity::Opaque,
            },
            Node::Computation(id) => match program.arena().computation(id) {
                Some(&Computation::Return(value)) => work.push((Node::Value(value), position)),
                Some(other) => panic!("the generator builds no {other:?}"),
                None => opacity = Opacity::Opaque,
            },
            Node::ValueType(id) => match program.arena().value_type(id) {
                Some(&ValueType::Base(_)) => {},
                Some(&ValueType::Abstract(constant)) => read(constant, Position::Type),
                Some(&ValueType::Thunk(suspended)) => {
                    work.push((Node::CompType(suspended), Position::Type));
                },
                Some(&ValueType::Element { code, .. }) => {
                    work.push((Node::Value(code), Position::Type));
                },
                Some(other) => panic!("the generator builds no {other:?}"),
                None => opacity = Opacity::Opaque,
            },
            Node::CompType(id) => match program.arena().comp_type(id) {
                Some(&CompType::Returner {
                    result,
                    ref effects,
                }) => {
                    work.push((Node::ValueType(result), Position::Type));
                    work.extend(
                        effects
                            .types()
                            .map(|ty| (Node::ValueType(ty), Position::Type)),
                    );
                },
                Some(other) => panic!("the generator builds no {other:?}"),
                None => opacity = Opacity::Opaque,
            },
        }
    }
    (reads, type_reads, opacity)
}

/// Check `program` and compare every item's carried footprint with
/// [`walk`].
///
/// # Specification
/// - ensures: asserts exact reads, type reads, opacity and hole marks for every
///   item; checking keeps the program's items, whose count the predicate
///   checks.
/// - panics: on a disagreement, or a fixture the checker refuses to order.
///
/// # Adequacy
/// - hypothesis: L2 — generated programs and their edited intermediates
///   separate omitted, invented and misfiled references.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
#[spec(captures: [count = program.items().len()], ensures: program.items().len() == count)]
fn assert_footprints(program: &mut Program)
{
    let checked = check_program(program, CheckBudget::DEFAULT).expect("ordered program");
    let mut found = BTreeSet::new();
    for (item, checkpoint) in program.items().iter().zip(checked.checkpoints().items()) {
        let DeclarationContent::Value { signature, body } = *item.declaration().content()
        else {
            panic!("the generator declares values only");
        };
        let (reads, type_reads, opacity) = walk(program, signature, body);
        let footprint = footprint_of(checkpoint.content());
        found.clear();
        found.extend(footprint.reads().cloned());
        assert_eq!(found, reads, "reads of {:?}", item.key());
        found.clear();
        found.extend(footprint.type_reads().cloned());
        assert_eq!(found, type_reads, "type reads of {:?}", item.key());
        assert_eq!(footprint.opacity(), opacity, "opacity of {:?}", item.key());
        assert_eq!(
            footprint.hole(),
            match body {
                Maybe::Present(_) => HoleMark::Filled,
                Maybe::Absent(_) => HoleMark::Hole,
            },
            "hole mark of {:?}",
            item.key()
        );
    }
}

proptest! {
    // `PROPTEST_CASES` scales the witness past the suite's default.
    #![proptest_config(ProptestConfig::with_cases(
        std::env::var("PROPTEST_CASES").ok().and_then(|cases| cases.parse().ok()).unwrap_or(CASES)
    ))]

    /// Every generated program and each edited intermediate agrees with an
    /// independent walk of the arena, signatures and shadowed references
    /// included.
    #[test]
    fn carried_footprint_matches_reference_walk((statements, edits) in program_and_edits()) {
        let mut current = statements;
        assert_footprints(&mut lower(&current));
        for edit in &edits {
            current = apply(&current, edit);
            assert_footprints(&mut lower(&current));
        }
    }
}
