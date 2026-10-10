//! Independent arena-walk oracle for the content table's carried footprint.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    warn(
        specification_present,
        spec_attribute_present,
        adequacy_present,
        adequacy_block_grammar
    )
)]

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
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
use quenchant_shape::shape::Maybe;

/// An arena node, without consulting the content encoding's formers or edges.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value occurrence.
    Value(ValueId),
    /// A computation occurrence.
    Computation(ComputationId),
    /// A value type occurrence.
    ValueType(ValueTypeId),
    /// A computation type occurrence.
    CompType(CompTypeId),
}

/// Whether a path has crossed a type former.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Position
{
    /// Only term formers enclose this occurrence.
    Value,
    /// A signature or type former encloses this occurrence.
    Type,
}

/// Resolve by scanning source items, independently of the layout's maps.
///
/// # Specification
/// - ensures: the key and count of prior equal keys at the requested admission
///   position; an unoccupied position is the unoccupied reference.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated shadowing, reordering and missing references
///   compare this linear resolution with the content table's indexed one.
/// - witness: `tests::incremental::carried_footprint_matches_reference_walk`
#[anodized::spec(ensures: |ret| match ret {
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

/// Compare every carried item footprint with a direct walk of the arena.
///
/// # Specification
/// - ensures: asserts exact reads, type reads, opacity and hole marks for every
///   item; the oracle never reads a content node or its support. The source
///   items are unchanged by checking and observation.
/// - panics: a semantic mismatch or a failed fixture check.
///
/// # Adequacy
/// - hypothesis: L2 — generated programs and edited intermediates distinguish
///   omissions, invented references and incorrect type-position promotion.
/// - witness: `tests::incremental::carried_footprint_matches_reference_walk`
#[anodized::spec(captures: items = program.items().to_vec(), ensures: program.items() == items)]
pub fn assert_footprints(program: &mut Program)
{
    let checked = check_program(program, CheckBudget::DEFAULT).expect("ordered program");
    for (item, checkpoint) in program.items().iter().zip(checked.checkpoints().items()) {
        let mut work = Vec::new();
        if let Maybe::Present(root) = item.declaration().signature() {
            work.push((Node::ValueType(root), Position::Type));
        }
        if let Maybe::Present(root) = item.declaration().body() {
            work.push((Node::Value(root), Position::Value));
        }
        let mut seen = BTreeSet::new();
        let mut reads = BTreeSet::new();
        let mut type_reads = BTreeSet::new();
        let mut opacity = Opacity::Transparent;
        while let Some((node, position)) = work.pop() {
            if !seen.insert((node, position)) {
                continue;
            }
            let mut record = |constant| {
                let reference = reference(program, constant);
                reads.insert(reference.clone());
                if position == Position::Type {
                    type_reads.insert(reference);
                }
            };
            match node {
                | Node::Value(id) => match program.arena().value(id) {
                    | Some(&Value::Variable { .. } | &Value::Unit | &Value::Literal(_)) => {},
                    | Some(&Value::Constant(constant)) => record(constant),
                    | Some(
                        &Value::Pair(first, second) | &Value::StaticApplication(first, second),
                    ) => {
                        work.extend([
                            (Node::Value(first), position),
                            (Node::Value(second), position),
                        ]);
                    },
                    | Some(
                        &Value::Injection(_, value)
                        | &Value::Lift { body: value, .. }
                        | &Value::StaticLambda(value),
                    ) => work.push((Node::Value(value), position)),
                    | Some(&Value::Thunk(body)) => work.push((Node::Computation(body), position)),
                    | Some(&Value::Quote(ty)) => work.push((Node::ValueType(ty), Position::Type)),
                    | Some(&Value::QuoteComputation(ty)) => {
                        work.push((Node::CompType(ty), Position::Type));
                    },
                    | None => opacity = Opacity::Opaque,
                },
                | Node::Computation(id) => match program.arena().computation(id) {
                    | Some(&Computation::Lambda(body)) => {
                        work.push((Node::Computation(body), position));
                    },
                    | Some(&Computation::Application(head, argument)) => work.extend([
                        (Node::Computation(head), position),
                        (Node::Value(argument), position),
                    ]),
                    | Some(&Computation::Return(value) | &Computation::Force(value)) => {
                        work.push((Node::Value(value), position));
                    },
                    | Some(&Computation::Bind(bound, rest)) => work.extend([
                        (Node::Computation(bound), position),
                        (Node::Computation(rest), position),
                    ]),
                    | Some(&Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    }) => work.extend([
                        (Node::Value(scrutinee), position),
                        (Node::Computation(on_left), position),
                        (Node::Computation(on_right), position),
                    ]),
                    | None => opacity = Opacity::Opaque,
                },
                | Node::ValueType(id) => match program.arena().value_type(id) {
                    | Some(
                        &ValueType::Base(_) | &ValueType::Unit | &ValueType::Universe { .. },
                    ) => {},
                    | Some(&ValueType::Abstract(constant)) => {
                        let reference = reference(program, constant);
                        reads.insert(reference.clone());
                        type_reads.insert(reference);
                    },
                    | Some(
                        &ValueType::Product(first, second)
                        | &ValueType::Sum(first, second)
                        | &ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        },
                    ) => work.extend([
                        (Node::ValueType(first), Position::Type),
                        (Node::ValueType(second), Position::Type),
                    ]),
                    | Some(&ValueType::Thunk(body)) => {
                        work.push((Node::CompType(body), Position::Type));
                    },
                    | Some(&ValueType::Lift { inner, .. }) => {
                        work.push((Node::ValueType(inner), Position::Type));
                    },
                    | Some(&ValueType::Element { code, .. }) => {
                        work.push((Node::Value(code), Position::Type));
                    },
                    | None => opacity = Opacity::Opaque,
                },
                | Node::CompType(id) => match program.arena().comp_type(id) {
                    | Some(&CompType::Returner(result)) => {
                        work.push((Node::ValueType(result), Position::Type));
                    },
                    | Some(
                        &CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain },
                    ) => work.extend([
                        (Node::ValueType(domain), Position::Type),
                        (Node::CompType(codomain), Position::Type),
                    ]),
                    | Some(&CompType::Element { code, .. }) => {
                        work.push((Node::Value(code), Position::Type));
                    },
                    | None => opacity = Opacity::Opaque,
                },
            }
        }
        let footprint = footprint_of(checkpoint.content());
        assert_eq!(footprint.reads().cloned().collect::<BTreeSet<_>>(), reads);
        assert_eq!(
            footprint.type_reads().cloned().collect::<BTreeSet<_>>(),
            type_reads
        );
        assert_eq!(footprint.opacity(), opacity);
        assert_eq!(footprint.hole(), match item.declaration().body() {
            | Maybe::Present(_) => HoleMark::Filled,
            | Maybe::Absent(_) => HoleMark::Hole,
        });
    }
}
