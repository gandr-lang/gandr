use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_session::Relation;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecursionIndex;
use gandr_core_term::session::SessionType;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::FieldLabel;
use quenchant_shape::shape::Maybe;

use super::PayloadPair;
use super::relate;
use crate::CheckBudget;
use crate::CheckingContext;

/// The session type over `syntax` rooted at its first node, its payloads
/// `payloads`, at `state`.
///
/// # Specification
/// trivial.
fn session(
    arena: &mut CoreArena,
    syntax: Vec<ProtocolSyntax>,
    payloads: &[ValueTypeId],
    state: ProtocolState,
) -> ValueTypeId
{
    let protocol = Protocol::new(
        syntax,
        ProtocolState::from(0_usize),
        PayloadCount::from(payloads.len()),
    )
    .unwrap();
    let session = SessionType::new(Arc::new(protocol), Arc::from(payloads))
        .unwrap()
        .at(state)
        .unwrap();
    arena.value_type_session(session)
}

#[test]
fn equivalence_sees_through_unfolding_and_payloads()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    // mu t. !Integer. t
    let folded = |arena: &mut CoreArena, payload| {
        session(
            arena,
            alloc::vec![
                ProtocolSyntax::Mu(ProtocolState::from(1_usize)),
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(2_usize),
                },
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ],
            &[payload],
            ProtocolState::from(0_usize),
        )
    };
    let left = folded(&mut arena, integer);
    let right = folded(&mut arena, string);
    // !Integer. mu t. !Integer. t, past its first send
    let unfolded = session(
        &mut arena,
        alloc::vec![
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(1_usize),
                next: ProtocolState::from(3_usize),
            },
            ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
        ],
        &[string, integer],
        ProtocolState::from(1_usize),
    );
    let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let slot = gandr_kernel_term::session::PayloadSlot;
    assert_eq!(
        relate(&context, left, unfolded, Relation::Equivalent),
        Ok(Maybe::Present(alloc::vec![PayloadPair {
            slots: (slot(0), slot(1)),
            types: (integer, integer),
        }])),
        "the binder past the prefix unfolds to the folded body, payload by payload"
    );
    assert_eq!(
        relate(&context, left, right, Relation::Equivalent),
        Ok(Maybe::Present(alloc::vec![PayloadPair {
            slots: (slot(0), slot(0)),
            types: (integer, string),
        }])),
        "the shapes relate and the differing payload pair is handed to conversion"
    );
}

#[test]
fn subtyping_follows_gay_and_hole_at_endpoints()
{
    let mut arena = CoreArena::new();
    let choice = |arena: &mut CoreArena, labels: &[&str]| {
        let mut syntax = alloc::vec![ProtocolSyntax::Select(
            labels
                .iter()
                .enumerate()
                .map(|(position, &label)| {
                    (
                        FieldLabel::from(alloc::string::String::from(label)),
                        ProtocolState::from(position.saturating_add(1)),
                    )
                })
                .collect::<BTreeMap<_, _>>()
        )];
        syntax.extend(labels.iter().map(|_| ProtocolSyntax::End));
        session(arena, syntax, &[], ProtocolState::from(0_usize))
    };
    let narrow = choice(&mut arena, &["a"]);
    let wide = choice(&mut arena, &["a", "b"]);
    let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        relate(&context, narrow, wide, Relation::Subtype),
        Ok(Maybe::Present(Vec::new())),
        "fewer selections substitute for more"
    );
    assert_eq!(
        relate(&context, wide, narrow, Relation::Subtype),
        Ok(Maybe::Absent(super::related::Absent::Unrelated)),
        "more selections do not substitute for fewer"
    );
    assert_eq!(
        relate(&context, narrow, wide, Relation::Equivalent),
        Ok(Maybe::Absent(super::related::Absent::Unrelated)),
        "equivalence requires equal widths"
    );
}
