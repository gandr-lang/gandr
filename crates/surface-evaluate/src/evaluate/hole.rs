//! A hole a run reaches: the perform focusing leaves where the source wrote a
//! hole, which no handler claims, read back to the hole and the place its
//! source writes it.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::REACHED;
use gandr_core_sequent::REACHED_HOLE;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::Literal;
use quenchant_shape::shape::Maybe;

/// The hole the command `at` reaches, when it is the perform focusing leaves
/// for a hole.
///
/// # Specification
/// - requires: nothing.
/// - ensures: present exactly when `at` is a perform of [`REACHED`] of
///   [`REACHED_HOLE`] whose payload is an integer literal naming a hole, with
///   that hole.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the match on the command.
///
/// # Adequacy
/// - hypothesis: L3 — a run reaching a hole is reported by its name, and a run
///   stuck at an unhandled operation is not.
/// - witness: `evaluate::entry::tests::a_hole_reached_stops_the_entry_by_name_1881`
pub(super) fn reached(
    arena: &CommandArena,
    at: CommandId,
) -> Maybe<HoleId, reached_hole::Absent>
{
    let Some(&CommandNode::Perform {
        ref signature,
        ref operation,
        payload,
        ..
    }) = arena.command(at)
    else {
        return Maybe::Absent(reached_hole::Absent::Other);
    };
    if signature.name().as_ref() != REACHED_HOLE || operation.as_ref() != REACHED {
        return Maybe::Absent(reached_hole::Absent::Other);
    }
    match arena.producer(payload) {
        Some(&ProducerNode::Literal(Literal::Integer(ref place))) => place
            .magnitude()
            .as_ref()
            .parse::<u32>()
            .map_or(Maybe::Absent(reached_hole::Absent::Other), |place| {
                Maybe::Present(HoleId::from(place))
            }),
        Some(_) | None => Maybe::Absent(reached_hole::Absent::Other),
    }
}

quenchant_shape::reason_enum! {
    /// Why a stuck command reaches no hole.
    pub mod reached_hole {
        /// The command is not the perform focusing leaves for a hole.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Any other command.
            Other,
        }
    }
}
