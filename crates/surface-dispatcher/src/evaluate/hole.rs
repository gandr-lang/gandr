//! A hole a run reaches: the perform focusing leaves where the source wrote a
//! hole, which no handler claims, read back to the hole and the place its
//! source writes it.

use alloc::collections::BTreeMap;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::REACHED;
use gandr_core_sequent::REACHED_HOLE;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::Literal;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

/// Where `module` writes each hole a run can reach, by its name: the span of
/// the one hole bearing it, or the shared absence where holes of several
/// sources share one name.
///
/// # Specification
/// - requires: `module` was lowered into `core`.
/// - ensures: every hole a computation of `module`'s origins holds is keyed; a
///   name every such computation writes at one span maps to that span, and one
///   written at two spans to [`hole_site::Absent::Shared`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the walk over the origins.
///
/// # Adequacy
/// - hypothesis: L3 — a run reaching a hole is reported at the hole's span.
/// - witness: `evaluate::entry::tests::a_hole_reached_stops_the_entry_by_name_1881`
pub(super) fn hole_sites(
    core: &CoreArena,
    module: &LoweredModule<'_>,
) -> BTreeMap<HoleId, Maybe<ByteSpan, hole_site::Absent>>
{
    let mut sites = BTreeMap::new();
    for &(computation, origin) in module.origins().computations() {
        let Some(&Computation::Hole(hole)) = core.computation(computation)
        else {
            continue;
        };
        let span = origin.span();
        let _held = sites
            .entry(hole)
            .and_modify(|site: &mut Maybe<ByteSpan, hole_site::Absent>| {
                if *site != Maybe::Present(span) {
                    *site = Maybe::Absent(hole_site::Absent::Shared);
                }
            })
            .or_insert(Maybe::Present(span));
    }
    sites
}

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

quenchant_shape::reason_enum! {
    /// Why a reached hole has no site to report.
    pub mod hole_site {
        /// The hole is not one the program's sources write at one place.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Holes of several sources bear its name.
            Shared,
            /// No computation of the program's sources writes it.
            Unwritten,
        }
    }
}
