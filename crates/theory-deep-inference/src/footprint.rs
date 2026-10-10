//! Polarized match footprints: an independence test that sits beside the shift
//! guard and that nothing in the crate consumes.
//!
//! [`derive_shift_equivalence`](crate::derive_shift_equivalence) remains the
//! only licence for a shift. This module measures one question: whether a
//! polarized independence test, rewritten against matched-but-preserved, read
//! off the match image rather than declared on the alphabet, licenses a
//! strictly larger commuting class than the guard's incomparable-positions
//! conjunct. It answers by disagreeing with the guard on recorded fixtures,
//! and the disagreements are the deliverable; the integration suite's
//! `footprint` area holds them.
//!
//! # The test
//!
//! The independence relation on transitions in Melliès and Stefanesco,
//! *Concurrent Separation Logic Meets Template Games*, has four conditions
//! over a quadruple `(rd, wr, lock, mem)`, of which only two are about
//! locations read and written:
//!
//! ```text
//! (rd(p) ∪ wr(p)) ∩ wr(p') = ∅        lock(p) ∩ lock(p') = ∅
//! (rd(p') ∪ wr(p')) ∩ wr(p) = ∅       mem(p) ∩ mem(p') = ∅
//! ```
//!
//! Independence is polarized, not disjointness: two transitions may share
//! read locations freely, and only write against anything collides. `lock` and
//! `mem` (allocation) have no counterpart at the cell-application layer, so
//! this module implements the two `rd`/`wr` conjuncts and nothing else.
//!
//! # What a footprint is here
//!
//! A footprint is attached to a transition, one [`CellApp`] firing in one
//! term, never to a store or a cell. Every position the redex covers (the
//! match image: the redex root and everything under it) lands in exactly one
//! of three classes:
//!
//! - **written**: the node at that address does not survive the rewrite as the
//!   same node: it is absent afterwards, its children change, or its own
//!   content changes once the children are held equal;
//! - **read**: the node survives, and the firing at its recorded position is
//!   sensitive to the content there: the rule looked and left it alone;
//! - **framed**: the node survives and the firing is insensitive to it: the
//!   hole instances the rule carries through without inspecting.
//!
//! Only `written` and `read` enter the footprint. The frame is excluded on
//! purpose: a transition that neither reads nor writes a location does not
//! collide there, however deep inside its match image that location sits.
//!
//! # Three modelling choices
//!
//! 1. **The spine is not in the footprint.** Positions strictly above the redex
//!    are traversed to reach it and rebuilt by splicing, but their nodes are
//!    unchanged. Counting the spine would make every pair of applications in
//!    one term collide at the root; footprints in the source are shallow.
//! 2. **The write test is node-local.** A rewrite strictly below a node changes
//!    its subterm but not the node, so subtree-keyed writes would again collide
//!    at the root. Node-locality is decided by grafting: hold the immediate
//!    children equal and ask whether what is left agrees.
//! 3. **Addresses are absolute term positions.** The source's footprints range
//!    over machine addresses, which do not move; a term position does. A rule
//!    that relocates its frame reports the vacated addresses as written, so
//!    such a pair is refused rather than licensed. That is conservative, and it
//!    is the shape of the debt an adoption would take on: a residual map on
//!    positions, which [`CellApp`] has no room for.
//!
//! The shapes are generic in the cell alphabet: an address is `A::Pos`, so a
//! carrier whose positions address a heap instantiates [`MatchFootprint`] and
//! [`FootprintIndependence`] rather than re-inventing them. No alphabet in the
//! tree addresses a store today, so the heap side is interface only, and an
//! instantiation re-decides the three choices above rather than inheriting
//! them.
//!
//! # What this module does not have
//!
//! Allocation has no event to read off: its condition needs a per-transition
//! freshness datum, and the freshness this crate has,
//! [`CellAlphabet::rename_apart`] and [`CellAlphabet::skolemize`], mints fresh
//! metavariable names for unification hygiene and records no address a firing
//! brought into or out of existence. A permission carrier is absent too: what
//! this module computes is owned against framed at one transition, while a
//! permission divides one location among simultaneous holders, a different
//! axis. [`FiringPermission`](gandr_theory_cell_complexes::FiringPermission)
//! is an admissibility flag on a cell's provenance and unrelated to either.
//!
//! # The metavariable seam
//!
//! The overlap enumerator counts a metavariable position as a composition
//! seam, so over an alphabet whose every subterm is a command position, a cell
//! whose right-hand side exposes a hole overlaps every cell and the guard's
//! overlap conjunct refuses the pair. This module consults the enumerator not
//! at all, so part of any measured gap between the two tests is that seam and
//! part is genuine polarization. The integration suite separates them with a
//! fixture whose only overlap is a hole seam.
//!
//! # Cost
//!
//! Unoptimized on purpose: one rewrite per candidate probe per covered
//! position, plus a quadratic scan for immediate children. It is a measurement
//! instrument, not a fast path.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

/// Whether the node at one address survives an application as the same node:
/// the write test, decided node-locally rather than on subterms.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum NodeSurvival
{
    /// The address still carries a node with the same immediate-child
    /// addresses and the same content once those children are held equal.
    Preserved,
    /// The address is gone, its children changed, or its own content changed.
    Replaced,
}

/// Whether an application's firing is sensitive to the content at an address
/// inside its match image: the read/frame test.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ContentSensitivity
{
    /// Some probe substituted at the address stops the cell firing at its
    /// recorded position: the rule looked there.
    Sensitive,
    /// No available probe stops it: the address is frame, carried through
    /// without being inspected.
    Insensitive,
}

/// The polarized footprint of one application in one term: the match image
/// split into rewritten, matched-but-preserved, and framed addresses.
///
/// The three vectors partition the addresses the redex covers, in the
/// alphabet's own enumeration order, and are pairwise disjoint by
/// construction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatchFootprint<A: CellAlphabet = SequentAlphabet>
{
    /// The position the application fired at: the match image's root.
    pub at: A::Pos,
    /// The addresses the rewrite destroys or replaces.
    pub written: Vec<A::Pos>,
    /// The addresses the rule matches and leaves standing.
    pub read: Vec<A::Pos>,
    /// The addresses the rule carries through without inspecting: the frame,
    /// which is not part of the footprint.
    pub framed: Vec<A::Pos>,
}

/// Why a footprint could not be read off a term and an application.
///
/// A footprint is a property of a transition, so an application that is not a
/// transition of this term has none.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FootprintObstruction<A: CellAlphabet = SequentAlphabet>
{
    /// The application names a cell the store does not hold.
    UnknownCell
    {
        /// The identifier that resolved to nothing.
        cell: CellId,
    },
    /// The application does not fire at its recorded position in this term, so
    /// there is no transition to attach a footprint to.
    StepDoesNotFire
    {
        /// The step that failed to fire.
        step: Box<CellApp<A>>,
    },
}

/// The polarized independence verdict for two footprints: the two `rd`/`wr`
/// conjuncts, and nothing else.
///
/// A read/read overlap is not a collision: it is the one place the source lets
/// this carrier earn more than the guard's incomparable-positions conjunct.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FootprintIndependence<A: CellAlphabet = SequentAlphabet>
{
    /// Neither write set meets the other's write or read set.
    Independent,
    /// Both applications rewrite the same address.
    WriteWrite
    {
        /// The address both of them write.
        position: A::Pos,
    },
    /// One application rewrites an address the other matches and preserves.
    ReadWrite
    {
        /// The address one writes and the other reads.
        position: A::Pos,
    },
}

/// Read the polarized footprint of `app` firing in `term`.
///
/// # Specification
/// - requires: `A::command_positions` enumerates the term's addresses without
///   repetition, and `A::position_order` decides prefix containment on them.
/// - ensures: a footprint whose three vectors partition exactly the addresses
///   `app.at` covers (itself and everything it encloses): `written` the
///   addresses whose node does not survive the rewrite, `read` the surviving
///   addresses whose content the firing depends on, `framed` the rest, each in
///   `A::command_positions` order.
/// - provides: the transition-attached datum the polarized independence test
///   reads, derived from the instance and never from the alphabet or the
///   overlap enumerator.
/// - fails: [`FootprintObstruction::UnknownCell`] for an unresolvable
///   identifier and [`FootprintObstruction::StepDoesNotFire`] for an
///   application that does not fire at its recorded position.
/// - panics: none.
/// - intension: the probes are the term's own distinct subterms in enumeration
///   order, so the read/frame split is a function of the input alone.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — the three classes own separate decision surfaces, each
///   separated by a fixture moving one address between them: a ground redex
///   whose whole image is written, a rule whose matched root survives into
///   `read`, and a rule whose hole instance lands in `framed` while the sibling
///   it matched lands in `written`; the refusals by an unstored identifier and
///   a non-firing step; the partition and the order by a sweep over the
///   differential fixture family that fails on any address classified twice,
///   left out, taken from above the redex, or emitted out of order.
/// - witness: `tests::footprint::a_ground_redex_writes_its_whole_match_image`
/// - witness: `tests::footprint::a_preserved_root_is_read_and_its_hole_is_framed`
/// - witness: `footprint::tests::a_footprint_needs_a_transition_to_attach_to`
/// - witness: `tests::footprint::every_footprint_partitions_exactly_the_addresses_its_redex_covers`
#[inline]
#[spec(ensures: |output| match store.get(app.cell) {
    Maybe::Absent(_) => matches!(output, Err(FootprintObstruction::UnknownCell { cell }) if cell == app.cell),
    Maybe::Present(cell) => match rewrite_at(cell, term, &app.at) {
        Maybe::Absent(_) => matches!(output, Err(FootprintObstruction::StepDoesNotFire { ref step }) if **step == *app),
        Maybe::Present(ref after) => output.as_ref().is_ok_and(|footprint| {
                let positions = A::command_positions(term);
                let after_positions = A::command_positions(after);
                let probes = distinct_subterms::<A>(term, &positions);
                footprint.at == app.at
                    && [&footprint.written, &footprint.read, &footprint.framed].iter().all(|part| part.iter().eq(positions.iter().filter(|position| part.contains(position))))
                    && positions.iter().all(|position| {
                        let in_write = footprint.written.contains(position);
                        let in_read = footprint.read.contains(position);
                        let in_frame = footprint.framed.contains(position);
                        if matches!(A::position_order(&app.at, position), PositionOrder::Same | PositionOrder::Encloses) {
                            match node_survival::<A>(term, after, &positions, &after_positions, position) {
                                NodeSurvival::Replaced => in_write && !in_read && !in_frame,
                                NodeSurvival::Preserved => match content_sensitivity::<A>(cell, term, &app.at, position, &probes) {
                                    ContentSensitivity::Sensitive => !in_write && in_read && !in_frame,
                                    ContentSensitivity::Insensitive => !in_write && !in_read && in_frame,
                                },
                            }
                        } else { !in_write && !in_read && !in_frame }
                    })
        }),
    },
})]
pub fn match_footprint<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    app: &CellApp<A>,
) -> Result<MatchFootprint<A>, FootprintObstruction<A>>
where
    A: CellAlphabet,
{
    let Maybe::Present(cell) = store.get(app.cell)
    else {
        return Err(FootprintObstruction::UnknownCell { cell: app.cell });
    };
    let Maybe::Present(after) = rewrite_at(cell, term, &app.at)
    else {
        return Err(FootprintObstruction::StepDoesNotFire {
            step: Box::new(app.clone()),
        });
    };
    let before_positions = A::command_positions(term);
    let after_positions = A::command_positions(&after);
    let probes = distinct_subterms::<A>(term, &before_positions);
    let mut written = Vec::new();
    let mut read = Vec::new();
    let mut framed = Vec::new();
    for position in &before_positions {
        // Inside the match image: the redex root and everything it encloses.
        // The spine above it is traversed, not read.
        if !matches!(
            A::position_order(&app.at, position),
            PositionOrder::Same | PositionOrder::Encloses
        ) {
            continue;
        }
        match node_survival::<A>(term, &after, &before_positions, &after_positions, position) {
            | NodeSurvival::Replaced => written.push(position.clone()),
            | NodeSurvival::Preserved => {
                match content_sensitivity::<A>(cell, term, &app.at, position, &probes) {
                    | ContentSensitivity::Sensitive => read.push(position.clone()),
                    | ContentSensitivity::Insensitive => framed.push(position.clone()),
                }
            },
        }
    }
    Ok(MatchFootprint {
        at: app.at.clone(),
        written,
        read,
        framed,
    })
}

/// Decide polarized independence of two footprints.
///
/// # Specification
/// - requires: the two footprints were read off the same term, so their
///   addresses are comparable.
/// - ensures: [`FootprintIndependence::Independent`] exactly when neither write
///   set meets the other's write set or read set; otherwise the variant naming
///   the first colliding address, searched in the left footprint's `written`
///   order first and then the right's.
/// - provides: the commutation licence the polarized reading grants, which
///   permits read/read overlap and so differs from the shift guard on both of
///   its first two conjuncts.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the three verdicts own separate decision surfaces: a pair
///   rewriting one address collides write/write, a pair whose inner application
///   rewrites the outer's matched-and-preserved skeleton collides read/write,
///   and a pair whose only shared address is read by both is independent; the
///   scan order is pinned by a pair colliding at every address of one match
///   image, which fixes that the reported address is the earliest in
///   enumeration order. A genuine identity transition has no reads or writes
///   and is independent of itself. Inventing a collision in an empty write
///   domain changes the verdict.
/// - witness: `tests::footprint::two_root_rules_sharing_only_a_read_node_are_independent`
/// - witness: `tests::footprint::a_rule_that_destroys_a_node_another_only_reads_is_refused`
/// - witness: `tests::footprint::two_rules_rewriting_one_child_collide_on_writes`
/// - witness: `tests::footprint::a_pair_colliding_several_ways_reports_the_earliest_address_it_scans`
/// - witness: `footprint::tests::node_and_probe_boundaries_distinguish_survival_from_sensitivity`
#[inline]
#[must_use]
#[spec(ensures: |output| left.written.iter().find(|position| right.written.contains(position) || right.read.contains(position)).map_or_else(
    || right.written.iter().find(|position| left.read.contains(position)).map_or(output == FootprintIndependence::Independent,
        |expected| matches!(output, FootprintIndependence::ReadWrite { ref position } if position == expected)),
    |expected| if right.written.contains(expected) {
        matches!(output, FootprintIndependence::WriteWrite { ref position } if position == expected)
    } else { matches!(output, FootprintIndependence::ReadWrite { ref position } if position == expected) },
))]
pub fn footprint_independence<A>(
    left: &MatchFootprint<A>,
    right: &MatchFootprint<A>,
) -> FootprintIndependence<A>
where
    A: CellAlphabet,
{
    for position in &left.written {
        if right.written.contains(position) {
            return FootprintIndependence::WriteWrite {
                position: position.clone(),
            };
        }
        if right.read.contains(position) {
            return FootprintIndependence::ReadWrite {
                position: position.clone(),
            };
        }
    }
    for position in &right.written {
        if left.read.contains(position) {
            return FootprintIndependence::ReadWrite {
                position: position.clone(),
            };
        }
    }
    FootprintIndependence::Independent
}

/// The term's distinct subterms, in enumeration order: the probe supply the
/// read/frame split perturbs addresses with.
///
/// # Specification
/// - ensures: one entry per distinct subterm addressed by `positions`, in that
///   order; an alphabet exposing few positions supplies few probes, which makes
///   the split coarser rather than wrong.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a matched root is classified `read` only because some
///   probe stops the firing, and a hole `framed` only because none does. Empty
///   supplies, unavailable addresses and repeated equal subterms retain the
///   first readable occurrence only. Duplicating, dropping or reordering probes
///   changes the direct observer.
/// - witness: `tests::footprint::a_preserved_root_is_read_and_its_hole_is_framed`
/// - witness: `footprint::tests::probe_supply_and_child_boundaries_preserve_order`
#[spec(ensures: |output| {
    let first_position = |wanted: &A::Cmd| positions.iter().position(|position| matches!(A::subterm_cmd_at(term, position), Maybe::Present(ref subterm) if subterm == wanted));
    output.iter().all(|subterm| first_position(subterm).is_some())
        && positions.iter().all(|position| match A::subterm_cmd_at(term, position) { Maybe::Present(ref subterm) => output.contains(subterm), Maybe::Absent(_) => true })
        && output.windows(2).all(|pair| pair.first().zip(pair.last()).is_some_and(|(left, right)| first_position(left) < first_position(right)))
})]
fn distinct_subterms<A>(
    term: &A::Cmd,
    positions: &[A::Pos],
) -> Vec<A::Cmd>
where
    A: CellAlphabet,
{
    let mut out: Vec<A::Cmd> = Vec::new();
    for position in positions {
        let Maybe::Present(subterm) = A::subterm_cmd_at(term, position)
        else {
            continue;
        };
        if !out.contains(&subterm) {
            out.push(subterm);
        }
    }
    out
}

/// The addresses immediately below `parent` among `positions`.
///
/// # Specification
/// - requires: `positions` is a term's complete address set, so "no address
///   strictly between" is decidable inside it.
/// - ensures: every address `parent` encloses with no enclosed intermediary, in
///   `positions` order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a rewrite strictly below a node leaves the node preserved
///   only because its immediate children, and not its grandchildren, are held
///   equal. Complete address sets distinguish children from grandchildren,
///   preserve a reversed enumeration order and leave a leaf with no children.
///   Including the parent or a descendant below an intermediary changes the
///   result.
/// - witness: `tests::footprint::a_preserved_root_is_read_and_its_hole_is_framed`
/// - witness: `footprint::tests::probe_supply_and_child_boundaries_preserve_order`
#[spec(ensures: |output| output.iter().eq(positions.iter().filter(|candidate| A::position_order(parent, candidate) == PositionOrder::Encloses
    && !positions.iter().any(|between| A::position_order(parent, between) == PositionOrder::Encloses && A::position_order(between, candidate) == PositionOrder::Encloses))))]
fn immediate_children<A>(
    positions: &[A::Pos],
    parent: &A::Pos,
) -> Vec<A::Pos>
where
    A: CellAlphabet,
{
    positions
        .iter()
        .filter(|candidate| {
            A::position_order(parent, candidate) == PositionOrder::Encloses
                && !positions.iter().any(|between| {
                    A::position_order(parent, between) == PositionOrder::Encloses
                        && A::position_order(between, candidate) == PositionOrder::Encloses
                })
        })
        .cloned()
        .collect()
}

/// Whether the node at `position` survives the rewrite as the same node.
///
/// The test is a graft: hold the immediate children equal to what the rewrite
/// produced and ask whether the rest of the node agrees. A rewrite strictly
/// below the address then leaves it preserved, which keeps the spine and every
/// ancestor out of the write set.
///
/// # Specification
/// - ensures: [`NodeSurvival::Preserved`] exactly when the address exists in
///   both terms, has the same immediate-child addresses in both, and the
///   before-term with those children replaced by the after-term's agrees with
///   the after-term at the address; otherwise [`NodeSurvival::Replaced`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a ground redex replaces its whole image, a rule whose
///   root survives preserves it, and a rule relocating its frame replaces the
///   vacated addresses. A changed descendant preserves the ancestor, while a
///   changed local head, changed child set or vacated address replaces it.
///   Child enumeration order alone cannot change survival.
/// - witness: `tests::footprint::a_ground_redex_writes_its_whole_match_image`
/// - witness: `tests::footprint::a_preserved_root_is_read_and_its_hole_is_framed`
/// - witness: `footprint::tests::node_and_probe_boundaries_distinguish_survival_from_sensitivity`
#[spec(ensures: |output| {
    let children = immediate_children::<A>(before_positions, position);
    let after_children = immediate_children::<A>(after_positions, position);
    (output == NodeSurvival::Preserved) == (after_positions.contains(position) && children.len() == after_children.len() && children.iter().all(|child| after_children.contains(child))
        && children.iter().try_fold(before.clone(), |current, child| match A::subterm_cmd_at(after, child) {
            Maybe::Present(replacement) => A::splice_cmd_at(&current, child, replacement).ok(),
            Maybe::Absent(_) => None,
        }).is_some_and(|grafted| matches!((A::subterm_cmd_at(&grafted, position), A::subterm_cmd_at(after, position)), (Maybe::Present(ref left), Maybe::Present(ref right)) if left == right)))
})]
fn node_survival<A>(
    before: &A::Cmd,
    after: &A::Cmd,
    before_positions: &[A::Pos],
    after_positions: &[A::Pos],
    position: &A::Pos,
) -> NodeSurvival
where
    A: CellAlphabet,
{
    if !after_positions.contains(position) {
        return NodeSurvival::Replaced;
    }
    let children = immediate_children::<A>(before_positions, position);
    // The two child address lists must denote one set; order is not compared,
    // because an alphabet's enumeration order within one depth is its own.
    let after_children = immediate_children::<A>(after_positions, position);
    if children.len() != after_children.len()
        || !children.iter().all(|child| after_children.contains(child))
    {
        return NodeSurvival::Replaced;
    }
    let mut grafted = before.clone();
    for child in &children {
        let Maybe::Present(replacement) = A::subterm_cmd_at(after, child)
        else {
            return NodeSurvival::Replaced;
        };
        let Ok(next) = A::splice_cmd_at(&grafted, child, replacement)
        else {
            return NodeSurvival::Replaced;
        };
        grafted = next;
    }
    match (
        A::subterm_cmd_at(&grafted, position),
        A::subterm_cmd_at(after, position),
    ) {
        | (Maybe::Present(left), Maybe::Present(right)) if left == right => NodeSurvival::Preserved,
        | _ => NodeSurvival::Replaced,
    }
}

/// Whether the cell's firing at `at` depends on the content at `position`.
///
/// # Specification
/// - requires: `cell` fires at `at` in `term`, and `at` covers `position`.
/// - ensures: [`ContentSensitivity::Sensitive`] when some probe differing from
///   the current content stops the cell firing at `at`;
///   [`ContentSensitivity::Insensitive`] when no supplied probe does.
/// - panics: none.
/// - intension: the probes are tried in supply order and the first refusal
///   decides, so the verdict is an under-approximation of "read" bounded by the
///   probes available, never a guess.
///
/// # Adequacy
/// - hypothesis: L3 — a matched root is sensitive and a carried hole is not. On
///   a firing rule, an empty supply or only the current content cannot
///   demonstrate sensitivity; a different root probe can. Probing a carried
///   hole leaves firing possible. Ignoring equality, supplied probes or the
///   selected address changes the verdict.
/// - witness: `tests::footprint::a_preserved_root_is_read_and_its_hole_is_framed`
/// - witness: `footprint::tests::node_and_probe_boundaries_distinguish_survival_from_sensitivity`
#[spec(ensures: |output| (output == ContentSensitivity::Sensitive) == match A::subterm_cmd_at(term, position) {
    Maybe::Absent(_) => true,
    Maybe::Present(ref current) => probes.iter().any(|probe| probe != current && matches!(A::splice_cmd_at(term, position, probe.clone()), Ok(ref perturbed) if matches!(rewrite_at(cell, perturbed, at), Maybe::Absent(_)))),
})]
fn content_sensitivity<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
    at: &A::Pos,
    position: &A::Pos,
    probes: &[A::Cmd],
) -> ContentSensitivity
where
    A: CellAlphabet,
{
    let Maybe::Present(current) = A::subterm_cmd_at(term, position)
    else {
        return ContentSensitivity::Sensitive;
    };
    for probe in probes {
        if *probe == current {
            continue;
        }
        let Ok(perturbed) = A::splice_cmd_at(term, position, probe.clone())
        else {
            continue;
        };
        if matches!(rewrite_at(cell, &perturbed, at), Maybe::Absent(_)) {
            return ContentSensitivity::Sensitive;
        }
    }
    ContentSensitivity::Insensitive
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;

    use super::*;

    #[test]
    fn the_sequent_alphabet_gives_the_prototype_one_address_to_work_with()
    {
        // The read/frame split is only as fine as the alphabet's address
        // vocabulary. A sequent command pattern has one command position, so
        // the whole match image is the root and the footprint degenerates to
        // "the redex is written": no hole sits at a command position. This is
        // why the differential suite runs on the toy alphabet.
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::frame("Succ", ConsPat::top()),
        );
        let footprint = match_footprint(&store, &term, &CellApp {
            cell: frame,
            at: Pos::root(),
        })
        .expect("the frame-defining cell fires at the root");
        assert_eq!(
            alloc::vec![Pos::root()],
            footprint.written,
            "the only address there is is written"
        );
        assert!(
            footprint.read.is_empty() && footprint.framed.is_empty(),
            "and the alphabet exposes no address for either of the other two classes"
        );
    }

    #[test]
    fn a_footprint_needs_a_transition_to_attach_to()
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        // A term the frame-defining cell has no redex in.
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let step = CellApp {
            cell: frame,
            at: Pos::root(),
        };
        assert_eq!(
            Err(FootprintObstruction::StepDoesNotFire {
                step: Box::new(step.clone()),
            }),
            match_footprint(&store, &term, &step),
            "a footprint is a property of a transition, so a non-transition has none"
        );
        let missing = CellId::from(41_usize);
        assert_eq!(
            Err(FootprintObstruction::UnknownCell { cell: missing }),
            match_footprint(&store, &term, &CellApp {
                cell: missing,
                at: Pos::root(),
            }),
            "and an unresolvable identifier is refused before the term is read"
        );
    }

    #[test]
    fn probe_supply_and_child_boundaries_preserve_order()
    {
        let root = ToyAlphabet::root_position();
        let left = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
        let right = ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]);
        let missing = ToyAlphabet::position_at_path(&[PositionStep::from(9_usize)]);
        let repeated = Toy::add(Toy::zero(), Toy::zero());
        assert!(distinct_subterms::<ToyAlphabet>(&repeated, &[]).is_empty());
        let probes = distinct_subterms::<ToyAlphabet>(&repeated, &[
            right.clone(),
            missing,
            root.clone(),
            left.clone(),
            right.clone(),
        ]);
        assert_eq!(alloc::vec![Toy::zero(), repeated], probes);
        let nested = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
        let mut positions = ToyAlphabet::command_positions(&nested);
        assert_eq!(
            alloc::vec![left.clone(), right.clone()],
            immediate_children::<ToyAlphabet>(&positions, &root)
        );
        assert!(immediate_children::<ToyAlphabet>(&positions, &right).is_empty());
        positions.reverse();
        assert_eq!(
            alloc::vec![right, left],
            immediate_children::<ToyAlphabet>(&positions, &root)
        );
    }

    #[test]
    fn node_and_probe_boundaries_distinguish_survival_from_sensitivity()
    {
        let root = ToyAlphabet::root_position();
        let left = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
        let right = ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]);
        let before = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
        let after = Toy::add(Toy::succ(Toy::succ(Toy::zero())), Toy::zero());
        let before_positions = ToyAlphabet::command_positions(&before);
        let mut after_positions = ToyAlphabet::command_positions(&after);
        assert_eq!(
            NodeSurvival::Preserved,
            node_survival::<ToyAlphabet>(
                &before,
                &after,
                &before_positions,
                &after_positions,
                &root
            )
        );
        after_positions.reverse();
        assert_eq!(
            NodeSurvival::Preserved,
            node_survival::<ToyAlphabet>(
                &before,
                &after,
                &before_positions,
                &after_positions,
                &root
            )
        );
        let reduced = Toy::zero();
        let one = Toy::succ(reduced.clone());
        let reduced_positions = ToyAlphabet::command_positions(&reduced);
        let one_positions = ToyAlphabet::command_positions(&one);
        assert_eq!(
            NodeSurvival::Replaced,
            node_survival::<ToyAlphabet>(&one, &reduced, &one_positions, &reduced_positions, &left)
        );
        let constant = ToyAlphabet::skolemize(&Toy::var("fresh"));
        assert_eq!(
            NodeSurvival::Replaced,
            node_survival::<ToyAlphabet>(
                &reduced,
                &constant,
                &reduced_positions,
                &ToyAlphabet::command_positions(&constant),
                &root
            )
        );
        assert_eq!(
            NodeSurvival::Replaced,
            node_survival::<ToyAlphabet>(&before, &one, &before_positions, &one_positions, &root)
        );
        let cell = toy_cell(
            Toy::add(Toy::zero(), Toy::var("x")),
            Toy::add(Toy::succ(Toy::zero()), Toy::var("x")),
        );
        let term = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
        assert_eq!(
            ContentSensitivity::Insensitive,
            content_sensitivity::<ToyAlphabet>(&cell, &term, &root, &root, &[])
        );
        assert_eq!(
            ContentSensitivity::Insensitive,
            content_sensitivity::<ToyAlphabet>(
                &cell,
                &term,
                &root,
                &root,
                core::slice::from_ref(&term)
            )
        );
        assert_eq!(
            ContentSensitivity::Sensitive,
            content_sensitivity::<ToyAlphabet>(&cell, &term, &root, &root, &[Toy::zero()])
        );
        assert_eq!(
            ContentSensitivity::Insensitive,
            content_sensitivity::<ToyAlphabet>(&cell, &term, &root, &right, &[
                Toy::zero(),
                Toy::succ(Toy::succ(Toy::zero()))
            ])
        );
        let mut store = CellStore::new();
        let identity = store.insert(toy_cell(Toy::var("x"), Toy::var("x")));
        let footprint = match_footprint(&store, &Toy::zero(), &CellApp {
            cell: identity,
            at: root.clone(),
        })
        .expect("the identity rule fires");
        assert_eq!(
            MatchFootprint::<ToyAlphabet> {
                at: root.clone(),
                written: Vec::new(),
                read: Vec::new(),
                framed: alloc::vec![root]
            },
            footprint
        );
        assert_eq!(
            FootprintIndependence::Independent,
            footprint_independence(&footprint, &footprint)
        );
    }
}
