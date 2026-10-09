//! Instantiation of a circuit rule: the site where the earned identification
//! of a two-redex body's two sequentializations is well-posed.
//!
//! # Why the licence is not asked for at the declaration
//!
//! A circuit rule is a schema. Its body applies rewrite-sorted ports — the
//! binders of its parameter telescope — not cells, so a two-redex body names
//! no pair of cells to put to the shift guard. Asking at the declaration would
//! ask whether every instantiation of the ports commutes, a much stronger
//! question than the one the guard decides. So the declaration's elaboration
//! keeps declining a two-redex body a single whiskered composite, and that
//! decline defers the question rather than refusing it; this module asks it at
//! an application, where each port is instantiated by a stored cell and the
//! pair is two cells at two positions of one term.
//!
//! # What the record supplies, and what the caller supplies
//!
//! The two positions come from the body's own occurrence record
//! ([`redex_occurrences`]): the argument paths the declared output port's
//! unfolding reaches its two redexes at. They are read, never fabricated — a
//! caller naming the positions could name incomparable ones for a nested pair
//! and buy the licence with the argument instead of earning it. The caller
//! supplies what the declaration cannot know: which stored cell each port is
//! instantiated by ([`RewriteBinding`]), the peak the rule is applied to, and
//! the convexity re-check ([`ConvexitySupply`]).
//!
//! The bindings are an environment, a function from port to cell: a port
//! presented twice is refused rather than resolved by a precedence rule, which
//! would make the identification depend on the order two bindings were
//! written in. Neither the bindings nor the peak is matched against the rule's
//! sphere; the instance is exercised instead — both orders fire — so a peak
//! that is not an instance of the body is refused by a step that does not
//! fire rather than identified.
//!
//! # The convexity supply point
//!
//! The shift guard's third conjunct asks that each match image stay convex in
//! the other application's reduct. A store whose left-hand sides are strongly
//! connected over acyclic targets discharges it once for every pair; a store
//! that cannot answers [`ConvexityDischarge::ReCheckRequired`], and the guard
//! refuses rather than assumes. The re-check is a directed reachability sweep
//! over a diagram reading of the term, which this crate does not hold, so it is
//! a parameter: the caller's [`ConvexitySupply`] is asked exactly when the
//! store withholds the discharge and the first two conjuncts have held, and its
//! warrant or refusal travels back verbatim. A discharged store never asks it.
//!
//! # Nothing here decides independence
//!
//! The positions, overlap and discharge conjuncts are the shift guard's
//! ([`derive_shift_equivalence`]), and its refusals are carried verbatim; this
//! module holds no second overlap oracle. A granted witness is replayed
//! ([`ShiftEquivalence::replay`]) before it is handed back, so a composite
//! neither sequentialization reaches is a refusal rather than a recorded
//! identification.
//!
//! [`ConvexityDischarge::ReCheckRequired`]: gandr_theory_cell_complexes::ConvexityDischarge::ReCheckRequired

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::rewrite_at;
use gandr_theory_deep_inference::ShiftEquivalence;
use gandr_theory_deep_inference::ShiftObstruction;
use gandr_theory_deep_inference::derive_shift_equivalence;
use gandr_theory_levitation::CircuitDerivationError;
use gandr_theory_levitation::CircuitRule;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RedexOccurrence;
use gandr_theory_levitation::redex_occurrences;
use quenchant_shape::shape::Maybe;

use crate::boundary::RedexOccurrenceCount;

/// Why a stored cell could not be instantiated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CellInstantiationError
{
    /// The identifier addresses no cell of the supplied store.
    UnknownCell
    {
        /// The stale or foreign identifier.
        cell: CellId,
    },
}

impl fmt::Display for CellInstantiationError
{
    /// Names the identifier that resolved to nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::UnknownCell { cell } => write!(
                f,
                "cell {} is not present in the supplied store",
                usize::from(cell)
            ),
        }
    }
}

impl core::error::Error for CellInstantiationError
{
}

/// Instantiate one stored cell under an alphabet substitution, into the same
/// store.
///
/// The original cell stays in the store, and the instantiated one is inserted
/// through [`CellStore::insert`], so structural deduplication stays the only
/// identity rule and the returned identifier is valid for the store the
/// replay machinery already reads.
///
/// # Specification
/// - requires: `subst` is the substitution the instantiation site induces.
/// - ensures: the returned identifier addresses a cell whose faces are exactly
///   the source's faces under `subst`, with the source's orientation and
///   provenance; an equal cell reuses its existing identifier.
/// - fails: [`CellInstantiationError::UnknownCell`] when `cell` is not in
///   `store`, which is then unchanged.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the exact substituted faces, identity reuse under the
///   empty substitution, preserved orientation and provenance, and the typed
///   unknown-identifier failure separate the observable branches.
/// - witness: `instantiate::tests::instantiating_a_cell_preserves_store_identity`
/// - witness: `instantiate::tests::instantiating_an_unknown_cell_returns_typed_error`
#[inline]
pub fn instantiate_cell<A>(
    store: &mut CellStore<A>,
    cell: CellId,
    subst: &A::Subst,
) -> Result<CellId, CellInstantiationError>
where
    A: CellAlphabet,
{
    let Maybe::Present(source) = store.get(cell)
    else {
        return Err(CellInstantiationError::UnknownCell { cell });
    };
    let instantiated = Cell::new(
        A::apply_subst(subst, source.lhs()),
        A::apply_subst(subst, source.rhs()),
        source.orient(),
        source.provenance(),
    );
    Ok(store.insert(instantiated))
}

/// One entry of a circuit rule's instantiation: the stored cell a
/// rewrite-sorted port is applied at.
///
/// The port is named the way the body names it, so the binding and the
/// occurrence record meet on one name. Two occurrences of one port are the
/// ordinary reconvergent case and resolve through that port's single binding.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RewriteBinding
{
    /// The rewrite-sorted port being instantiated.
    pub port: Name,
    /// The stored cell it is instantiated by.
    pub cell: CellId,
}

impl RewriteBinding
{
    /// The binding of `port` to `cell`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        port: N,
        cell: CellId,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            port: port.into(),
            cell,
        }
    }
}

/// The per-pair convexity re-check a store that withholds its discharge is
/// owed: the supply point a caller fills.
///
/// The re-check decides whether each application's match image is still
/// convex in the other's reduct, a directed reachability sweep over a diagram
/// reading of the peak. That reading lives above this crate, so the sweep is
/// supplied rather than built here, and its evidence is the supplier's own
/// type in both directions.
pub trait ConvexitySupply<A>
where
    A: CellAlphabet,
{
    /// The evidence that both match images stay convex.
    type Warrant;
    /// The evidence that one does not: a directed path leaving an image and
    /// returning, or why the sweep could not be run.
    type Refusal;

    /// Re-check the convexity conjunct for `first` and `second` in `peak`.
    ///
    /// # Specification
    /// - requires: an implementor answers the conjunct itself — the warrant
    ///   only when neither application's reduct makes the other's match image
    ///   non-convex — and refuses whatever it cannot decide.
    /// - ensures: called only for a pair whose cells resolve in `store`, whose
    ///   positions are incomparable, and whose cells have no overlap, on a
    ///   store whose discharge is withheld.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ConvexitySupply::Refusal`] when the conjunct does not hold or cannot
    /// be decided.
    fn recheck(
        &self,
        store: &CellStore<A>,
        peak: &A::Cmd,
        first: &CellApp<A>,
        second: &CellApp<A>,
    ) -> Result<Self::Warrant, Self::Refusal>;
}

/// How an earned identification's convexity conjunct was met.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ConvexityGrant<W>
{
    /// The store's own discharge covered it; the supply point was not asked.
    Discharged,
    /// The store withheld its discharge, and the supply point's re-check
    /// granted the pair with this warrant.
    Rechecked(W),
}

/// The earned identification of an instantiated two-redex circuit rule's two
/// sequentializations.
///
/// Holding one is the record of which guard granted the identification, at
/// which two applications, under which convexity grant, and that the composite
/// replayed under both orders before the record was handed back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CircuitShift<A, W>
where
    A: CellAlphabet,
{
    /// The witness the pair earned, spanning the peak and the composite; its
    /// own convexity field is the store's discharge.
    pub witness: ShiftEquivalence<A>,
    /// How the convexity conjunct was met.
    pub convexity: ConvexityGrant<W>,
}

/// Why an instantiated circuit rule earns no identification of its two
/// sequentializations.
///
/// The first four variants say the instantiation is ill-formed, so there is no
/// pair to ask about; the last three are about the pair: the guard's own
/// refusal, the supply point's refusal, and a witness whose composite did not
/// re-execute.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitShiftObstruction<A, R>
where
    A: CellAlphabet,
{
    /// The instantiation binds one port twice, so it is not a function from
    /// port to cell.
    DuplicateBinding
    {
        /// The earliest port whose binding repeats, in presentation order.
        port: Name,
    },
    /// The body's wiring does not unfold, so there is no occurrence record.
    Wiring(CircuitDerivationError),
    /// The body does not hold exactly two redex occurrences: none or one is a
    /// rule whose composite the declaration's elaboration already builds, and
    /// three or more is a wider composite nothing here decomposes.
    NotTwoOccurrences
    {
        /// How many occurrences the body unfolds to.
        occurrences: RedexOccurrenceCount,
    },
    /// A redex applies a rewrite the instantiation binds no cell for.
    UnboundRewrite
    {
        /// The rewrite the body applies and the instantiation leaves unbound.
        rewrite: Name,
    },
    /// The shift guard refused the pair, with its own obstruction: an
    /// unresolvable cell, comparable positions, a genuine overlap, a withheld
    /// discharge it could not hand on, a step that does not fire, or two orders
    /// reaching different terms.
    Refused(Box<ShiftObstruction<A>>),
    /// The store withheld its discharge and the supply point's re-check
    /// refused the pair, with its own evidence.
    NotConvex(R),
    /// The guard granted the witness and its composite did not replay.
    CompositeDoesNotReplay
    {
        /// The unconfirmed witness.
        witness: Box<ShiftEquivalence<A>>,
    },
}

/// Instantiate a two-redex circuit rule at `peak` and earn, or refuse, the
/// identification of its two sequentializations.
///
/// # Specification
/// - ensures: success exactly when `bindings` binds each port at most once, the
///   body unfolds to two redex occurrences, both their rewrites are bound, the
///   pair at the record's two positions clears the guard's positions and
///   overlap conjuncts, the convexity conjunct is met — by the store's
///   discharge, or else by `convexity`'s re-check — both sequentializations
///   fire from `peak` to one composite, and that composite replays under both
///   orders.
/// - ensures: the witness's applications carry the record's positions, in the
///   record's left-to-right order, and the cells their ports are bound to; two
///   occurrences of one port carry its one cell at two positions.
/// - ensures: `convexity` is asked only when the store withholds its discharge
///   and the first two conjuncts hold; its warrant is returned as
///   [`ConvexityGrant::Rechecked`], and otherwise the grant is
///   [`ConvexityGrant::Discharged`].
/// - provides: the per-pair licence a two-redex circuit rule's horizontal
///   composite rests on, earned where the rule is applied.
/// - fails: [`CircuitShiftObstruction::DuplicateBinding`],
///   [`CircuitShiftObstruction::Wiring`],
///   [`CircuitShiftObstruction::NotTwoOccurrences`],
///   [`CircuitShiftObstruction::UnboundRewrite`],
///   [`CircuitShiftObstruction::Refused`],
///   [`CircuitShiftObstruction::NotConvex`] and
///   [`CircuitShiftObstruction::CompositeDoesNotReplay`], as each variant
///   states.
/// - panics: none.
/// - intension: decided in this order — the environment, the wiring, the
///   occurrence count, the bindings the record asks for, the guard's positions
///   and overlap conjuncts, convexity, the two sequentializations, the replay —
///   so an instantiation failing several is refused by the earliest.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the shape declines are separated by a port bound twice, a
///   single-redex body, a missing binding and a cyclic body; the pair's
///   outcomes by the `cong2` instantiation that earns and replays, an
///   overlapping instantiation refused by the guard, a sequential body refused
///   its positions, and a peak with no redex at the record's positions refused
///   by the instance check; the environment is kept off the body by a
///   reconvergent block; the supply point by a withheld store whose re-check
///   grants, one whose re-check refuses, a withheld store whose pair fails
///   positions before the supply point is asked, and a discharged store whose
///   refusing supply point is never asked.
/// - witness: `tests::circuit_instantiation::an_instantiated_cong2_rule_earns_its_shift_witness`
/// - witness: `tests::circuit_instantiation::the_instantiated_applications_carry_the_records_positions`
/// - witness: `tests::circuit_instantiation::a_genuinely_overlapping_instantiation_is_refused_at_the_application_site`
/// - witness: `tests::circuit_instantiation::a_sequential_two_redex_body_is_refused_comparable_positions`
/// - witness: `tests::circuit_instantiation::a_reconvergent_body_resolves_both_occurrences_through_one_binding`
/// - witness: `tests::convexity_supply::a_withheld_discharge_is_rechecked_by_the_supply_point`
/// - witness: `tests::convexity_supply::a_refused_recheck_refuses_the_instantiation_with_its_evidence`
/// - witness: `tests::convexity_supply::the_supply_point_is_asked_only_after_the_positions_and_overlap_conjuncts`
/// - witness: `instantiate::tests::a_single_redex_rule_has_no_pair_to_identify`
/// - witness: `instantiate::tests::an_unbound_rewrite_port_declines_the_instantiation`
/// - witness: `instantiate::tests::a_port_bound_twice_is_not_a_functional_environment`
/// - witness: `instantiate::tests::a_cyclic_body_declines_before_any_pair_is_read`
/// - witness: `instantiate::tests::a_peak_carrying_no_redex_at_the_records_positions_is_refused`
#[inline]
pub fn instantiate_two_redex_rule<A, C>(
    store: &CellStore<A>,
    rule: &CircuitRule,
    bindings: &[RewriteBinding],
    peak: &A::Cmd,
    convexity: &C,
) -> Result<CircuitShift<A, C::Warrant>, CircuitShiftObstruction<A, C::Refusal>>
where
    A: CellAlphabet,
    C: ConvexitySupply<A>,
{
    functional_environment(bindings)?;
    let occurrences = redex_occurrences(&rule.body).map_err(CircuitShiftObstruction::Wiring)?;
    let [ref first, ref second] = *occurrences
    else {
        return Err(CircuitShiftObstruction::NotTwoOccurrences {
            occurrences: RedexOccurrenceCount::from(occurrences.len()),
        });
    };
    let first = application(first, bindings)?;
    let second = application(second, bindings)?;
    let (witness, grant) = match derive_shift_equivalence(store, peak, &first, &second) {
        | Ok(witness) => (witness, ConvexityGrant::Discharged),
        // The guard decides its conjuncts in order, so a withheld discharge
        // means the cells resolved, the positions are incomparable and the
        // cells do not overlap: exactly the pair the supply point is owed.
        | Err(ShiftObstruction::ConvexityNotDischarged) => {
            let warrant = convexity
                .recheck(store, peak, &first, &second)
                .map_err(CircuitShiftObstruction::NotConvex)?;
            let joins_at = exercise(store, peak, &first, &second)
                .map_err(|obstruction| CircuitShiftObstruction::Refused(Box::new(obstruction)))?;
            let witness = ShiftEquivalence {
                peak: peak.clone(),
                first,
                second,
                joins_at,
                convexity: A::convexity_discharge(store),
            };
            (witness, ConvexityGrant::Rechecked(warrant))
        },
        | Err(obstruction) => return Err(CircuitShiftObstruction::Refused(Box::new(obstruction))),
    };
    if !bool::from(witness.replay(store)) {
        return Err(CircuitShiftObstruction::CompositeDoesNotReplay {
            witness: Box::new(witness),
        });
    }
    Ok(CircuitShift {
        witness,
        convexity: grant,
    })
}

/// Check that the instantiation is a function from port to cell.
///
/// A port presented twice is refused whether or not the two entries name one
/// cell: two entries for one port say nothing about which the caller meant.
///
/// # Specification
/// - ensures: success exactly when no two entries of `bindings` name one port.
/// - fails: [`CircuitShiftObstruction::DuplicateBinding`] naming the earliest
///   port whose binding repeats.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn functional_environment<A, R>(
    bindings: &[RewriteBinding]
) -> Result<(), CircuitShiftObstruction<A, R>>
where
    A: CellAlphabet,
{
    for (index, binding) in bindings.iter().enumerate() {
        if bindings
            .iter()
            .take(index)
            .any(|earlier| earlier.port == binding.port)
        {
            return Err(CircuitShiftObstruction::DuplicateBinding {
                port: binding.port.clone(),
            });
        }
    }
    Ok(())
}

/// The application one recorded occurrence instantiates to: the record's
/// position, and the cell the occurrence's rewrite is bound to.
///
/// # Specification
/// - requires: `bindings` is a function from port to cell.
/// - ensures: an application at the alphabet's position for the occurrence's
///   argument path, carrying the cell its rewrite is bound to.
/// - fails: [`CircuitShiftObstruction::UnboundRewrite`] when no binding names
///   the rewrite.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn application<A, R>(
    occurrence: &RedexOccurrence,
    bindings: &[RewriteBinding],
) -> Result<CellApp<A>, CircuitShiftObstruction<A, R>>
where
    A: CellAlphabet,
{
    let Some(binding) = bindings
        .iter()
        .find(|binding| binding.port == occurrence.rewrite)
    else {
        return Err(CircuitShiftObstruction::UnboundRewrite {
            rewrite: occurrence.rewrite.clone(),
        });
    };
    let path: Vec<PositionStep> = occurrence
        .position
        .iter()
        .map(|&index| PositionStep::from(usize::from(index)))
        .collect();
    Ok(CellApp {
        cell: binding.cell,
        at: A::position_at_path(&path),
    })
}

/// Fire both orders of a re-checked pair from `peak` and return the term both
/// reach.
///
/// # Specification
/// - ensures: the composite, when `first` then `second` and `second` then
///   `first` each fire at their recorded positions and reach one term.
/// - fails: [`ShiftObstruction::UnknownCell`] for a stale identifier,
///   [`ShiftObstruction::StepDoesNotFire`] for a position carrying no redex for
///   its cell, and [`ShiftObstruction::SequentializationsDiffer`] when the two
///   orders reach different terms.
/// - panics: none.
/// - intension: the guard's own instance check, run after the supply point
///   granted the conjunct the guard could not.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a re-checked `cong2` pair reaches its composite through
///   both orders.
/// - witness: `tests::convexity_supply::a_withheld_discharge_is_rechecked_by_the_supply_point`
fn exercise<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    first: &CellApp<A>,
    second: &CellApp<A>,
) -> Result<A::Cmd, ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let after_first = fire(store, peak, first)?;
    let first_then_second = fire(store, &after_first, second)?;
    let after_second = fire(store, peak, second)?;
    let second_then_first = fire(store, &after_second, first)?;
    if first_then_second != second_then_first {
        return Err(ShiftObstruction::SequentializationsDiffer {
            first_then_second: Box::new(first_then_second),
            second_then_first: Box::new(second_then_first),
        });
    }
    Ok(first_then_second)
}

/// Fire one recorded application.
///
/// # Specification
/// - ensures: the term after `step`'s cell fires at its recorded position.
/// - fails: [`ShiftObstruction::UnknownCell`] for a stale identifier and
///   [`ShiftObstruction::StepDoesNotFire`] when no redex is there.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn fire<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    step: &CellApp<A>,
) -> Result<A::Cmd, ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let Maybe::Present(cell) = store.get(step.cell)
    else {
        return Err(ShiftObstruction::UnknownCell { cell: step.cell });
    };
    match rewrite_at(cell, term, &step.at) {
        | Maybe::Present(result) => Ok(result),
        | Maybe::Absent(_) => Err(ShiftObstruction::StepDoesNotFire {
            step: Box::new(step.clone()),
        }),
    }
}

#[cfg(test)]
mod tests
{
    use core::convert::Infallible;

    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::MetaVar;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::SequentAlphabet;
    use gandr_theory_cell_complexes::Subst;
    use gandr_theory_levitation::CircuitBody;
    use gandr_theory_levitation::CircuitFrame;
    use gandr_theory_levitation::CircuitNode;
    use gandr_theory_levitation::CircuitRedex;
    use gandr_theory_levitation::FrameHead;
    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::RuleFace;
    use gandr_theory_levitation::SurfaceSpan;
    use gandr_theory_levitation::derive_boundaries;

    use super::*;

    /// A supply point that refuses every pair, so a result other than
    /// [`CircuitShiftObstruction::NotConvex`] shows it was never asked.
    struct RefusingSupply;

    /// The refusal [`RefusingSupply`] answers with.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Asked;

    impl<A> ConvexitySupply<A> for RefusingSupply
    where
        A: CellAlphabet,
    {
        type Refusal = Asked;
        type Warrant = Infallible;

        /// Refuses.
        ///
        /// # Specification
        /// trivial.
        fn recheck(
            &self,
            _store: &CellStore<A>,
            _peak: &A::Cmd,
            _first: &CellApp<A>,
            _second: &CellApp<A>,
        ) -> Result<Infallible, Asked>
        {
            Err(Asked)
        }
    }

    #[test]
    fn instantiating_a_cell_preserves_store_identity()
    {
        let mut store: CellStore<SequentAlphabet> = CellStore::new();
        let source_id = store.insert(sequent_cell(ProdPat::meta("x"), ProdPat::meta("x")));
        let identity_id = instantiate_cell(&mut store, source_id, &Subst::new())
            .expect("the source identifier addresses a stored cell");
        assert_eq!(
            source_id, identity_id,
            "the empty substitution reuses the source's identifier"
        );
        let mut substitution = Subst::new();
        substitution
            .bind_prod(MetaVar::producer("x"), ProdPat::ctor("Zero", []))
            .expect("a fresh producer binding");
        let instantiated_id = instantiate_cell(&mut store, source_id, &substitution)
            .expect("the induced substitution instantiates the source");
        assert_ne!(
            source_id, instantiated_id,
            "a changed cell is a new identifier"
        );
        let Maybe::Present(instantiated) = store.get(instantiated_id)
        else {
            panic!("the instantiated identifier addresses the inserted cell");
        };
        assert_eq!(
            &sequent_cell(ProdPat::ctor("Zero", []), ProdPat::ctor("Zero", [])),
            instantiated,
            "both substituted faces are exact, orientation and provenance kept"
        );
        assert!(
            matches!(store.get(source_id), Maybe::Present(source) if source != instantiated),
            "the source remains in the store, distinct from its instance"
        );
    }

    #[test]
    fn instantiating_an_unknown_cell_returns_typed_error()
    {
        let mut store: CellStore<SequentAlphabet> = CellStore::new();
        let missing = CellId::from(usize::MAX);
        assert_eq!(
            Err(CellInstantiationError::UnknownCell { cell: missing }),
            instantiate_cell(&mut store, missing, &Subst::new()),
            "a foreign identifier cannot be instantiated"
        );
    }

    #[test]
    fn a_single_redex_rule_has_no_pair_to_identify()
    {
        // `cong1`: one redex whiskered into one frame, which has a composite of
        // its own, so there is nothing to identify.
        let body = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}"),
                    "x\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y")],
                    "z",
                )),
            ],
            "z",
        );
        let mut store = CellStore::new();
        let ground = store.insert(add_zero_ground());
        assert_eq!(
            Err(CircuitShiftObstruction::NotTwoOccurrences {
                occurrences: RedexOccurrenceCount::from(1_usize),
            }),
            instantiate_two_redex_rule(
                &store,
                &rule_over(body),
                &[RewriteBinding::new("p", ground)],
                &zero_at_top(),
                &RefusingSupply,
            ),
            "the decline reports how many occurrences the body unfolds to"
        );
    }

    #[test]
    fn an_unbound_rewrite_port_declines_the_instantiation()
    {
        // `q` is applied by the body and instantiated by nothing.
        let mut store = CellStore::new();
        let ground = store.insert(add_zero_ground());
        assert_eq!(
            Err(CircuitShiftObstruction::UnboundRewrite {
                rewrite: "q".into(),
            }),
            instantiate_two_redex_rule(
                &store,
                &rule_over(cong2_body()),
                &[RewriteBinding::new("p", ground)],
                &zero_at_top(),
                &RefusingSupply,
            ),
            "the decline names the rewrite the instantiation left unbound"
        );
    }

    #[test]
    fn a_port_bound_twice_is_not_a_functional_environment()
    {
        // `p` is presented twice, at two cells, over the well-formed `cong2`
        // body: the environment is refused before the body is unfolded.
        let mut store = CellStore::new();
        let ground = store.insert(add_zero_ground());
        let other = store.insert(sequent_cell(
            ProdPat::ctor("Zero", []),
            ProdPat::ctor("Zero", []),
        ));
        assert_eq!(
            Err(CircuitShiftObstruction::DuplicateBinding { port: "p".into() }),
            instantiate_two_redex_rule(
                &store,
                &rule_over(cong2_body()),
                &[
                    RewriteBinding::new("p", ground),
                    RewriteBinding::new("q", ground),
                    RewriteBinding::new("p", other),
                ],
                &zero_at_top(),
                &RefusingSupply,
            ),
            "the refusal names the port whose binding repeats"
        );
    }

    #[test]
    fn a_cyclic_body_declines_before_any_pair_is_read()
    {
        let body = CircuitBody::new(
            [
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("f".into()),
                    [FreeTerm::var("b")],
                    "a",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("g".into()),
                    [FreeTerm::var("a")],
                    "b",
                )),
            ],
            "a",
        );
        let rule = CircuitRule::new("wheel", face(FreeTerm::var("a"), FreeTerm::var("a")), body);
        assert_eq!(
            Err(CircuitShiftObstruction::Wiring(
                CircuitDerivationError::CyclicWiring("a".into())
            )),
            instantiate_two_redex_rule(
                &CellStore::<SequentAlphabet>::new(),
                &rule,
                &[],
                &zero_at_top(),
                &RefusingSupply,
            ),
            "the wiring refusal reaches the site unchanged"
        );
    }

    #[test]
    fn a_peak_carrying_no_redex_at_the_records_positions_is_refused()
    {
        // The guard passes — one cell that overlaps nothing, instantiating
        // both ports, at the record's two incomparable positions — and the
        // instance check declines: a sequent command has one command position,
        // so nothing fires at the frame's argument slots. That the refusal is
        // the instance check rather than comparable positions pins the two
        // positions as the record's `[0]` and `[1]` rather than the root twice.
        let mut store = CellStore::new();
        let ground = store.insert(add_zero_ground());
        assert_eq!(
            Err(CircuitShiftObstruction::Refused(Box::new(
                ShiftObstruction::StepDoesNotFire {
                    step: Box::new(CellApp {
                        cell: ground,
                        at: Pos::from_steps([PositionStep::from(0_usize)]),
                    }),
                }
            ))),
            instantiate_two_redex_rule(
                &store,
                &rule_over(cong2_body()),
                &[
                    RewriteBinding::new("p", ground),
                    RewriteBinding::new("q", ground),
                ],
                &CmdPat::cut(
                    Polarity::Positive,
                    ProdPat::ctor("Zero", []),
                    ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
                ),
                &RefusingSupply,
            ),
            "the guard's own obstruction is carried, naming the step and its recorded position"
        );
    }

    /// A positive sequent cell `⟨lhs | ★⟩ ~> ⟨rhs | ★⟩` from a surface rule.
    ///
    /// # Specification
    /// trivial.
    fn sequent_cell(
        lhs: ProdPat,
        rhs: ProdPat,
    ) -> Cell
    {
        Cell::new(
            CmdPat::cut(Polarity::Positive, lhs, ConsPat::top()),
            CmdPat::cut(Polarity::Positive, rhs, ConsPat::top()),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// `⟨Zero | ★⟩`.
    ///
    /// # Specification
    /// trivial.
    fn zero_at_top() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        )
    }

    /// `⟨Zero | add(Zero; ★)⟩ ~> ⟨Zero | ★⟩`: a ground cell whose right-hand
    /// side offers no seam, so it overlaps nothing, not even itself.
    ///
    /// # Specification
    /// trivial.
    fn add_zero_ground() -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
            ),
            zero_at_top(),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// A face over two terms, with no derived metadata and an empty span.
    ///
    /// # Specification
    /// trivial.
    fn face(
        lhs: FreeTerm,
        rhs: FreeTerm,
    ) -> RuleFace
    {
        RuleFace::new(lhs, rhs, Vec::new(), SurfaceSpan::default())
    }

    /// The `cong2` body: two redexes at the two argument positions of one
    /// `add` frame.
    ///
    /// # Specification
    /// trivial.
    fn cong2_body() -> CircuitBody
    {
        CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}"),
                    "x\u{2032}",
                )),
                CircuitNode::Redex(CircuitRedex::new(
                    "q",
                    FreeTerm::var("y"),
                    FreeTerm::var("y\u{2032}"),
                    "y\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y\u{2032}")],
                    "z",
                )),
            ],
            "z",
        )
    }

    /// A rule over `body`, declared at the sphere its wiring derives.
    ///
    /// # Specification
    /// - panics: when the body derives no boundary pair, which is a fixture
    ///   defect.
    fn rule_over(body: CircuitBody) -> CircuitRule
    {
        let derived = derive_boundaries(&body).expect("the fixture bodies derive their boundaries");
        CircuitRule::new("cong2", face(derived.source, derived.target), body)
    }
}
