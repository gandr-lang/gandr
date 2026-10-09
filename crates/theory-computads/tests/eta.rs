//! The η cells a declaration mints, and what makes them safe to mint.
//!
//! - `the_two_routes_out_of_the_eta_redex_agree` is the soundness witness: the
//!   η cell shortcuts a two-step route that already exists, so the critical
//!   pair between them must join. If the law were not a law, the two routes
//!   would land in different normal forms.
//! - `a_codata_eta_cell_joins_the_projection_route_at_its_negative_cut` is the
//!   same witness for a `codata` declaration, whose rule and frame cells cut at
//!   the negative polarity its η cell requires; at any other polarity the
//!   projection route would be stuck where the η route is not.
//! - `the_eta_cell_reaches_a_redex_the_projection_route_cannot` is why the cell
//!   is worth minting: the projection rule needs a producer built by the
//!   constructor, and the η cell quantifies over the producer.
//! - `a_data_eta_cell_does_not_fire_at_a_negative_cut` and
//!   `a_codata_eta_cell_does_not_fire_at_a_positive_cut` drive the
//!   strategy-tied η discipline from a minted cell.
//! - `an_eta_step_replays` pins that a recorded η step re-executes, so the cell
//!   is inside the replay discipline rather than beside it.

use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_coherent_resolutions::Normalization;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::normalize;
use gandr_theory_coherent_resolutions::replay_from_peak;
use gandr_theory_computads::EtaElaboration;
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
fn the_two_routes_out_of_the_eta_redex_agree()
{
    // Both routes out of `⟨MkWrap(Zero) | unwrap(MkWrap⁻(★))⟩` exist: the
    // projection rule strips the constructor and the frame-defining cell puts
    // it back, and the η cell says those two steps cancel. The engine tries
    // cells in insertion order, so where the η cell sits decides the route;
    // both orders are built and both normalized.
    let (projection_first, eta_ids) = wrapper_store(DeclPolarity::Data);
    let eta_first = store_with_eta_first(&projection_first, &eta_ids);
    let redex = eta_redex(Polarity::Positive);
    let by_projection = normal(&projection_first, &redex);
    let by_eta = normal(&eta_first, &redex);
    assert_eq!(
        by_projection.normal, by_eta.normal,
        "the critical pair joins: destructing and rebuilding lands where cancelling does"
    );
    assert!(
        by_eta.path.len() < by_projection.path.len(),
        "the η route is the shorter one, which is what makes the cell worth minting"
    );
    assert!(
        by_eta
            .path
            .iter()
            .any(|step| step.cell == eta_id(&eta_first)),
        "and the short route really is the η step"
    );
}

#[test]
fn a_codata_eta_cell_joins_the_projection_route_at_its_negative_cut()
{
    // The codata redex sits at a negative cut. The projection route there is
    // the rule cell then the frame-defining cell, so it exists only when both
    // cut negative, as the η cell does; the η cell is left out of one store so
    // the projection route is the only one it has.
    let (store, eta_ids) = wrapper_store(DeclPolarity::Codata);
    let without_eta = store_without(&store, &eta_ids);
    let eta_first = store_with_eta_first(&store, &eta_ids);
    let redex = eta_redex(Polarity::Negative);
    let by_projection = normal(&without_eta, &redex);
    let by_eta = normal(&eta_first, &redex);
    assert_eq!(
        2,
        by_projection.path.len(),
        "the projection route fires at the negative cut: the rule cell, then the frame cell"
    );
    assert_eq!(
        CmdPat::cut(
            Polarity::Negative,
            ProdPat::ctor("MkWrap", [ProdPat::ctor("Zero", [])]),
            ConsPat::top()
        ),
        by_projection.normal,
        "and it rebuilds the value at the negative cut it started from"
    );
    assert_eq!(
        by_projection.normal, by_eta.normal,
        "the codata critical pair joins where the η step lands"
    );
    assert!(
        by_eta
            .path
            .iter()
            .any(|step| step.cell == eta_id(&eta_first)),
        "and that route is the η step"
    );
}

#[test]
fn the_eta_cell_reaches_a_redex_the_projection_route_cannot()
{
    // The projection rule matches only a producer built by the constructor;
    // the η cell quantifies over the producer.
    let (store, eta_ids) = wrapper_store(DeclPolarity::Data);
    let without_eta = store_without(&store, &eta_ids);
    let opaque = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Opaque", []),
        ConsPat::op("unwrap", [], ConsPat::frame("MkWrap", ConsPat::top())),
    );
    assert_eq!(
        opaque,
        normal(&without_eta, &opaque).normal,
        "without the η cell the redex is stuck: no rule matches a producer that is not a \
         `MkWrap` application"
    );
    assert_eq!(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Opaque", []),
            ConsPat::top()
        ),
        normal(&store, &opaque).normal,
        "with it, the destructor and the rebuild cancel and the producer is handed on"
    );
}

#[test]
fn a_data_eta_cell_does_not_fire_at_a_negative_cut()
{
    // Data η is a call-by-value law, so the redex at a negative cut is a
    // normal form; nothing else in the data store cuts negative either.
    let (store, _) = wrapper_store(DeclPolarity::Data);
    let redex = eta_redex(Polarity::Negative);
    let outcome = normal(&store, &redex);
    assert_eq!(
        redex, outcome.normal,
        "data η does not fire at a negative cut, so the redex is a normal form"
    );
    assert!(outcome.path.is_empty(), "and no step was taken");
}

#[test]
fn a_codata_eta_cell_does_not_fire_at_a_positive_cut()
{
    // The η cell is inserted first, so wherever it may fire it is the first
    // step taken; the declaration's other cells cut negative too.
    let (elaborated, eta_ids) = wrapper_store(DeclPolarity::Codata);
    let store = store_with_eta_first(&elaborated, &eta_ids);
    let eta = eta_id(&store);
    assert!(
        matches!(
            normal(&store, &eta_redex(Polarity::Negative)).path.first(),
            Some(step) if step.cell == eta
        ),
        "codata η fires at the negative cut it declares"
    );
    assert!(
        normal(&store, &eta_redex(Polarity::Positive))
            .path
            .iter()
            .all(|step| step.cell != eta),
        "and never at a positive one, however well its left-hand side matches"
    );
}

#[test]
fn an_eta_step_replays()
{
    // A recorded η step re-executes rather than being trusted.
    let (projection_first, eta_ids) = wrapper_store(DeclPolarity::Data);
    let store = store_with_eta_first(&projection_first, &eta_ids);
    let redex = eta_redex(Polarity::Positive);
    let outcome = normal(&store, &redex);
    assert!(
        outcome.path.iter().any(|step| step.cell == eta_id(&store)),
        "the normalization took the η step"
    );
    assert!(
        bool::from(replay_from_peak(
            &store,
            &redex,
            &outcome.normal,
            &outcome.path,
            &outcome.path
        )),
        "a path recording the η step replays over the store"
    );
}

/// Normalize `term` under `store`, generously enough that exhaustion means a
/// loop rather than a short ceiling.
///
/// # Specification
/// - panics: when the budget runs out, which is a fixture defect.
fn normal(
    store: &CellStore,
    term: &CmdPat,
) -> Normalization
{
    let outcome = normalize(store, term, NormalizationBudget::from(64_usize));
    assert!(
        !bool::from(outcome.exhausted),
        "the normalization reaches a normal form rather than looping"
    );
    outcome
}

/// The η redex `⟨MkWrap(Zero) |ε unwrap(MkWrap⁻(★))⟩`: the destructor applied
/// and its result rebuilt.
///
/// # Specification
/// trivial.
fn eta_redex(polarity: Polarity) -> CmdPat
{
    CmdPat::cut(
        polarity,
        ProdPat::ctor("MkWrap", [ProdPat::ctor("Zero", [])]),
        ConsPat::op("unwrap", [], ConsPat::frame("MkWrap", ConsPat::top())),
    )
}

/// A copy of `store` whose η cells come first, so insertion-order cell choice
/// takes the η route.
///
/// # Specification
/// trivial.
fn store_with_eta_first(
    store: &CellStore,
    eta_ids: &[CellId],
) -> CellStore
{
    let mut out = CellStore::new();
    for &id in eta_ids {
        if let Maybe::Present(cell) = store.get(id) {
            out.insert(cell.clone());
        }
    }
    for (id, cell) in store.iter() {
        if !eta_ids.contains(&id) {
            out.insert(cell.clone());
        }
    }
    out
}

/// A copy of `store` without the cells at `dropped`.
///
/// # Specification
/// trivial.
fn store_without(
    store: &CellStore,
    dropped: &[CellId],
) -> CellStore
{
    let mut out = CellStore::new();
    for (id, cell) in store.iter() {
        if !dropped.contains(&id) {
            out.insert(cell.clone());
        }
    }
    out
}

/// The identifier of the store's η cell.
///
/// # Specification
/// - panics: when the store holds none, which is a fixture defect.
fn eta_id(store: &CellStore) -> CellId
{
    store
        .iter()
        .find(|&(_, cell)| matches!(cell.provenance(), CellProvenance::Eta(_)))
        .map(|(id, _)| id)
        .expect("the store holds an η cell")
}

/// The elaborated store of a single-constructor `Wrap` declaration whose
/// `unwrap` operation carries the inverse face, with the η cells it minted.
///
/// # Specification
/// - panics: when the declaration does not elaborate whole or mints no η cell,
///   which is a fixture defect.
fn wrapper_store(polarity: DeclPolarity) -> (CellStore, Vec<CellId>)
{
    let desc: SignDesc<Ungraded> = SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Wrap"),
        Vec::new(),
        [CtorDesc::new(
            "MkWrap",
            Code::var("Nat"),
            "Wrap",
            Attrs::empty(),
        )],
        [OperDesc::new(
            "unwrap",
            BridgeArity::single_output([SortRef::new("w", "Wrap")], SortRef::new("out", "Nat")),
            Attrs::empty(),
        )],
        [face(
            FreeTerm::op("unwrap", [FreeTerm::ctor("MkWrap", [FreeTerm::var("x")])]),
            FreeTerm::var("x"),
        )],
        polarity,
        Attrs::empty(),
    );
    let elaborated = elaborate_data_desc(&desc);
    assert!(
        elaborated.declined_faces.is_empty() && elaborated.declined_opers.is_empty(),
        "the wrapper declaration elaborates whole"
    );
    let EtaElaboration::Minted(eta) = elaborated.eta
    else {
        panic!(
            "the wrapper declaration mints an η cell: {:?}",
            elaborated.eta
        );
    };
    (elaborated.store, eta)
}
