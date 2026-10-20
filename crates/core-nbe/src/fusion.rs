//! Cong fusion: a chain of congs whose functions compose to the identity
//! returns the path it starts from.
//!
//! `cong(f, p)` is derived: the transport `tr(y. Path(B, s, ⟨f y⟩), p,
//! here(s))` of reflexivity at the start `s` along `p : Path(A, a, b)`, in
//! the family whose right endpoint moves by `f`. Along a stuck path it is
//! stuck, and so is a cong of it: `run q <- cong(f, p); cong(g, q)` stands as
//! the transport along `p` with the bind into `q. tr(y. Path(C, t, ⟨g y⟩), q,
//! here(t))` on its spine. Two laws of the path type relate such a chain to
//! its path:
//!
//! - **functoriality**: `cong(g, cong(f, p)) = cong(g ∘ f, p)`, transport along
//!   `cong(f, p)` being transport along `p` in the family pulled back along
//!   `f`;
//! - **identity**: `cong(id, p) = p`, the singleton row of transport — `tr(y.
//!   Path(D, l, y), p, here(l))` returns `p` — at a family whose right endpoint
//!   is its binder once it computes.
//!
//! [`fused`] decides the composite of the two that conversion needs: a chain
//! whose functions compose to the identity returns its path.
//!
//! # The reading
//!
//! A **link** is a transport of a reflexivity in a family `y. Path(D, l, r)`
//! whose carrier `D` and left endpoint `l` never read `y`. A **cong chain** is
//! a link stuck on a path `p`, followed on the spine by binds whose
//! continuations are each one link along the path the bind binds, its family
//! reading no other index the bind opened. The chain **fuses** when its
//! composite right endpoint `rₙ[y := … r₁[y := y]]`, read at a variable `y` no
//! side of the goal mentions, is `y` itself: each `rᵢ` evaluated through every
//! manifest definition ([`Definitions::manifest`]), and the last taken to its
//! presented normal form ([`normal_form`]). A fused chain converts with
//! `return p`. The words over a looped point are a presented type too, their
//! cancellations its rules, so the same reading fuses a chain of conses one
//! stratum up: `loop ∷ back(loop) ∷ y` is `y` in normal form.
//!
//! The conversion machine reads each side of a pair this way before it plans
//! the pair — a computation, or a returned endpoint by the computation it
//! holds — a forced step no decision of the trace records; the kernel's replay
//! reads the same chain after weak head reduction by its own evaluator, a
//! returned endpoint opened to its computation first, as a forced step too.
//!
//! # Decisions
//!
//! - **Fusion reads to the identity, not to a composite.** A chain fuses only
//!   when its composite function is the identity, and then to its path; a chain
//!   whose functions compose to anything else stays the chain. Alternatives:
//!   fusing any two links into one transport in the composite family, which
//!   mints a family at conversion time — a closure over a composite no term
//!   spells — and needs a kernel rule rebuilding the same family by
//!   substitution, for no obligation a corpus row states yet; and uniqueness of
//!   identity proofs at a path type whose carrier has no cells, which decides
//!   more pairs but is false of a presented type the moment it carries a
//!   2-cell, the path stratum's next step. Reversal: a rule whose two sides
//!   read as chains with different composites — `cong(f, p)` against `cong(g,
//!   p)` for `f` and `g` that agree up to the rules — makes the reading compare
//!   composites rather than test one against the identity.
//! - **The functions are read through their definitions in every stance.** A
//!   respect obligation is decided δ-free, and a chain whose composite is the
//!   identity only once `looped` and `unlooped` unfold could never fuse there.
//!   The reading evaluates the composite under [`Definitions::manifest`]
//!   whatever the run's stance, the transparency scope still sealing what it
//!   seals, as a returned leaf under a presented constructor is read.
//!   Alternatives: a recorded `Unfold` per function, which needs a trace
//!   position under a transport's family and gives a δ-free run nothing to
//!   record into. Reversal: a function whose reading would need a search takes
//!   the recorded route.
//! - **One link per continuation.** A continuation that binds a chain of its
//!   own keeps the chain stuck; the reassociated continuations a conversion
//!   compares run one link and bind the next, which is the shape a respect
//!   obligation reaches. Reversal: a corpus row whose chain nests its links
//!   inside one continuation.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::RewriteFuel;

use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::closure::CompBody;
use crate::closure::Environment;
use crate::closure::ValueBody;
use crate::conv::ConversionFault;
use crate::domain::BinderLevel;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::eval_value_within;
use crate::free::CoreTerm;
use crate::free::FreeFault;
use crate::free::FreeIndices;
use crate::free::Membership;
use crate::presented::NormalForm;
use crate::presented::normal_form;

/// What reading a computation as a cong chain gave.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fusion
{
    /// A cong chain whose composite function reads as the identity: the
    /// computation returns this path.
    Fused(DomainValueId),
    /// No cong chain, or one whose composite reads as something else.
    Kept,
    /// The reading ran out of budget first.
    Exhausted,
}

/// One link of a chain: its family's right endpoint, read under the family's
/// binder, and the environment the endpoint's other indices read.
struct Link
{
    /// The family's right endpoint.
    right: ValueId,
    /// What the endpoint's indices past the family's binder stand for.
    environment: Environment,
}

/// What reading a family as a link's gave.
enum Family
{
    /// The family is a path type whose carrier and left endpoint never read
    /// its binder, and which reads none of the indices the continuation
    /// opened: its right endpoint.
    Link(ValueId),
    /// Any other family.
    Other,
}

/// Read `computation` as a cong chain and, when its functions compose to the
/// identity, as the path it starts from.
///
/// # Specification
/// - requires: `computation` lives in `domain`, its closures over `core`;
///   `fresh` is a binder level no side of the goal mentions.
/// - ensures: [`Fusion::Fused`] with a value standing for `p` exactly when
///   `computation` is a neutral whose spine is a path transport of a
///   reflexivity stuck on `p`, in a family `y. Path(D, l, r₁)` with `D` and `l`
///   closed over `y`, followed by binds each of whose continuations is one such
///   transport along the index the bind opens, its family reading no other
///   index the continuation opened — and the composite `rₙ[y := … r₁[y := y]]`,
///   evaluated at a rigid variable at `fresh` under [`Definitions::manifest`]
///   and taken to its presented normal form, is that variable with an empty
///   spine; [`Fusion::Exhausted`] when the reading ran out of `fuel` first;
///   [`Fusion::Kept`] otherwise. Each evaluation step and each node the normal
///   form compared or copied costs one unit of `fuel`.
/// - provides: cong fusion to the identity, the forced step conversion takes
///   before it plans a pair.
/// - fails: [`ConversionFault::Domain`] for a node or closure the arena does
///   not hold; [`ConversionFault::Evaluation`] for a reading the evaluator
///   refuses otherwise than on fuel, or a family naming no core node.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loops over the spine's continuations and over the
///   chain's links, not recursion; each evaluation is bounded by `fuel`.
/// - measure: the continuations, then the links, still to read.
///
/// # Adequacy
/// - hypothesis: L3 — over the presented circle, `run q <- cong(unlooped, p);
///   cong(looped, q)` against `return p` converts under a rigid run and the
///   kernel derives the same, `run q <- cong(looped, p); cong(looped, q)` stays
///   apart from it, and over a free circle the identity chain stays apart too.
/// - witness: `fusion::tests::a_cong_chain_composing_to_the_identity_is_its_path`
/// - witness: `fusion::tests::a_chain_fuses_only_through_links_whose_image_is_the_point`
#[spec(captures: before = u64::from(*fuel), ensures: |ret| u64::from(*fuel) <= before
    && match ret {
        Ok(Fusion::Fused(path)) => domain.value(path).is_some(),
        Ok(Fusion::Exhausted) => u64::from(*fuel) == 0,
        Ok(Fusion::Kept) | Err(_) => true,
    })]
pub fn fused(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    (computation, fresh): (DomainCompId, BinderLevel),
    fuel: &mut RewriteFuel,
) -> Result<Fusion, ConversionFault>
{
    let dangling = ConversionFault::Domain(DomainFault::Dangling);
    let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(computation)
    else {
        return Ok(Fusion::Kept);
    };
    let held = domain.neutral(neutral).ok_or(dangling)?;
    let spine = held.spine();
    let binds = spine
        .iter()
        .rev()
        .take_while(|elimination| matches!(elimination, Elimination::Bind(_)))
        .count();
    let Some(at) = spine
        .len()
        .checked_sub(binds)
        .and_then(|end| end.checked_sub(1_usize))
    else {
        return Ok(Fusion::Kept);
    };
    let Some(&Elimination::PathTransport { motive, value }) = spine.get(at)
    else {
        return Ok(Fusion::Kept);
    };
    if !matches!(domain.value(value), Some(DomainValue::Here { .. })) {
        return Ok(Fusion::Kept);
    }
    let head = held.head();
    let unfolding = held.unfolding();
    let prefix = spine.get(.. at).ok_or(dangling)?.to_vec();
    let continuations: Vec<_> = spine
        .get(at.saturating_add(1_usize) ..)
        .ok_or(dangling)?
        .iter()
        .filter_map(|elimination| match *elimination {
            Elimination::Bind(continuation) => Some(continuation),
            Elimination::DataCase(_)
            | Elimination::Split(_)
            | Elimination::Projection(_)
            | Elimination::Transport(_)
            | Elimination::ProductTransport(_)
            | Elimination::PathTransport { .. }
            | Elimination::Ride { .. }
            | Elimination::TelescopeTransport { .. }
            | Elimination::Apply(_)
            | Elimination::Force
            | Elimination::Case(_)
            | Elimination::ListFold { .. }
            | Elimination::ListCase { .. }
            | Elimination::StaticApply(_)
            | Elimination::Fixpoint { .. } => None,
        })
        .collect();
    let point = variable(domain, fresh)?;
    let closure = domain.value_closure(motive).ok_or(dangling)?;
    let ValueBody::ValueType(family) = closure.body()
    else {
        return Ok(Fusion::Kept);
    };
    let Family::Link(right) = link(core, family, Binders::NONE)?
    else {
        return Ok(Fusion::Kept);
    };
    let mut links = Vec::from([Link {
        right,
        environment: closure.environment().clone(),
    }]);
    for continuation in continuations {
        let closure = domain.comp_closure(continuation).ok_or(dangling)?;
        let CompBody::Source(body) = closure.body()
        else {
            return Ok(Fusion::Kept);
        };
        let Some(&Computation::PathTransport {
            motive,
            path,
            value,
        }) = core.computation(body)
        else {
            return Ok(Fusion::Kept);
        };
        let along = matches!(
            core.value(path),
            Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == DeBruijnIndex::from(0_u32)
        );
        if !along || !matches!(core.value(value), Some(&Value::Here(_))) {
            return Ok(Fusion::Kept);
        }
        let Family::Link(right) = link(core, motive, Binders::ONE)?
        else {
            return Ok(Fusion::Kept);
        };
        let mut environment = closure.environment().clone();
        environment.extend(Zone::Intuitionistic, point);
        links.push(Link { right, environment });
    }
    let manifest = definitions.manifest();
    let mut image = point;
    for Link {
        right,
        mut environment,
    } in links
    {
        environment.extend(Zone::Intuitionistic, image);
        let slice = Fuel::from(u32::try_from(u64::from(*fuel)).unwrap_or(u32::MAX));
        let (read, left) =
            match eval_value_within(core, domain, manifest, slice, right, environment) {
                Ok(ran) => ran,
                Err(EvalFault::OutOfFuel) => {
                    *fuel = RewriteFuel::from(0_u64);
                    return Ok(Fusion::Exhausted);
                },
                Err(fault) => return Err(ConversionFault::Evaluation(fault)),
            };
        let spent = u32::from(slice).saturating_sub(u32::from(left));
        *fuel = RewriteFuel::from(u64::from(*fuel).saturating_sub(u64::from(spent)));
        image = read;
    }
    let image = match normal_form(core, domain, manifest, image, fuel)? {
        NormalForm::Kept => image,
        NormalForm::Rewritten(normal) => normal,
        NormalForm::Exhausted => return Ok(Fusion::Exhausted),
    };
    let returned_point = match domain.value(image) {
        Some(&DomainValue::Neutral { neutral, .. }) => {
            let read = domain.neutral(neutral).ok_or(dangling)?;
            read.spine().is_empty()
                && read.head()
                    == NeutralHead::Variable {
                        zone: Zone::Intuitionistic,
                        level: fresh,
                    }
        },
        Some(_) => false,
        None => return Err(dangling),
    };
    if !returned_point {
        return Ok(Fusion::Kept);
    }
    let base = domain
        .neutral_node(head, prefix, unfolding)
        .map_err(ConversionFault::Domain)?;
    let path = domain
        .value_neutral(base, TermFace::Reduced)
        .map_err(ConversionFault::Domain)?;
    Ok(Fusion::Fused(path))
}

/// A rigid intuitionistic variable at `level`, with an empty spine.
///
/// # Specification
/// trivial.
fn variable(
    domain: &mut DomainArena,
    level: BinderLevel,
) -> Result<DomainValueId, ConversionFault>
{
    let head = NeutralHead::Variable {
        zone: Zone::Intuitionistic,
        level,
    };
    let neutral = domain
        .neutral_node(head, Vec::new(), Unfolding::Rigid)
        .map_err(ConversionFault::Domain)?;
    domain
        .value_neutral(neutral, TermFace::Reduced)
        .map_err(ConversionFault::Domain)
}

/// Read `family`, a value type under one binder, as a link's family.
///
/// # Specification
/// - requires: `family` is a transport's family, read under its one binder;
///   `opened` counts the indices past that binder its continuation opened.
/// - ensures: [`Family::Link`] with its right endpoint exactly when `family` is
///   a path type whose carrier and left endpoint read no index its binder binds
///   and which reads none of the `opened` indices past that binder;
///   [`Family::Other`] otherwise.
/// - provides: the shape every link of a cong chain shares.
/// - fails: [`ConversionFault::Evaluation`] carrying the free-index walk's
///   fault as the evaluator names it.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the opened indices, not recursion.
/// - measure: the indices still to test.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fused`]: a chain whose link reads the bound path in
///   its family is no chain.
/// - witness: `fusion::tests::a_cong_chain_composing_to_the_identity_is_its_path`
#[spec(ensures: |ret| match ret {
    Ok(Family::Link(endpoint)) => matches!(core.value_type(family), Some(&ValueType::Path { right, .. }) if right == endpoint),
    Ok(Family::Other) | Err(_) => true,
})]
fn link(
    core: &CoreArena,
    family: ValueTypeId,
    opened: Binders,
) -> Result<Family, ConversionFault>
{
    let refused = |fault| {
        ConversionFault::Evaluation(match fault {
            FreeFault::Dangling => EvalFault::DanglingTerm,
            FreeFault::MachineInvariant => EvalFault::MachineInvariant,
        })
    };
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = core.value_type(family)
    else {
        return Ok(Family::Other);
    };
    let bound = DeBruijnIndex::from(0_u32);
    let mut free = FreeIndices::default();
    if free
        .of_type(core, carrier)
        .map_err(refused)?
        .intuitionistic()
        .holds(bound)
        == Membership::Held
        || free
            .of(core, CoreTerm::Value(left))
            .map_err(refused)?
            .intuitionistic()
            .holds(bound)
            == Membership::Held
    {
        return Ok(Family::Other);
    }
    for index in 1_u32 ..= u32::from(opened) {
        if free
            .of_type(core, family)
            .map_err(refused)?
            .intuitionistic()
            .holds(DeBruijnIndex::from(index))
            == Membership::Held
        {
            return Ok(Family::Other);
        }
    }
    Ok(Family::Link(right))
}

#[cfg(test)]
mod tests;
