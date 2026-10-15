//! The products of two universe paths and of two universe flows in the core:
//! `pathProduct(p, q)`, judged componentwise and elaborated to the kernel's
//! native product, and its directed twin `flowProduct(p, q)`.
//!
//! # The rule
//!
//! `pathProduct(p, q)` synthesises from its two components, each a path of
//! the universe in either of its two readings: the native `Path_U(⌜A⌝, ⌜A′⌝)`
//! the checker's own forms synthesise, or the element identity
//! `Path(Type, ⌜A⌝, ⌜A′⌝)` at the value universe of level zero that
//! `here(⌜A⌝)`, `equiv(f, g)` and `ua[n, k]` synthesise. Every endpoint is a
//! quoted closed first-order code, as [`crate::formation::path_code`] reads
//! one. From `p` relating `⌜A⌝` to `⌜A′⌝` and `q` relating `⌜B⌝` to `⌜B′⌝` the
//! product relates the eager pairs `⌜A × B⌝` and `⌜A′ × B′⌝`: at
//! `Path(Type, …)` when either component reads as an element identity, at
//! `Path_U(…)` when both are native. The product is binary, as the kernel's
//! is, so a telescope nests to the right: `pathProduct(p₀, pathProduct(p₁,
//! p₂))` relates `⌜A₀ × (A₁ × A₂)⌝`.
//!
//! A component that reads as neither is [`CheckRefusal::ShapeMismatch`]
//! wanting a universe path; an endpoint that is no closed first-order code is
//! [`CheckRefusal::PathCode`].
//!
//! # Elaboration
//!
//! A product with an element component is elaborated to the native product
//! [`native`] reads it as, and the checker records that path at the product's
//! node, as it records the path a `ua` statement derives: a constant the
//! product defines unfolds to it, the bridge erases the node to it, and the
//! kernel admits it. Each component is read as the native certificate it
//! stands for: `here(⌜A⌝)` as the reflexivity at the code, `equiv(f, g)` as the
//! universe certificate over its two translators with the round-trip evidence
//! its decision recorded, a `ua` statement or an inner product as the path the
//! checker recorded for it, and a constant as its definition. A component that
//! names no closed certificate — a path a parameter binds, or a constant with
//! no body — is [`CheckRefusal::ShapeMismatch`] at the component, wanting the
//! universe path: the kernel's product relates certificates, and an open path
//! is none.
//!
//! The degree-one path `ua[1, k]` derives, written by hand, is such a product;
//! [`crate::ua`] § The derivation states what the derived form carries beyond
//! it.
//!
//! # The directed product
//!
//! `flowProduct(p, q)` synthesises from two components, each a flow of the
//! universe `Flow(Type, ⌜A⌝, ⌜A′⌝)` at the value universe of level zero —
//! what `stay(⌜A⌝)`, `forward(f)`, a composite and an inner flow product
//! synthesise — between quoted closed first-order codes. From `p` relating
//! `⌜A⌝` to `⌜A′⌝` and `q` relating `⌜B⌝` to `⌜B′⌝` the product flows from
//! `⌜A × B⌝` to `⌜A′ × B′⌝`, nested to the right as the path product nests. A
//! component at any other type is [`CheckRefusal::ShapeMismatch`] wanting a
//! flow; an endpoint that is no closed first-order code is
//! [`CheckRefusal::PathCode`]. No elaboration is needed: the surface's flows
//! are the kernel's own introductions, so the bridge erases the product to the
//! kernel's `FlowProduct` over its erased components, and the kernel reads each
//! component under either reading of the universe. A ride along it at the
//! decode of the binder moves a pair componentwise, the first flow on the left.
//!
//! The degree-one universe flow over a telescope, written by hand, is a nested
//! flow product of `stay` at the unit and one forward flow per corolla — the
//! shape a derived directed univalence at degree one would take.
//!
//! # Decisions
//!
//! - **Elaborated, as `ua` is.** The written product is a term of the surface
//!   vocabulary over surface certificates; what the kernel admits and what
//!   conversion compares is the native product. The alternative, a conversion
//!   rule identifying `equiv(f, g)` with its native certificate and `here(⌜A⌝)`
//!   with the native reflexivity, makes conversion compare two vocabularies
//!   where it now compares one. Reversal: a core whose universe certificates
//!   are one former on both sides of the bridge.
//! - **Both readings of a component.** The surface writes universe paths at
//!   `Path(Type, …)` and the checker's own forms stand at `Path_U`, so a rule
//!   that read one would refuse the other's products. A product over native
//!   components alone keeps the native classifier, so a native module's product
//!   types as it always has. Reversal: one universe path type in the core.
//! - **Open components refused.** The kernel's product rule reads each
//!   component's native classifier, and a path a parameter binds has none, so
//!   accepting it would leave the kernel to refuse what the checker admitted.
//!   Reversal: a kernel product that reads a component's universe identity
//!   through its fibre.
//!
//! # References
//!
//! - Michael Shulman. "Univalence for Inverse Diagrams and Homotopy
//!   Canonicity." _Mathematical Structures in Computer Science_ 25, 5 (2015).
//!   `doi:10.1017/S0960129514000565` — a diagram's identity built stage by
//!   stage as a product over its matching objects: the telescope a nested
//!   product writes.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// Which of the universe's two path types a component synthesised.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Reading
{
    /// The native `Path_U(⌜A⌝, ⌜A′⌝)`.
    Native,
    /// The element identity `Path(Type, ⌜A⌝, ⌜A′⌝)` at the value universe of
    /// level zero.
    Element,
}

/// One component of a product: the two codes its path relates and how its
/// classifier reads.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Component
{
    /// The source code.
    pub source: ValueTypeId,
    /// The target code.
    pub target: ValueTypeId,
    /// The path type the component synthesised.
    pub reading: Reading,
}

/// The component `at` of a product, read off the type it synthesised.
///
/// # Specification
/// - requires: `classifier` is the type `at` synthesised.
/// - ensures: the two decoded endpoint codes of `Path_U(⌜A⌝, ⌜A′⌝)`, read as
///   [`Reading::Native`], or of `Path(Type, ⌜A⌝, ⌜A′⌝)` at the value universe
///   of level zero, read as [`Reading::Element`].
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a universe path,
///   for any other classifier; [`CheckRefusal::PathCode`] for an endpoint that
///   is no quoted closed first-order code; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity at the unit and an equivalence of Bool read
///   as element identities, a native product's components as native paths, and
///   a path at Integer is refused by its shape.
/// - witness: `product::tests::a_product_of_written_paths_elaborates_to_the_native_product`
/// - witness: `product::tests::what_the_product_cannot_read_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == TermNode::Value(at) && wanted == ExpectedShape::PathUniverse && found == TypeNode::Value(classifier),
    | Ok(_) | Err(_) => true,
})]
pub fn component(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifier: ValueTypeId,
) -> Result<Component, CheckRefusal>
{
    let refused = CheckRefusal::ShapeMismatch {
        at: TermNode::Value(at),
        wanted: ExpectedShape::PathUniverse,
        found: TypeNode::Value(classifier),
    };
    let head = context.whnf_value_type(classifier)?;
    let (source, target, reading) = match value_type_view(context.arena(), head)? {
        ValueTypeView::PathUniverse(source, target) => (source, target, Reading::Native),
        ValueTypeView::Path {
            carrier,
            left,
            right,
        } => {
            let carrier = context.whnf_value_type(carrier)?;
            match value_type_view(context.arena(), carrier)? {
                ValueTypeView::Universe {
                    sort: GroundSort::Value,
                    level,
                } if *level == Level::zero() => (left, right, Reading::Element),
                ValueTypeView::Data { .. }
                | ValueTypeView::Record(_)
                | ValueTypeView::Stack { .. }
                | ValueTypeView::PathUniverse(..)
                | ValueTypeView::Path { .. }
                | ValueTypeView::Flow { .. }
                | ValueTypeView::Run(_)
                | ValueTypeView::Sum(_)
                | ValueTypeView::List(_)
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Universe { .. }
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Element { .. }
                | ValueTypeView::Product(_)
                | ValueTypeView::StaticPi { .. }
                | ValueTypeView::Sigma { .. }
                | ValueTypeView::Abstract(_)
                | ValueTypeView::Staged { .. }
                | ValueTypeView::Capability { .. }
                | ValueTypeView::Session(_)
                | ValueTypeView::Unknown => return Err(refused),
            }
        },
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Session(_)
        | ValueTypeView::Unknown => return Err(refused),
    };
    Ok(Component {
        source: crate::formation::path_code(context.arena(), source)?,
        target: crate::formation::path_code(context.arena(), target)?,
        reading,
    })
}

/// The path type a product of `first` and `second` synthesises.
///
/// # Specification
/// - ensures: between the quotes of the eager pairs of the two components'
///   sources and of their targets, the element identity at the value universe
///   of level zero when either component reads as one, and the native universe
///   path otherwise.
/// - panics: none.
/// - executable: none — the minted node is compared by the judgement that
///   checks the product against its declared type.
///
/// # Adequacy
/// - hypothesis: L3 — a product of written paths synthesises the element
///   identity between its pairs and checks at the declared telescope, and a
///   product of native paths keeps the native classifier.
/// - witness: `product::tests::a_product_of_written_paths_elaborates_to_the_native_product`
/// - witness: `bridge::tests::native_path_module_round_trips`
pub fn classifier(
    arena: &mut CoreArena,
    first: Component,
    second: Component,
) -> ValueTypeId
{
    let source = arena.value_type_product(&[first.source, second.source]);
    let target = arena.value_type_product(&[first.target, second.target]);
    let source = arena.value_quote(source);
    let target = arena.value_quote(target);
    if first.reading == Reading::Native && second.reading == Reading::Native {
        return arena.value_type_path_universe(source, target);
    }
    let universe = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    arena.value_type_path(universe, source, target)
}

/// The component `at` of a flow product, read off the type it synthesised:
/// its source and target codes.
///
/// # Specification
/// - requires: `classifier` is the type `at` synthesised.
/// - ensures: the two decoded endpoint codes of `Flow(Type, ⌜A⌝, ⌜A′⌝)` at the
///   value universe of level zero, source first.
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a flow, for any
///   other classifier; [`CheckRefusal::PathCode`] for an endpoint that is no
///   quoted closed first-order code; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — `stay` at the unit and a forward flow of Bool read as
///   universe flows, and a flow at Integer is refused by its shape.
/// - witness: `product::tests::a_flow_product_synthesises_the_flow_between_its_pairs`
/// - witness: `product::tests::what_the_flow_product_cannot_read_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == TermNode::Value(at) && wanted == ExpectedShape::Flow && found == TypeNode::Value(classifier),
    | Ok(_) | Err(_) => true,
})]
pub fn flow_component(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifier: ValueTypeId,
) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
{
    let refused = CheckRefusal::ShapeMismatch {
        at: TermNode::Value(at),
        wanted: ExpectedShape::Flow,
        found: TypeNode::Value(classifier),
    };
    let head = context.whnf_value_type(classifier)?;
    let ValueTypeView::Flow {
        carrier,
        source,
        target,
    } = value_type_view(context.arena(), head)?
    else {
        return Err(refused);
    };
    let carrier = context.whnf_value_type(carrier)?;
    match value_type_view(context.arena(), carrier)? {
        ValueTypeView::Universe {
            sort: GroundSort::Value,
            level,
        } if *level == Level::zero() => {},
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Session(_)
        | ValueTypeView::Unknown => return Err(refused),
    }
    Ok((
        crate::formation::path_code(context.arena(), source)?,
        crate::formation::path_code(context.arena(), target)?,
    ))
}

/// The flow type a flow product of `first` and `second` synthesises.
///
/// # Specification
/// - ensures: `Flow(Type, ⌜A × B⌝, ⌜A′ × B′⌝)` at the value universe of level
///   zero, from the components' sources `A`, `B` and targets `A′`, `B′`.
/// - panics: none.
/// - executable: none — the minted node is compared by the judgement that
///   checks the product against its declared type.
///
/// # Adequacy
/// - hypothesis: L3 — a product of `stay` and a forward flow synthesises the
///   flow between its pairs, and checks at the declared telescope.
/// - witness: `product::tests::a_flow_product_synthesises_the_flow_between_its_pairs`
pub fn flow_classifier(
    arena: &mut CoreArena,
    (first_source, first_target): (ValueTypeId, ValueTypeId),
    (second_source, second_target): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let source = arena.value_type_product(&[first_source, second_source]);
    let target = arena.value_type_product(&[first_target, second_target]);
    let source = arena.value_quote(source);
    let target = arena.value_quote(target);
    let universe = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    arena.value_type_flow(universe, source, target)
}

/// The native product the judged product at `at` stands for.
///
/// # Specification
/// - requires: the product at `at` and both its components were judged, each
///   component's classifier given in `classifiers`, first then second.
/// - ensures: the native path product of the two components' certificates, as
///   [`certificate`] reads each.
/// - fails: as [`certificate`] fails at either component; a node that is no
///   product.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal::ShapeMismatch`] at a component that names no closed
///   certificate; [`CheckRefusal::PathCode`] at reflexivity over an endpoint
///   that is no code; [`CheckRefusal::MachineInvariant`] for a node that is no
///   product, or a judged `equiv` or `ua` with no recorded decision.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity at the unit beside an equivalence of Bool
///   elaborates to the native reflexivity beside the native certificate over
///   the same translators; a component a parameter binds is refused.
/// - witness: `product::tests::a_product_of_written_paths_elaborates_to_the_native_product`
/// - witness: `product::tests::what_the_product_cannot_read_it_refuses_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&native| matches!(context.arena().value(native), Some(Value::PathProduct(..)))))]
pub fn native(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifiers: (ValueTypeId, ValueTypeId),
) -> Result<ValueId, CheckRefusal>
{
    let Some(&Value::PathProduct(first, second)) = context.arena().value(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let first = certificate(context, first, classifiers.0)?;
    let second = certificate(context, second, classifiers.1)?;
    Ok(context.arena_mut().value_path_product(first, second))
}

/// The native certificate the judged path `at` stands for.
///
/// # Specification
/// - requires: `at` was judged at `classifier`.
/// - ensures: a native reflexivity, certificate or product, or `at` itself when
///   it is one: `here(⌜A⌝)` as the reflexivity at `⌜A⌝`; `equiv(f, g)` as the
///   certificate over `f` and `g` at its decision's classifier, with its
///   decision's evidence; a `ua` statement or a product as the path recorded at
///   it; a constant as its definition's certificate.
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a universe path,
///   for a path that names no closed certificate; [`CheckRefusal::PathCode`]
///   for reflexivity at a point that is no code.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above, and [`CheckRefusal::MachineInvariant`] for a
///   judged `equiv` or `ua` with no recorded decision.
///
/// # Termination
/// - reason: one `loop` that only continues through a constant's definition.
/// - measure: the admission position of the constant read; a definition only
///   names constants admitted before its own.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity, an equivalence through a constant and a
///   parameter each reach their own arm.
/// - witness: `product::tests::a_product_of_written_paths_elaborates_to_the_native_product`
/// - witness: `product::tests::what_the_product_cannot_read_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(native) => matches!(context.arena().value(native), Some(Value::PathRefl(_) | Value::PathEquiv { .. } | Value::PathProduct(..))),
    | Err(CheckRefusal::ShapeMismatch { found, .. }) => found == TypeNode::Value(classifier),
    | Err(_) => true,
})]
fn certificate(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifier: ValueTypeId,
) -> Result<ValueId, CheckRefusal>
{
    let open = CheckRefusal::ShapeMismatch {
        at: TermNode::Value(at),
        wanted: ExpectedShape::PathUniverse,
        found: TypeNode::Value(classifier),
    };
    let mut read = at;
    loop {
        let recorded = context.natives().get(&read).copied();
        match context.arena().value(read) {
            Some(&(Value::PathRefl(_) | Value::PathEquiv { .. })) => return Ok(read),
            Some(&Value::PathProduct(..)) => return Ok(recorded.unwrap_or(read)),
            Some(&Value::Ua { .. }) => return recorded.ok_or(CheckRefusal::MachineInvariant),
            Some(&Value::Equiv(forward, backward)) => {
                let Some(decided) = context.equivalences().get(&read)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let (path_type, evidence) = (decided.classifier(), Arc::clone(decided.evidence()));
                return Ok(context
                    .arena_mut()
                    .value_path_equiv(path_type, forward, backward, evidence));
            },
            Some(&Value::Here(point)) => {
                let _code = crate::formation::path_code(context.arena(), point)?;
                return Ok(context.arena_mut().value_path_refl(point));
            },
            Some(&Value::Constant(constant)) => match context.definitions().body(constant) {
                Maybe::Present(body) => read = body,
                Maybe::Absent(_) => return Err(open),
            },
            _ => return Err(open),
        }
    }
}
