//! Finite discrete ends, coends, Fubini and co-Yoneda.

use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::DiagramCarrierEmptyStatus;
use crate::boundary::DiagramCarrierLength;
use crate::boundary::DiscreteHomInhabitation;
use crate::vdc::TermRef;

/// A **finite diagram** `F` over a reflected signature's carrier.
///
/// The functor an `∫` binder ranges over, reflected as an explicit map from
/// carrier objects to their diagonal components `x ↦ F(x, x)`. The carrier is
/// finite, explicitly enumerated and discrete.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Diagram
{
    /// The `(object, F(object))` entries, one per carrier object, in order.
    pub entries: Vec<(TermRef, TermRef)>,
}

impl Diagram
{
    /// A diagram over the given `(object, component)` entries.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(entries: Vec<(TermRef, TermRef)>) -> Self
    {
        Self { entries }
    }

    /// The component `F(object)` at a carrier object, or `Absent` when the
    /// object is off the carrier.
    ///
    /// # Specification
    /// - ensures: the component of the **first** `(object, _)` entry, or
    ///   `Absent`.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L3 — the first matching carrier entry and the off-carrier
    ///   boundary are observed, including the actual component value.
    /// - witness: `tests::directed::tests::coyoneda_collapses_to_the_diagonal_component`
    #[spec(ensures: |out| match out { Maybe::Present(value) => self.entries.iter().find(|entry| entry.0 == *object).is_some_and(|entry| &entry.1 == value), Maybe::Absent(_) => self.entries.iter().all(|entry| entry.0 != *object) })]
    pub fn component(
        &self,
        object: &TermRef,
    ) -> Maybe<&TermRef, carrier_lookup::Absent>
    {
        for entry in &self.entries {
            if entry.0 == *object {
                return Maybe::Present(&entry.1);
            }
        }
        Maybe::Absent(carrier_lookup::Absent::OffCarrier)
    }

    /// The number of carrier objects.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn len(&self) -> DiagramCarrierLength
    {
        DiagramCarrierLength::from(self.entries.len())
    }

    /// Whether the carrier is empty.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_empty(&self) -> DiagramCarrierEmptyStatus
    {
        DiagramCarrierEmptyStatus::from(self.entries.is_empty())
    }
}

/// The **end** `∫_x F(x, x)` over a finite discrete carrier — the universal
/// quantifier, realized as the product of the diagram's diagonal components.
///
/// The wedge condition is vacuous over a discrete (refl-generated) carrier — no
/// non-identity morphisms constrain the components — so the end is the full
/// product.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct End
{
    /// The product components `F(x, x)`, one per carrier object.
    pub components: Vec<TermRef>,
}

impl End
{
    /// The end of `diagram` — its diagonal components as a product.
    ///
    /// # Specification
    /// - ensures: `components` are the diagram's entry components, in carrier
    ///   order (the discrete-carrier product `Π_x F(x, x)`).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — ordered equality to the carrier components detects
    ///   missing, duplicated or permuted factors.
    /// - witness: `tests::directed::tests::the_end_and_coend_collect_the_diagonal_components`
    #[spec(ensures: |out| out.components.iter().eq(diagram.entries.iter().map(|entry| &entry.1)))]
    pub fn of(diagram: &Diagram) -> Self
    {
        let mut components = Vec::with_capacity(diagram.entries.len());
        for entry in &diagram.entries {
            components.push(entry.1.clone());
        }
        Self { components }
    }
}

/// The **coend** `∫^x F(x, x)` over a finite discrete carrier — the existential
/// quantifier, realized as the coproduct of the diagram's diagonal components.
///
/// The cowedge quotient is trivial over a discrete carrier, so the coend is the
/// full coproduct.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Coend
{
    /// The coproduct summands `F(x, x)`, one per carrier object.
    pub summands: Vec<TermRef>,
}

impl Coend
{
    /// The coend of `diagram` — its diagonal components as a coproduct.
    ///
    /// # Specification
    /// - ensures: `summands` are the diagram's entry components, in carrier
    ///   order (the discrete-carrier coproduct `Σ_x F(x, x)`).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — ordered equality to the carrier components detects
    ///   missing, duplicated or permuted summands.
    /// - witness: `tests::directed::tests::the_end_and_coend_collect_the_diagonal_components`
    #[spec(ensures: |out| out.summands.iter().eq(diagram.entries.iter().map(|entry| &entry.1)))]
    pub fn of(diagram: &Diagram) -> Self
    {
        let mut summands = Vec::with_capacity(diagram.entries.len());
        for entry in &diagram.entries {
            summands.push(entry.1.clone());
        }
        Self { summands }
    }
}

/// A **finite two-variable diagram** `F(x, y)` over a product carrier `Xs × Ys`
/// — the shape a double end `∫_x ∫_y F` quantifies.
///
/// Reflected as an explicit map from `(x, y)` index pairs to payloads; the
/// carrier is finite and enumerated.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BiDiagram
{
    /// The `((x, y), F(x, y))` entries, one per index pair.
    pub entries: Vec<((TermRef, TermRef), TermRef)>,
}

impl BiDiagram
{
    /// A two-variable diagram over the given `((x, y), payload)` entries.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(entries: Vec<((TermRef, TermRef), TermRef)>) -> Self
    {
        Self { entries }
    }

    /// The payloads of the iterated end `∫_x ∫_y F(x, y)` over the discrete
    /// finite carrier — the product components, order-independent.
    ///
    /// # Specification
    /// - ensures: one payload per entry, in entry order; the multiset is the
    ///   iterated-end value that Fubini preserves.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the carrier payloads are preserved with order and
    ///   multiplicity.
    /// - witness: `tests::directed::tests::fubini_preserves_the_iterated_end`
    #[spec(ensures: |out| out.iter().eq(self.entries.iter().map(|entry| &entry.1)))]
    pub fn payloads(&self) -> Vec<TermRef>
    {
        let mut payloads = Vec::with_capacity(self.entries.len());
        for entry in &self.entries {
            payloads.push(entry.1.clone());
        }
        payloads
    }

    /// The index pairs of the carrier, in entry order.
    ///
    /// # Specification
    /// - ensures: the `(x, y)` key of each entry, in order.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — every index pair is observed in carrier order, not
    ///   merely the number of indices.
    /// - witness: `tests::directed::tests::fubini_swap_is_an_involution`
    #[spec(ensures: |out| out.iter().eq(self.entries.iter().map(|entry| &entry.0)))]
    pub fn index_pairs(&self) -> Vec<(TermRef, TermRef)>
    {
        let mut indices = Vec::with_capacity(self.entries.len());
        for entry in &self.entries {
            indices.push(entry.0.clone());
        }
        indices
    }
}

/// **Fubini** — swap the two `∫` binders.
///
/// `∫_x ∫_y F(x, y) ≅ ∫_y ∫_x F(x, y)`. Over the finite carrier the isomorphism
/// is the **transpose bijection** on the index set: each `(x, y)` becomes
/// `(y, x)` with the payload carried unchanged. It is derived, not primitive —
/// the reindexing that witnesses the double end is order-independent — and is
/// its own inverse.
///
/// # Specification
/// - ensures: a [`BiDiagram`] whose entries are `((y, x), F(x, y))` for each
///   `((x, y), F(x, y))` of `f`; the payload multiset ([`BiDiagram::payloads`])
///   is preserved and `fubini_swap(fubini_swap(f)) == f` (an involution).
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 pointwise + property — over generated finite bidiagrams the
///   swap is asserted an involution, the index set exactly transposed, and the
///   iterated-end payload multiset preserved (the finite content of Fubini).
/// - witness: `tests::directed::tests::fubini_swap_is_an_involution`
/// - witness: `tests::directed::tests::fubini_preserves_the_iterated_end`
#[inline]
#[must_use]
#[spec(ensures: |out| out.entries.iter().map(|entry| (&entry.0.0, &entry.0.1, &entry.1)).eq(f.entries.iter().map(|entry| (&entry.0.1, &entry.0.0, &entry.1))))]
pub fn fubini_swap(f: &BiDiagram) -> BiDiagram
{
    BiDiagram {
        entries: f
            .entries
            .iter()
            .map(|entry| {
                let ((ref x, ref y), ref payload) = *entry;
                ((y.clone(), x.clone()), payload.clone())
            })
            .collect(),
    }
}

/// **co-Yoneda** — collapse the density coend `∫^x hom(a, x) × F(x)` to `F(a)`.
///
/// Over the discrete (refl-generated) reflected signature, every off-diagonal
/// summand of the coend is empty ([`discrete_hom_inhabited`]), so the coend
/// collapses to the single `x == a` summand `hom(a, a) × F(a) ≅ F(a)`. This is
/// the derived co-Yoneda (density) transformation over this discrete carrier.
///
/// # Specification
/// - ensures: `Present(F(a))` iff `a` is on `diagram`'s carrier (the surviving
///   diagonal summand); `Absent` when `a` is off the carrier (an empty coend).
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 pointwise + property — over generated finite diagrams the
///   collapse reproduces `F(a)` for every carrier object `a`, and is `Absent`
///   off-carrier; the boundary is that only the diagonal summand survives.
/// - witness: `tests::directed::tests::coyoneda_collapses_to_the_diagonal_component`
/// - witness: `tests::directed::tests::coyoneda_is_none_off_carrier`
#[inline]
#[spec(ensures: |out| out == diagram.component(a))]
pub fn coyoneda_collapse<'diagram>(
    a: &TermRef,
    diagram: &'diagram Diagram,
) -> Maybe<&'diagram TermRef, carrier_lookup::Absent>
{
    for entry in &diagram.entries {
        if bool::from(discrete_hom_inhabited(a, &entry.0)) {
            return Maybe::Present(&entry.1);
        }
    }
    Maybe::Absent(carrier_lookup::Absent::OffCarrier)
}

/// Whether the **discrete** reflected hom `hom(a, x)` is inhabited — at this
/// rung the hom is refl-generated, so it is inhabited exactly on the diagonal.
///
/// # Specification
/// - ensures: `true` iff `a == x` (only `refl` inhabits the discrete hom).
/// - panics: none.
#[inline]
#[must_use]
/// # Adequacy
/// - hypothesis: L3 — the discrete diagonal and its nearest off-diagonal case
///   distinguish inhabited homs. This is not a claim about non-discrete
///   carriers.
/// - witness: `tests::directed::tests::coyoneda_is_none_off_carrier`
#[spec(ensures: |out| bool::from(out) == (a == x))]
pub fn discrete_hom_inhabited(
    a: &TermRef,
    x: &TermRef,
) -> DiscreteHomInhabitation
{
    DiscreteHomInhabitation::from(a == x)
}
quenchant_shape::reason_enum! {
/// Why a finite diagram has no component at an object.
pub mod carrier_lookup {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// The object is outside the enumerated carrier.
    OffCarrier,
}
}

}
