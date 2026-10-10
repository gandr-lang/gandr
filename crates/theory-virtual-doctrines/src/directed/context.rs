//! Variance-sorted contexts for reflected signatures.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellVariance;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use quenchant_shape::shape::Maybe;

use crate::boundary::DirectedContextDeclaration;
use crate::boundary::DirectedObjectCovariance;
use crate::vdc::SignatureRef;

/// The **variance** a reflected object variable is sorted at
///  — the directed polarity `x : I` vs `x
/// : Iᵒᵖ`.
///
/// This is the closed two-way polarity vocabulary of directed type theory. The
/// engine's [`CellVariance`] has a third case, [`CellVariance::Mixed`] — a hole
/// spanning both polarities — which is **not** a directed variance (it is the
/// mixed-polarity shape excluded by directed transport); [`Variance::of_cell`]
/// maps it to `Absent`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Variance
{
    /// **Covariant** — the variable ranges over `I` (a producer / target slot).
    Covariant,
    /// **Contravariant** — the variable ranges over `Iᵒᵖ` (a consumer / source
    /// slot).
    Contravariant,
}

impl Variance
{
    /// The **opposite** variance — the `−ᵒᵖ` involution on the polarity itself.
    ///
    /// # Specification
    /// - ensures: [`Variance::Contravariant`] for [`Variance::Covariant`] and
    ///   vice versa; `flip(flip(v)) == v` (an involution).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — both polarities reverse, so an identity action cannot
    ///   satisfy the pointwise contract even though it is an involution.
    /// - witness: `tests::directed::tests::op_is_an_involution_on_reflected_signatures`
    #[spec(ensures: |out| matches!((self, out), (Self::Covariant, Self::Contravariant) | (Self::Contravariant, Self::Covariant)))]
    pub fn flip(self) -> Self
    {
        match self {
            | Self::Covariant => Self::Contravariant,
            | Self::Contravariant => Self::Covariant,
        }
    }

    /// The directed variance an engine [`CellVariance`] witnesses, or `Absent`
    /// when the hole is [`CellVariance::Mixed`] (spans both polarities — not a
    /// directed variance).
    ///
    /// # Specification
    /// - ensures: [`Variance::Covariant`] for [`CellVariance::Producer`],
    ///   [`Variance::Contravariant`] for [`CellVariance::Consumer`], and
    ///   `Absent` for [`CellVariance::Mixed`] — the mapping that makes the
    ///   reflection rules metadata checkable against a directed context.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L3 — producer, consumer and mixed metadata each have a
    ///   distinct observed result; the mixed case cannot silently choose a
    ///   polarity.
    /// - witness: `tests::directed::tests::a_mixed_hole_cannot_be_sorted_at_a_directed_variance`
    #[spec(ensures: |out| matches!((variance, out), (CellVariance::Producer, Maybe::Present(Self::Covariant)) | (CellVariance::Consumer, Maybe::Present(Self::Contravariant)) | (CellVariance::Mixed, Maybe::Absent(variance_sorting::Absent::BothPolarities))))]
    pub fn of_cell(variance: CellVariance) -> Maybe<Self, variance_sorting::Absent>
    {
        match variance {
            | CellVariance::Producer => Maybe::Present(Self::Covariant),
            | CellVariance::Consumer => Maybe::Present(Self::Contravariant),
            | CellVariance::Mixed => Maybe::Absent(variance_sorting::Absent::BothPolarities),
        }
    }
}

/// A **reflected signature with a variance slot** — the directed object a
/// variable stands in, `I` (covariant) or `Iᵒᵖ` (contravariant).
///
/// The `op` involution ([`OpSig::op`]) lives here, on the *reflected*
/// signature, never on the frozen [`SignatureRef`] core.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OpSig
{
    /// The underlying reflected signature (a frozen-core [`SignatureRef`]).
    pub sig: SignatureRef,
    /// The variance slot the signature stands in.
    pub variance: Variance,
}

impl OpSig
{
    /// The **covariant** sorting of `sig` (`x : I`).
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn covariant(sig: SignatureRef) -> Self
    {
        Self {
            sig,
            variance: Variance::Covariant,
        }
    }

    /// The **contravariant** sorting of `sig` (`x : Iᵒᵖ`).
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn contravariant(sig: SignatureRef) -> Self
    {
        Self {
            sig,
            variance: Variance::Contravariant,
        }
    }

    /// The **opposite** object `−ᵒᵖ` — the same underlying signature at the
    /// flipped variance.
    ///
    /// # Specification
    /// - ensures: the same `sig` with [`Variance::flip`] applied; `op(op(x)) ==
    ///   x` (an involution), realized on the reflected signature alone — the
    ///   frozen [`SignatureRef`] is unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — `op` is asserted an involution over
    ///   generated signatures and both variances; the boundary is that the
    ///   underlying `sig` never changes.
    /// - witness: `tests::directed::tests::op_is_an_involution_on_reflected_signatures`
    #[inline]
    #[must_use]
    #[spec(ensures: |out| out.sig == self.sig && out.variance == self.variance.flip())]
    pub fn op(&self) -> Self
    {
        Self {
            sig: self.sig.clone(),
            variance: self.variance.flip(),
        }
    }

    /// Whether this object stands in the covariant slot.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_covariant(&self) -> DirectedObjectCovariance
    {
        DirectedObjectCovariance::from(matches!(self.variance, Variance::Covariant))
    }
}

/// A **variance-sorted reflected context** — object variables paired with the
/// directed object ([`OpSig`]) they range over.
///
/// The undirected face's [`crate::check::Context`] is two-sided but
/// variance-blind; the directed context sorts each variable by variance
/// instead, so the polarity side condition of the directed J
/// ([`crate::directed::hom`]) and the variance check below can consult it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DirectedContext
{
    /// The variance-sorted object variables, in binding order.
    pub vars: Vec<(Name, OpSig)>,
}

/// Why an engine cell's variance disagrees with a directed context.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum VarianceError
{
    /// A cell hole naming a declared object variable is sorted at the opposite
    /// polarity from the context.
    Mismatch
    {
        /// The object variable the hole names.
        var: Name,
        /// The variance the context sorted it at.
        declared: Variance,
        /// The variance the engine derived for the hole.
        derived: Variance,
    },
    /// A cell hole naming a declared object variable is [`CellVariance::Mixed`]
    /// — it spans both polarities, so it cannot be sorted at a single directed
    /// variance.
    MixedHole
    {
        /// The object variable the mixed hole names.
        var: Name,
    },
}

impl DirectedContext
{
    /// An empty variance-sorted context.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Sort `name` at the directed object `obj`.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn with_var(
        mut self,
        name: NameRef<'_>,
        obj: OpSig,
    ) -> Self
    {
        self.vars.push((Name::from(name), obj));
        self
    }

    /// The variance `name` is sorted at — the **innermost** binding, or
    /// `Absent` when `name` is undeclared.
    ///
    /// # Specification
    /// - ensures: the [`Variance`] of the last `(name, _)` binding, or
    ///   `Absent`.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L1 — exact innermost-binding projection and absence are
    ///   executable; the variance laws exercise declared versus derived
    ///   polarity.
    /// - witness: `tests::directed::tests::a_producer_hole_sorted_contravariantly_is_rejected`
    #[spec(ensures: |out| match (out, self.vars.iter().rfind(|entry| entry.0.as_ref() == name.as_ref())) { (Maybe::Present(variance), Some(entry)) => variance == entry.1.variance, (Maybe::Absent(_), None) => true, _ => false })]
    pub fn variance_of(
        &self,
        name: NameRef<'_>,
    ) -> Maybe<Variance, context_lookup::Absent>
    {
        for binding in self.vars.iter().rev() {
            if binding.0.as_ref() == name.as_ref() {
                return Maybe::Present(binding.1.variance);
            }
        }
        Maybe::Absent(context_lookup::Absent::Undeclared)
    }

    /// The signature `name` ranges over — the **innermost** binding, or
    /// `Absent` when `name` is undeclared.
    ///
    /// # Specification
    /// - ensures: the [`SignatureRef`] of the last `(name, _)` binding, or
    ///   `Absent`.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L1 — exact innermost-signature projection and absence are
    ///   executable. The opposite law observes signature preservation
    ///   independently of the polarity.
    /// - witness: `tests::directed::tests::op_is_an_involution_on_reflected_signatures`
    #[spec(ensures: |out| match (out, self.vars.iter().rfind(|entry| entry.0.as_ref() == name.as_ref())) { (Maybe::Present(signature), Some(entry)) => signature == &entry.1.sig, (Maybe::Absent(_), None) => true, _ => false })]
    pub fn signature_of(
        &self,
        name: NameRef<'_>,
    ) -> Maybe<&SignatureRef, context_lookup::Absent>
    {
        for binding in self.vars.iter().rev() {
            if binding.0.as_ref() == name.as_ref() {
                return Maybe::Present(&binding.1.sig);
            }
        }
        Maybe::Absent(context_lookup::Absent::Undeclared)
    }

    /// Whether `name` is declared.
    ///
    /// # Specification
    /// - ensures: `true` iff `name` appears in `vars`.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — declaration membership separates constrained engine
    ///   holes from undeclared ones.
    /// - witness: `tests::directed::tests::an_undeclared_hole_is_unconstrained`
    #[spec(ensures: |out| bool::from(out) == self.vars.iter().any(|entry| entry.0.as_ref() == name.as_ref()))]
    pub fn declares(
        &self,
        name: NameRef<'_>,
    ) -> DirectedContextDeclaration
    {
        for binding in &self.vars {
            if binding.0.as_ref() == name.as_ref() {
                return DirectedContextDeclaration::from(true);
            }
        }
        DirectedContextDeclaration::from(false)
    }

    /// **Check** an engine cell's derived variance against this context — the
    /// the reflection rules metadata made *checkable*.
    ///
    /// Every metavariable of `cell` whose name is a declared object variable
    /// must be derived at the variance the context sorted it at; a hole the
    /// engine classified [`CellVariance::Mixed`] cannot inhabit a single
    /// directed variance at all. Holes the context does not declare are the
    /// cell's own local data and are not constrained.
    ///
    /// # Specification
    /// - ensures: `Ok(())` iff, for each of `cell`'s derived
    ///   [`gandr_theory_cell_complexes::CellVarMeta`] whose name this context
    ///   declares, the [`Variance::of_cell`] of its derived [`CellVariance`]
    ///   equals the declared [`Variance`]; a `Mixed` hole naming a declared
    ///   variable fails.
    /// - fails: [`VarianceError::Mismatch`] for a declared hole at the opposite
    ///   polarity; [`VarianceError::MixedHole`] for a declared hole the engine
    ///   classified `Mixed`.
    /// - panics: none.
    ///
    /// # Errors
    /// See the `- fails:` clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — a producer hole sorted covariantly passes;
    ///   the same hole sorted contravariantly asserts
    ///   [`VarianceError::Mismatch`]; a `Mixed` hole (a name at both
    ///   polarities) sorted at either variance asserts
    ///   [`VarianceError::MixedHole`].
    /// - witness: `tests::directed::tests::a_producer_hole_checks_covariantly`
    /// - witness: `tests::directed::tests::a_producer_hole_sorted_contravariantly_is_rejected`
    /// - witness: `tests::directed::tests::a_mixed_hole_cannot_be_sorted_at_a_directed_variance`
    #[inline]
    #[spec(ensures: |out| out.is_ok() == cell.meta().vars().iter().all(|meta| match self.variance_of(NameRef::from(meta.var().hole().as_ref())) { Maybe::Absent(_) => true, Maybe::Present(declared) => Variance::of_cell(meta.variance()) == Maybe::Present(declared) }))]
    pub fn check_cell_variance(
        &self,
        cell: &Cell,
    ) -> Result<(), VarianceError>
    {
        for var_meta in cell.meta().vars() {
            let name = var_meta.var().hole().as_ref();
            let Maybe::Present(declared) = self.variance_of(NameRef::from(name))
            else {
                continue;
            };
            match Variance::of_cell(var_meta.variance()) {
                | Maybe::Absent(_) => {
                    return Err(VarianceError::MixedHole {
                        var: Name::from(name),
                    });
                },
                | Maybe::Present(derived) if derived != declared => {
                    return Err(VarianceError::Mismatch {
                        var: Name::from(name),
                        declared,
                        derived,
                    });
                },
                | Maybe::Present(_) => {},
            }
        }
        Ok(())
    }
}
quenchant_shape::reason_enum! {
/// Why an engine variance has no directed sorting.
pub mod variance_sorting {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// The hole spans both polarities.
    BothPolarities,
}
}
}
quenchant_shape::reason_enum! {
/// Why a context query has no answer.
pub mod context_lookup {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// The object variable is undeclared.
    Undeclared,
}
}

}

impl core::fmt::Display for VarianceError
{
    /// Render the typed refusal and its boundary evidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Mismatch {
                ref var,
                declared,
                derived,
            } => write!(
                f,
                "variable {} is declared {} but derived {}",
                var.as_ref(),
                match declared {
                    | Variance::Covariant => "covariant",
                    | Variance::Contravariant => "contravariant",
                },
                match derived {
                    | Variance::Covariant => "covariant",
                    | Variance::Contravariant => "contravariant",
                }
            ),
            | Self::MixedHole { ref var } => {
                write!(f, "variable {} occurs at both polarities", var.as_ref())
            },
        }
    }
}
impl core::error::Error for VarianceError
{
}
