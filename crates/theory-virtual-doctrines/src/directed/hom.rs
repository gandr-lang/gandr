//! Polarity-restricted elimination of directed hom.

use anodized::spec;

use crate::boundary::DirectedHomReflexivity;
use crate::boundary::MotiveCovariance;
use crate::vdc::SignatureRef;
use crate::vdc::TermRef;

/// A **directed hom** protype `hom_I(a ⇝ b)` — the directed refinement of
/// [`crate::syntax::ProtypeKind::Path`].
///
/// The source `a` stands in the contravariant slot, the target `b` in the
/// covariant slot; unlike the undirected path, the two endpoints are **not**
/// interchangeable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DirectedHom
{
    /// The signature both endpoints inhabit.
    pub sig: SignatureRef,
    /// The contravariant **source** endpoint `a`.
    pub src: TermRef,
    /// The covariant **target** endpoint `b`.
    pub tgt: TermRef,
}

impl DirectedHom
{
    /// The directed hom `hom_sig(src ⇝ tgt)`.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(
        sig: SignatureRef,
        src: TermRef,
        tgt: TermRef,
    ) -> Self
    {
        Self { sig, src, tgt }
    }

    /// The **reflexive** directed hom `hom_sig(term ⇝ term)` — the diagonal the
    /// directed J's base case inhabits.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn refl(
        sig: SignatureRef,
        term: TermRef,
    ) -> Self
    {
        Self {
            sig,
            src: term.clone(),
            tgt: term,
        }
    }

    /// Whether this hom is on the diagonal (`src == tgt`) — reflexive.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_reflexive(&self) -> DirectedHomReflexivity
    {
        DirectedHomReflexivity::from(self.src == self.tgt)
    }
}

/// Which slot of the motive's produced hom the **moving** (covariant) endpoint
/// occupies.
///
/// The directed J transports along the scrutinee's covariant target endpoint;
/// the motive `C(x)` abstracts that endpoint. Only a motive that keeps it
/// covariant is admissible — a contravariant use is the symmetry shape the
/// polarity side condition refuses.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MotiveShape
{
    /// `C(x) = hom(fixed ⇝ x)` — the moving endpoint stays in the covariant
    /// **target** slot. **J-admissible.**
    CovariantTarget,
    /// `C(x) = hom(x ⇝ fixed)` — the moving endpoint is in the contravariant
    /// **source** slot. This is the **symmetry** shape; the polarity side
    /// condition refuses it.
    ContravariantSource,
    /// `C(x) = hom(fixed ⇝ fixed)` — the moving endpoint is unused (a constant
    /// family). **J-admissible** (trivially covariant).
    Constant,
}

impl MotiveShape
{
    /// Whether this motive respects the covariance the directed J requires.
    ///
    /// # Specification
    /// - ensures: `true` for [`MotiveShape::CovariantTarget`] and
    ///   [`MotiveShape::Constant`]; `false` for
    ///   [`MotiveShape::ContravariantSource`] (the symmetry shape).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — generated endpoints cannot make the contravariant
    ///   motive admissible; the two admitted motive shapes remain distinct.
    /// - witness: `tests::directed::tests::symmetry_is_never_derivable`
    #[spec(ensures: |out| bool::from(out) == matches!(self, Self::CovariantTarget | Self::Constant))]
    pub fn is_covariant(self) -> MotiveCovariance
    {
        MotiveCovariance::from(!matches!(self, Self::ContravariantSource))
    }
}

/// A **directed-J elimination** — the motive shape plus the fixed endpoint the
/// motive holds constant.
///
/// The moving endpoint is supplied by the scrutinee's target; `fixed` is the
/// other endpoint the motive's produced hom pins.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DirectedJ
{
    /// Which slot the motive puts the moving endpoint in.
    pub motive: MotiveShape,
    /// The endpoint the motive holds fixed.
    pub fixed: TermRef,
}

impl DirectedJ
{
    /// The directed-J elimination with motive `motive` fixing `fixed`.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(
        motive: MotiveShape,
        fixed: TermRef,
    ) -> Self
    {
        Self { motive, fixed }
    }

    /// The **symmetry** elimination for a scrutinee whose source is `src` — the
    /// motive `C(x) = hom(x ⇝ src)` that would transport backward.
    ///
    /// # Specification
    /// - ensures: [`MotiveShape::ContravariantSource`] fixing `src`; passing it
    ///   to [`check_directed_j`] always yields [`JError::MotiveNotCovariant`]
    ///   (symmetry is underivable).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the fixed endpoint is retained while the moving
    ///   endpoint is marked contravariant; directed J refuses that shape.
    /// - witness: `tests::directed::tests::directed_j_refuses_the_symmetry_motive`
    #[spec(captures: expected = src.clone(), ensures: |out| out.motive == MotiveShape::ContravariantSource && out.fixed == expected)]
    pub fn symmetry(src: TermRef) -> Self
    {
        Self {
            motive: MotiveShape::ContravariantSource,
            fixed: src,
        }
    }
}

/// Why a directed-J elimination is ill-formed.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum JError
{
    /// The motive places the moving endpoint in the contravariant source slot
    /// — the **symmetry** shape the polarity side condition refuses.
    MotiveNotCovariant,
}

/// **Check** a directed-J elimination against a directed-hom scrutinee and
/// return the transported hom.
///
/// The scrutinee's covariant target endpoint is the moving endpoint. The motive
/// must be covariant in it ([`MotiveShape::is_covariant`]); a contravariant
/// motive — the only shape that could produce the reversed `hom(b ⇝ a)` — is
/// the symmetry shape and is refused, so **symmetry is underivable by
/// construction**.
///
/// # Specification
/// - ensures: `Ok(hom(j.fixed ⇝ scrut.tgt))` for
///   [`MotiveShape::CovariantTarget`] (the moving endpoint transported into the
///   covariant slot); `Ok(hom(j.fixed ⇝ j.fixed))` for
///   [`MotiveShape::Constant`]; the result inhabits the same signature as
///   `scrut`.
/// - fails: [`JError::MotiveNotCovariant`] for
///   [`MotiveShape::ContravariantSource`] — the polarity side condition, which
///   is exactly the symmetry case.
/// - panics: none.
///
/// # Errors
/// See the `- fails:` clause.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — a covariant motive transports forward to
///   `hom(fixed ⇝ b)`; the contravariant (symmetry) motive asserts
///   [`JError::MotiveNotCovariant`]; the boundary is that
///   [`DirectedJ::symmetry`] is refused for every generated hom.
/// - witness: `tests::directed::tests::directed_j_transports_along_a_covariant_motive`
/// - witness: `tests::directed::tests::directed_j_refuses_the_symmetry_motive`
/// - witness: `tests::directed::tests::symmetry_is_never_derivable`
#[inline]
#[spec(ensures: |out| match j.motive { MotiveShape::CovariantTarget => out.as_ref().is_ok_and(|hom| (&hom.sig, &hom.src, &hom.tgt) == (&scrut.sig, &j.fixed, &scrut.tgt)), MotiveShape::Constant => out.as_ref().is_ok_and(|hom| (&hom.sig, &hom.src, &hom.tgt) == (&scrut.sig, &j.fixed, &j.fixed)), MotiveShape::ContravariantSource => out == Err(JError::MotiveNotCovariant) })]
pub fn check_directed_j(
    scrut: &DirectedHom,
    j: &DirectedJ,
) -> Result<DirectedHom, JError>
{
    if !bool::from(j.motive.is_covariant()) {
        return Err(JError::MotiveNotCovariant);
    }
    match j.motive {
        | MotiveShape::CovariantTarget => Ok(DirectedHom {
            sig: scrut.sig.clone(),
            src: j.fixed.clone(),
            tgt: scrut.tgt.clone(),
        }),
        | MotiveShape::Constant => Ok(DirectedHom {
            sig: scrut.sig.clone(),
            src: j.fixed.clone(),
            tgt: j.fixed.clone(),
        }),
        | MotiveShape::ContravariantSource => Err(JError::MotiveNotCovariant),
    }
}

impl core::fmt::Display for JError
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
        f.write_str("directed motive places its moving endpoint contravariantly")
    }
}
impl core::error::Error for JError
{
}
