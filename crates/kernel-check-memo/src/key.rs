//! What a consumer's support must supply to be usable as a memo key.

use crate::digest::ContentAgreement;
use crate::digest::ContentDigest;

/// A consumer-owned support usable as a memo key.
///
/// The seam names no term, type, or identifier of its own, so every component
/// of a key is the consumer's. What the seam does fix is the *shape* of the
/// key's two comparisons: a digest that may narrow, and a content comparison
/// that decides.
///
/// The associated plane is the accounting partition, not a term notion. A
/// checker that runs two machines over one shared graph — a goal loop over
/// terms and a formation walk over types — gives each machine its own plane, so
/// entry counts can be asserted per plane and neither machine's collapse hides
/// behind the other's numbers. A consumer with one machine uses a plane type
/// with one value.
///
/// # Specification
/// - requires: the implementing support is the **complete** input to one unit
///   of the computation whose outcome it indexes. Equal supports must force
///   equal outcomes, or the memo changes answers and no property of this crate
///   rescues it.
/// - requires: [`MemoKey::digest`] is derived from content alone, and is
///   consistent with [`MemoKey::agreement`] in one direction only — agreeing
///   supports must produce equal digests. The converse is explicitly *not*
///   required, and a memo must not assume it.
/// - requires: [`MemoKey::agreement`] is an equivalence relation on supports,
///   and it decides. A digest comparison is not an admissible implementation.
/// - ensures: [`MemoKey::plane`] is a function of the support, so an entry's
///   plane never changes under it.
/// - provides: the two comparisons a memo needs, with the deciding one named.
///   This stays prose: every clause above constrains the implementor's own
///   relations — the completeness of the support, the one-directional digest
///   agreement, and the equivalence — and a clause on a trait declaration
///   requires the trait itself to carry `#[spec]`, which turns each declaration
///   into a wrapper over a generated required method and changes what an
///   implementor implements.
/// - panics: none.
pub trait MemoKey
{
    /// The consumer's accounting partition.
    type Plane: Copy + Ord;

    /// The plane this support is accounted to.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own preconditions.
    /// - ensures: answers the same plane for the same support, so an entry's
    ///   plane never changes under it.
    /// - provides: the accounting partition per-plane entry counts are kept
    ///   over. This stays prose: which partition a support belongs to is what
    ///   the implementor decides, and a clause on the declaration would change
    ///   what an implementor implements.
    /// - panics: none.
    fn plane(&self) -> Self::Plane;

    /// The content digest: a positive fast path, never a decision.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own preconditions.
    /// - ensures: answers a digest derived from the support's content alone,
    ///   equal for supports that agree; unequal digests prove the supports
    ///   differ, and equal ones decide nothing.
    /// - provides: the bucket selector a memo narrows with before the deciding
    ///   comparison. This stays prose: content derivation and the
    ///   one-directional agreement are obligations on the implementor, and a
    ///   clause on the declaration would change what an implementor implements.
    /// - panics: none.
    fn digest(&self) -> ContentDigest;

    /// The deciding comparison over content.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own preconditions.
    /// - ensures: [`ContentAgreement::Agree`] exactly when the two supports are
    ///   the same complete input, so that either may answer for the other.
    /// - provides: the relation a memo hit is served on. This stays prose:
    ///   whether two supports are the same complete input is what the
    ///   implementor decides, so no clause here can check it, and a clause on
    ///   the declaration would change what an implementor implements.
    /// - panics: none.
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement;
}
