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
/// - panics: none.
/// - executable: none — these are laws over consumer-defined computations and
///   relations; applying the attribute to the trait also generates new required
///   methods and changes the implementor API.
///
/// # Adequacy
/// - hypothesis: L2 — the shared and unshared finite DAG workload compares
///   answers with a fresh walk on both planes, catching omitted support
///   content. L1 closed-form expansion counts distinguish content keys from
///   arena positions. L3 colliding unequal contents and equal contents on
///   distinct planes separate digest-only and plane-blind agreement. These
///   witnesses cover the shipped fixtures, not arbitrary implementations.
/// - witness: `differential::tests::memoized_and_memoless_agree_answer_for_answer`
/// - witness: `differential::tests::a_content_key_collapses_the_unshared_spelling_too`
/// - witness: `memo::tests::colliding_digests_share_a_bucket_and_still_decide`
/// - witness: `memo::tests::entries_are_accounted_to_their_own_plane`
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
    ///   over.
    /// - panics: none.
    /// - executable: none — the partition is consumer-defined, and decorating
    ///   this declaration generates required methods in the implementor API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — on supports with equal content but distinct planes,
    ///   exact independent entry counts and served outcomes distinguish a
    ///   constant partition or plane-blind support identity. Repeated entries
    ///   on one plane distinguish per-plane counts from the total.
    /// - witness: `memo::tests::entries_are_accounted_to_their_own_plane`
    fn plane(&self) -> Self::Plane;

    /// The content digest: a positive fast path, never a decision.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own preconditions.
    /// - ensures: answers a digest derived from the support's content alone,
    ///   equal for supports that agree; unequal digests prove the supports
    ///   differ, and equal ones decide nothing.
    /// - provides: the bucket selector used before the deciding comparison.
    /// - panics: none.
    /// - executable: none — the source content and equivalence are supplied by
    ///   the consumer; a declaration attribute changes required trait methods.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — equal subgraphs at different arena positions must
    ///   reach the closed-form distinct-content count, separating position
    ///   hashes from content hashes. L3 an equal digest for unequal content
    ///   must still produce distinct answers and a colliding miss, separating a
    ///   bucket selector from an equality decision.
    /// - witness: `differential::tests::a_content_key_collapses_the_unshared_spelling_too`
    /// - witness: `memo::tests::colliding_digests_share_a_bucket_and_still_decide`
    fn digest(&self) -> ContentDigest;

    /// The deciding comparison over content.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own preconditions.
    /// - ensures: [`ContentAgreement::Agree`] exactly when the two supports are
    ///   the same complete input, so that either may answer for the other.
    /// - provides: the relation a memo hit is served on.
    /// - panics: none.
    /// - executable: none — complete-input equivalence belongs to the consumer;
    ///   a declaration attribute would change the required implementor API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for the fixture relation, equal support, unequal
    ///   content sharing a digest, and equal content on distinct planes have
    ///   exact hit, miss and separate-answer observations. These distinguish
    ///   digest-only, content-only and always-different comparisons; they do
    ///   not prove the equivalence laws for arbitrary downstream supports.
    /// - witness: `memo::tests::remembering_an_agreeing_support_replaces_rather_than_accumulates`
    /// - witness: `memo::tests::colliding_digests_share_a_bucket_and_still_decide`
    /// - witness: `memo::tests::entries_are_accounted_to_their_own_plane`
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement;
}
