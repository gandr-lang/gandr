//! Explicit serial images for measured candidate and plain equation sizes.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use serde::Serialize;
use serde::ser::Error as _;
use serde::ser::SerializeSeq as _;

use super::Arena;
use super::Candidate;
use super::Entry;
use super::Graph;
use super::GuardId;
use super::Id;
use super::MemberIndex;
use super::Rule;
use super::StageError;
use super::Step;

/// A local decision, independent of compiler enum discriminant layout.
#[repr(transparent)]
struct RuleImage(Rule);
impl Serialize for RuleImage
{
    /// Present the decision as a layout-independent name.
    ///
    /// # Specification
    /// - ensures: presents the exact local rule to the serializer.
    /// - fails: serializer rejection, propagated unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Propagates the serializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — decoding images and replaying their equations against
    ///   the original inputs distinguishes lost payloads, edges and guard
    ///   choices.
    /// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let name = match self.0 {
            | Rule::Congruence => "congruence",
            | Rule::Beta => "beta",
            | Rule::SpliceQuote => "splice-quote",
            | Rule::QuoteSplice => "quote-splice",
            | Rule::IterateZero => "iterate-zero",
            | Rule::IterateSuccessor => "iterate-successor",
            | Rule::Eliminate => "eliminate",
        };
        name.serialize(serializer)
    }
}

/// Both sides and the decision with the same complete graph schema as a
/// template.
#[derive(Serialize)]
struct EquationImage
{
    /// Only reachable syntax, with classifier payloads and edges.
    graph: Graph,
    /// Ordered source and target graph addresses.
    sides: [Id; 2],
    /// The independently replayed decision.
    rule: RuleImage,
}

/// The skeleton and guarded arm dictionary, without discovery columns or
/// caches.
#[derive(Serialize)]
struct TemplateImage
{
    /// Generalized equation; arm roots share its graph.
    equation: EquationImage,
    /// Every point and every guarded arm address.
    entries: Vec<Entry>,
}

/// Serialize arm addresses and guards as pairs rather than JSON object keys.
#[repr(transparent)]
struct Arms<'image>(&'image BTreeMap<Id, GuardId>);
impl Serialize for Arms<'_>
{
    /// Present every arm address with its guard.
    ///
    /// # Specification
    /// - ensures: presents all address/guard pairs in map order.
    /// - fails: serializer rejection, propagated unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Propagates the serializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — decoding images and replaying their equations against
    ///   the original inputs distinguishes lost payloads, edges and guard
    ///   choices.
    /// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.0.len()))?;
        for (id, guard) in self.0 {
            sequence.serialize_element(&(*id, usize::from(*guard)))?;
        }
        sequence.end()
    }
}
impl Serialize for Entry
{
    /// Present a point and its complete arm dictionary.
    ///
    /// # Specification
    /// - ensures: presents the point identity and every guarded arm.
    /// - fails: serializer rejection, propagated unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Propagates the serializer's error.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — decoding images and replaying their equations against
    ///   the original inputs distinguishes lost payloads, edges and guard
    ///   choices.
    /// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        (usize::from(self.point), Arms(&self.arms)).serialize(serializer)
    }
}

/// One member's guard choices in the template's declared point order.
struct Choices<'candidate>
{
    /// Discovery columns are borrowed only while measuring.
    candidate: &'candidate Candidate,
    /// Member position in every correlated column.
    member: MemberIndex,
}
impl Serialize for Choices<'_>
{
    /// Present one complete correlated member substitution.
    ///
    /// # Specification
    /// - ensures: presents exactly one declared guard per point, in entry
    ///   order.
    /// - fails: missing member arms or guards, or serializer rejection.
    /// - panics: none.
    ///
    /// # Errors
    /// Propagates serializer rejection and reports missing member arms or
    /// guards as serializer errors.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — decoding images and replaying their equations against
    ///   the original inputs distinguishes lost payloads, edges and guard
    ///   choices.
    /// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let generalizer = self.candidate;
        let mut sequence = serializer.serialize_seq(Some(generalizer.entries.len()))?;
        for (entry, column) in generalizer.entries.iter().zip(&generalizer.arms) {
            let arm = column
                .get(usize::from(self.member))
                .ok_or_else(|| S::Error::custom("missing member arm"))?;
            let guard = entry
                .arms
                .get(arm)
                .ok_or_else(|| S::Error::custom("missing arm guard"))?;
            sequence.serialize_element(&usize::from(*guard))?;
        }
        sequence.end()
    }
}

impl Candidate
{
    /// Build an untrusted serial image containing only skeleton and distinct
    /// arms.
    ///
    /// # Specification
    /// - ensures: retains constructor payloads, classifier edges, both roots,
    ///   the decision and every guarded arm. No measured cache or counter
    ///   enters the image; a structural or price refusal does not become an
    ///   admission.
    /// - fails: malformed internal graph references.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced` for missing graph addresses.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independently decoding the compacted image and
    ///   replaying each original equation distinguishes stale references and
    ///   lost classifier payloads.
    /// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
    #[inline]
    pub fn image(&self) -> Result<impl Serialize, StageError>
    {
        let mut retained = Vec::from(self.sides);
        retained.extend(
            self.entries
                .iter()
                .flat_map(|entry| entry.arms.keys().copied()),
        );
        let (graph, map) = self.graph.compact(&retained)?;
        let entries = self
            .entries
            .iter()
            .map(|entry| {
                let arms = entry
                    .arms
                    .iter()
                    .map(|(id, guard)| {
                        let id = *map.get(id).ok_or(StageError::Unbalanced)?;
                        Ok((id, *guard))
                    })
                    .collect::<Result<_, StageError>>()?;
                Ok(Entry {
                    point: entry.point,
                    arms,
                })
            })
            .collect::<Result<_, StageError>>()?;
        let [source, target] = self.sides;
        let source = *map.get(&source).ok_or(StageError::Unbalanced)?;
        let target = *map.get(&target).ok_or(StageError::Unbalanced)?;
        Ok(TemplateImage {
            equation: EquationImage {
                graph,
                sides: [source, target],
                rule: RuleImage(self.rule),
            },
            entries,
        })
    }

    /// Borrow every member's complete substitution, including empty ground
    /// rows.
    ///
    /// # Specification
    /// - ensures: one guard row per member, in declared point order; repeated
    ///   occurrences of a point cannot receive independent choices.
    /// - fails: the serializer refuses any missing arm instead of omitting it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — decoded substitutions must reconstruct each original
    ///   source and target, not merely preserve the number of member rows.
    /// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
    #[inline]
    pub fn substitutions(&self) -> impl Iterator<Item = impl Serialize + '_> + '_
    {
        (0 .. usize::from(self.cost.members)).map(|member| Choices {
            candidate: self,
            member: MemberIndex::from(member),
        })
    }
}

/// Build the independent serial image of one plain equation, excluding arena
/// garbage.
///
/// # Specification
/// - ensures: contains all reachable source and target syntax, classifier
///   payloads, roots and rule, with the same graph schema as a template image.
/// - fails: malformed arena references or graph overflow.
/// - panics: none.
///
/// # Errors
/// Propagates staging syntax import errors.
///
/// # Adequacy
/// - hypothesis: L2 — independent per-member serialization includes the actual
///   literal payloads and does not charge normalization intermediates.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
#[inline]
pub fn plain_image(
    arena: &Arena,
    step: &Step,
) -> Result<impl Serialize, StageError>
{
    let mut graph = Graph::default();
    let roots = graph.import(arena, &[step.source, step.target])?;
    let source = *roots.first().ok_or(StageError::Unbalanced)?;
    let target = *roots.get(1).ok_or(StageError::Unbalanced)?;
    Ok(EquationImage {
        graph,
        sides: [source, target],
        rule: RuleImage(step.rule),
    })
}
