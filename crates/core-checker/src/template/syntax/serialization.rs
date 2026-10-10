//! Flat syntax images: payloads and classifier edges, not interning caches.

use serde::Serialize;
use serde::ser::SerializeSeq as _;

use super::Graph;
use super::Head;
use super::Index;
use super::Natural;
use super::Stage;
use super::Type;
use super::TypeId;

/// A stage tag with its universe identity.
#[repr(transparent)]
struct StageImage(Stage);
impl Serialize for StageImage
{
    /// Present the stage with its model identity.
    ///
    /// # Specification
    /// - ensures: distinguishes outer stage from every inner model.
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
        match self.0 {
            | Stage::Outer => "outer".serialize(serializer),
            | Stage::Inner(model) => ("inner", model.0).serialize(serializer),
        }
    }
}

/// One nonrecursive classifier constructor.
#[repr(transparent)]
struct TypeImage(Type);
impl Serialize for TypeImage
{
    /// Present one complete flat classifier constructor.
    ///
    /// # Specification
    /// - ensures: presents the constructor, model and all classifier edges.
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
        match self.0 {
            | Type::Nat(stage) => ("nat", StageImage(stage)).serialize(serializer),
            | Type::In(model) => ("in", model.0).serialize(serializer),
            | Type::Universe(model) => ("universe", model.0).serialize(serializer),
            | Type::Arrow(a, b) => ("arrow", a.0, b.0).serialize(serializer),
            | Type::Lift(body) => ("lift", body.0).serialize(serializer),
        }
    }
}

/// The complete classifier table, preserving identifiers rather than Debug
/// text.
#[repr(transparent)]
struct Types<'graph>(&'graph alloc::collections::BTreeMap<TypeId, Type>);
impl Serialize for Types<'_>
{
    /// Present the complete classifier vocabulary.
    ///
    /// # Specification
    /// - ensures: presents every classifier address and constructor, without
    ///   renumbering.
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
        for (id, ty) in self.0 {
            sequence.serialize_element(&(id.0, TypeImage(*ty)))?;
        }
        sequence.end()
    }
}

impl Serialize for Head
{
    /// Present a term constructor and every rigid payload.
    ///
    /// # Specification
    /// - ensures: preserves literal, binder, classifier, model and point
    ///   identities.
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
        match *self {
            | Self::Variable(Index(index)) => ("variable", index).serialize(serializer),
            | Self::OuterNatural(Natural(value)) => ("outer-natural", value).serialize(serializer),
            | Self::InnerNatural(model, Natural(value)) => {
                ("inner-natural", model.0, value).serialize(serializer)
            },
            | Self::Code(ty) => ("code", ty.0).serialize(serializer),
            | Self::Lambda(ty) => ("lambda", ty.0).serialize(serializer),
            | Self::Eliminate(ty) => ("eliminate", ty.0).serialize(serializer),
            | Self::Point(point) => ("point", usize::from(point)).serialize(serializer),
            | Self::Apply => "apply".serialize(serializer),
            | Self::Multiply => "multiply".serialize(serializer),
            | Self::Quote => "quote".serialize(serializer),
            | Self::Splice => "splice".serialize(serializer),
            | Self::Iterate => "iterate".serialize(serializer),
            | Self::Predecessor => "pred".serialize(serializer),
        }
    }
}

impl Serialize for Graph
{
    /// Present semantic graph data, excluding runtime indexes.
    ///
    /// # Specification
    /// - ensures: presents all classifier definitions and flat syntax nodes.
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
        (Types(&self.types), &self.nodes).serialize(serializer)
    }
}
