//! Schema maps and the pull-back of a store along one.
//!
//! A [`SchemaMap`] `F: C → D` sends each object of `C` to an object of `D`,
//! each arrow `f: a → b` of `C` to a path of `D` from `F(a)` to `F(b)`, and
//! each attribute `α: a → T` of `C` to a path of `D` from `F(a)` followed by
//! an attribute of `D` whose type has `T`'s name. It must send each equation
//! of `C` to paths that every store of `D` agrees on.
//! [`Store::pull_back`](crate::Store::pull_back) is the data migration
//! `Δ_F`: it turns a store of `D` into a store of `C`
//! whose table at `a` is `D`'s table at `F(a)`, with each column computed by
//! following its image path.
//!
//! # What the pull-back preserves
//!
//! Keys: a part of `C` at `a` is the part of `D` at `F(a)` under the same
//! key, and each table keeps its counter, so a key minted after migration is
//! never one minted before it. Referential integrity: a followed path from a
//! live part reaches a live part. Equations: the map's check below admits
//! only images that hold in every store of `D`, so the pulled-back store
//! needs no equation check of its own; [`Store::audit`](crate::Store::audit)
//! confirms it on the witness fixture rather than as a step.
//!
//! **Choice.** The equation check is sound and incomplete: the two images of
//! an equation of `C` must be the same path of `D`, or must differ by one
//! application of one equation of `D` in context — `u·L·v` against `u·R·v`
//! with `L = R` an equation of `D` leaving the object `u` reaches. Each
//! admitted image holds wherever `D`'s equations hold, which is everywhere
//! in a store of `D`. **Alternatives.** Deciding equality of paths under
//! `D`'s equations is the word problem for a finitely presented category,
//! undecidable in general; a bounded rewrite search or a Knuth–Bendix
//! completion would admit more maps at a cost and a failure mode this slice
//! does not need. Checking the equations on each pulled-back store instead
//! would turn a property of the map into a per-store cost. **Reversal.** A
//! map a consumer needs that holds only by two or more rewrite steps.
//!
//! The pushout `Σ_F` and the right adjoint `Π_F` are not provided.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::schema::ArrowId;
use crate::schema::AttributeId;
use crate::schema::ElementKind;
use crate::schema::Name;
use crate::schema::ObjectId;
use crate::schema::Ordinal;
use crate::schema::Path;
use crate::schema::Schema;
use crate::schema::SchemaError;

/// Every way a schema map is refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MapError
{
    /// A name does not resolve in the schema it belongs to.
    Schema(SchemaError),
    /// An element of the source schema is not mapped.
    Unmapped
    {
        /// Its kind.
        kind: ElementKind,
        /// Its name.
        name: Name,
    },
    /// An image path takes an arrow out of an object it is not at.
    NotComposable
    {
        /// The source element whose image it is.
        element: Name,
        /// The arrow of the target schema that does not compose.
        arrow: Name,
        /// The target object the path had reached.
        at: Name,
    },
    /// An image path ends at another object than the map requires.
    WrongEnd
    {
        /// The source element whose image it is.
        element: Name,
        /// The target object the image must reach.
        expected: Name,
        /// The target object it reaches.
        found: Name,
    },
    /// An attribute's image has a type of another name.
    AttributeType
    {
        /// The source attribute.
        attribute: Name,
        /// Its type's name.
        expected: Name,
        /// The image's type's name.
        found: Name,
    },
    /// An equation's images are not shown equal in the target schema.
    EquationNotPreserved
    {
        /// The source equation.
        equation: Name,
    },
}

impl fmt::Display for MapError
{
    /// Writes the refusal with the names it carries.
    ///
    /// # Specification
    /// - ensures: writes one sentence naming the refusal's kind and every name
    ///   it carries.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the attribute-type refusal renders both type names.
    /// - witness: `tests::migrate::a_map_onto_another_attribute_type_is_refused`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Schema(ref error) => write!(f, "schema map: {error}"),
            Self::Unmapped { kind, ref name } => {
                write!(f, "schema map: {kind} `{name}` is not mapped")
            },
            Self::NotComposable {
                ref element,
                ref arrow,
                ref at,
            } => write!(
                f,
                "schema map: the image of `{element}` takes `{arrow}` out of `{at}`, where it does not start"
            ),
            Self::WrongEnd {
                ref element,
                ref expected,
                ref found,
            } => write!(
                f,
                "schema map: the image of `{element}` ends at `{found}`, not `{expected}`"
            ),
            Self::AttributeType {
                ref attribute,
                ref expected,
                ref found,
            } => write!(
                f,
                "schema map: `{attribute}` has type `{expected}` but its image has type `{found}`"
            ),
            Self::EquationNotPreserved { ref equation } => {
                write!(
                    f,
                    "schema map: the images of equation `{equation}` are not shown equal in the target schema"
                )
            },
        }
    }
}

impl core::error::Error for MapError
{
}

impl From<SchemaError> for MapError
{
    /// Carries a schema lookup's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: SchemaError) -> Self
    {
        Self::Schema(error)
    }
}

/// A schema map being stated by names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MapBuilder
{
    /// The source schema.
    source: Schema,
    /// The target schema.
    target: Schema,
    /// Each source object's image.
    objects: BTreeMap<Name, Name>,
    /// Each source arrow's image path.
    arrows: BTreeMap<Name, Vec<Name>>,
    /// Each source attribute's image path and attribute.
    attributes: BTreeMap<Name, AttributeImage>,
}

/// An attribute's image, by names.
#[derive(Clone, Debug, Eq, PartialEq)]
struct AttributeImage
{
    /// The path of target arrows.
    path: Vec<Name>,
    /// The target attribute at its end.
    attribute: Name,
}

impl MapBuilder
{
    /// Maps a source object to a target object.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn object<N, M>(
        mut self,
        from: N,
        to: M,
    ) -> Self
    where
        N: Into<Name>,
        M: Into<Name>,
    {
        self.objects.insert(from.into(), to.into());
        self
    }

    /// Maps a source arrow to a path of target arrows, first applied first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arrow<N, I, M>(
        mut self,
        from: N,
        path: I,
    ) -> Self
    where
        N: Into<Name>,
        I: IntoIterator<Item = M>,
        M: Into<Name>,
    {
        self.arrows
            .insert(from.into(), path.into_iter().map(Into::into).collect());
        self
    }

    /// Maps a source attribute to a path of target arrows and a target
    /// attribute at its end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn attribute<N, I, M, A>(
        mut self,
        from: N,
        path: I,
        to: A,
    ) -> Self
    where
        N: Into<Name>,
        I: IntoIterator<Item = M>,
        M: Into<Name>,
        A: Into<Name>,
    {
        self.attributes.insert(from.into(), AttributeImage {
            path: path.into_iter().map(Into::into).collect(),
            attribute: to.into(),
        });
        self
    }

    /// Checks the map and fixes it.
    ///
    /// # Specification
    /// - ensures: on success every source object, arrow and attribute has an
    ///   image, each arrow's image runs between its ends' images, each
    ///   attribute's image ends at an attribute of the same type name, and each
    ///   equation's images are equal or differ by one target equation in
    ///   context.
    /// - fails: [`MapError::Schema`] for a name that does not resolve,
    ///   [`MapError::Unmapped`], [`MapError::NotComposable`],
    ///   [`MapError::WrongEnd`], [`MapError::AttributeType`], and
    ///   [`MapError::EquationNotPreserved`], each naming the element, in
    ///   object, arrow, attribute then equation order.
    /// - panics: none.
    /// - executable: none — the postcondition is the whole check; the witnesses
    ///   drive each refusal.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — a view of the keyed schema whose equation holds by
    ///   one target equation is admitted; one whose image breaks its equation,
    ///   one with a path that does not compose, and one onto another attribute
    ///   type are each refused by name.
    /// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
    /// - witness: `tests::migrate::a_map_that_breaks_an_equation_is_refused`
    /// - witness: `tests::migrate::a_map_that_does_not_compose_is_refused_by_name`
    /// - witness: `tests::migrate::a_map_onto_another_attribute_type_is_refused`
    #[inline]
    pub fn build(self) -> Result<SchemaMap, MapError>
    {
        let source = &self.source;
        let target = &self.target;

        let mut objects = Vec::with_capacity(source.objects().len());
        for object in source.objects() {
            let name = source.object_name(object)?;
            let image = self.objects.get(name).ok_or_else(|| MapError::Unmapped {
                kind: ElementKind::Object,
                name: name.clone(),
            })?;
            objects.push(target.object(image.clone())?);
        }

        let mut arrows = Vec::with_capacity(source.arrows().len());
        for arrow in source.arrows() {
            let spec = source.arrow_at(arrow)?;
            let names = self
                .arrows
                .get(spec.name())
                .ok_or_else(|| MapError::Unmapped {
                    kind: ElementKind::Arrow,
                    name: spec.name().clone(),
                })?;
            let start = image_of(&objects, spec.source())?;
            let end = image_of(&objects, spec.target())?;
            let path = compose(target, spec.name(), start, names)?;
            ensure_end(target, spec.name(), &path, end)?;
            arrows.push(path);
        }

        let mut attributes = Vec::with_capacity(source.attributes().len());
        for attribute in source.attributes() {
            let spec = source.attribute_at(attribute)?;
            let image = self
                .attributes
                .get(spec.name())
                .ok_or_else(|| MapError::Unmapped {
                    kind: ElementKind::Attribute,
                    name: spec.name().clone(),
                })?;
            let start = image_of(&objects, spec.object())?;
            let path = compose(target, spec.name(), start, &image.path)?;
            let landing = target.attribute(image.attribute.clone())?;
            let landing_spec = target.attribute_at(landing)?;
            ensure_end(target, spec.name(), &path, landing_spec.object())?;
            let expected = source.attribute_type_name(spec.ty())?;
            let found = target.attribute_type_name(landing_spec.ty())?;
            if expected != found {
                return Err(MapError::AttributeType {
                    attribute: spec.name().clone(),
                    expected: expected.clone(),
                    found: found.clone(),
                });
            }
            attributes.push((path, landing));
        }

        for equation in source.equations() {
            let spec = source.equation_at(equation)?;
            let left = image_arrows(&arrows, spec.left())?;
            let right = image_arrows(&arrows, spec.right())?;
            let start = image_of(&objects, spec.left().start())?;
            let shown = shown_equal(target, start, &left, &right)?;
            if shown == ShownEqual::NotShown {
                return Err(MapError::EquationNotPreserved {
                    equation: spec.name().clone(),
                });
            }
        }

        Ok(SchemaMap {
            source: self.source,
            target: self.target,
            objects: objects.into_boxed_slice(),
            arrows: arrows.into_boxed_slice(),
            attributes: attributes.into_boxed_slice(),
        })
    }
}

/// A checked schema map `F: C → D`.
///
/// # Specification
/// - requires: construction through [`MapBuilder::build`].
/// - ensures: every element of the source has an image of the right shape, and
///   every equation of the source holds of its images in every store of the
///   target.
/// - provides: [`Store::pull_back`](crate::store::Store::pull_back).
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a pulled-back keyed store passes the full audit.
/// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SchemaMap
{
    /// The source schema.
    source: Schema,
    /// The target schema.
    target: Schema,
    /// Each source object's image, by ordinal.
    objects: Box<[ObjectId]>,
    /// Each source arrow's image path, by ordinal.
    arrows: Box<[Path]>,
    /// Each source attribute's image path and attribute, by ordinal.
    attributes: Box<[(Path, AttributeId)]>,
}

impl SchemaMap
{
    /// A map from `source` to `target`, stated by names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn builder(
        source: Schema,
        target: Schema,
    ) -> MapBuilder
    {
        MapBuilder {
            source,
            target,
            objects: BTreeMap::new(),
            arrows: BTreeMap::new(),
            attributes: BTreeMap::new(),
        }
    }

    /// The source schema.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> &Schema
    {
        &self.source
    }

    /// The target schema.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> &Schema
    {
        &self.target
    }

    /// A source object's image.
    ///
    /// # Specification
    /// - ensures: on success the target object the map sends it to.
    /// - fails: [`SchemaError::UnknownOrdinal`] for an object outside the
    ///   source.
    /// - panics: none.
    /// - executable: none — the answer is the stored image.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the pulled-back tables are the image tables.
    /// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
    #[inline]
    pub fn object(
        &self,
        object: ObjectId,
    ) -> Result<ObjectId, SchemaError>
    {
        image_of(&self.objects, object)
    }

    /// A source arrow's image path.
    ///
    /// # Specification
    /// - ensures: on success the target path the map sends it to.
    /// - fails: [`SchemaError::UnknownOrdinal`] for an arrow outside the
    ///   source.
    /// - panics: none.
    /// - executable: none — the answer is the stored image.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the pulled-back arrow reads the followed path.
    /// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
    #[inline]
    pub fn arrow(
        &self,
        arrow: ArrowId,
    ) -> Result<&Path, SchemaError>
    {
        self.arrows
            .get(usize::from(arrow))
            .ok_or_else(|| SchemaError::UnknownOrdinal {
                kind: ElementKind::Arrow,
                ordinal: Ordinal(usize::from(arrow)),
            })
    }

    /// A source attribute's image path and attribute.
    ///
    /// # Specification
    /// - ensures: on success the target path and attribute the map sends it to.
    /// - fails: [`SchemaError::UnknownOrdinal`] for an attribute outside the
    ///   source.
    /// - panics: none.
    /// - executable: none — the answer is the stored image.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the pulled-back attribute reads the value at the
    ///   followed path's end.
    /// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
    #[inline]
    pub fn attribute(
        &self,
        attribute: AttributeId,
    ) -> Result<&(Path, AttributeId), SchemaError>
    {
        self.attributes
            .get(usize::from(attribute))
            .ok_or_else(|| SchemaError::UnknownOrdinal {
                kind: ElementKind::Attribute,
                ordinal: Ordinal(usize::from(attribute)),
            })
    }
}

/// An object's image in a list of images.
///
/// # Specification
/// - ensures: on success the image at the object's ordinal.
/// - fails: [`SchemaError::UnknownOrdinal`] past the list.
/// - panics: none.
/// - executable: none — the answer is the stored image.
///
/// # Errors
/// [`SchemaError::UnknownOrdinal`].
///
/// # Adequacy
/// - hypothesis: L2 — the keyed view's objects map to their tables.
/// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
#[inline]
fn image_of(
    objects: &[ObjectId],
    object: ObjectId,
) -> Result<ObjectId, SchemaError>
{
    objects
        .get(usize::from(object))
        .copied()
        .ok_or_else(|| SchemaError::UnknownOrdinal {
            kind: ElementKind::Object,
            ordinal: Ordinal(usize::from(object)),
        })
}

/// Resolves and composes a path of target arrow names.
///
/// # Specification
/// - ensures: on success the path leaves `start` and each arrow leaves the
///   object the path has reached.
/// - fails: [`MapError::Schema`] for an arrow name, and
///   [`MapError::NotComposable`] naming the element, the arrow and the object
///   reached.
/// - panics: none.
/// - executable: none — the composite is the walk itself.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — an image taking `attempt_task` out of `Move` is refused
///   with all three names.
/// - witness: `tests::migrate::a_map_that_does_not_compose_is_refused_by_name`
#[inline]
fn compose(
    target: &Schema,
    element: &Name,
    start: ObjectId,
    names: &[Name],
) -> Result<Path, MapError>
{
    let mut at = start;
    let mut arrows = Vec::with_capacity(names.len());
    for name in names {
        let arrow = target.arrow(name.clone())?;
        let spec = target.arrow_at(arrow)?;
        if spec.source() != at {
            return Err(MapError::NotComposable {
                element: element.clone(),
                arrow: name.clone(),
                at: target.object_name(at)?.clone(),
            });
        }
        at = spec.target();
        arrows.push(arrow);
    }
    Ok(Path::composed(start, at, arrows.into_boxed_slice()))
}

/// Refuses an image path that does not end where the map requires.
///
/// # Specification
/// - ensures: success exactly when the path ends at `end`.
/// - fails: [`MapError::WrongEnd`] naming the element and both objects.
/// - panics: none.
///
/// # Errors
/// [`MapError::WrongEnd`].
///
/// # Adequacy
/// - hypothesis: L3 — an image of `move_task` stopping at `Attempt` is refused
///   with both ends.
/// - witness: `tests::migrate::a_map_that_does_not_compose_is_refused_by_name`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == (path.end() == end))]
fn ensure_end(
    target: &Schema,
    element: &Name,
    path: &Path,
    end: ObjectId,
) -> Result<(), MapError>
{
    if path.end() == end {
        return Ok(());
    }
    Err(MapError::WrongEnd {
        element: element.clone(),
        expected: target.object_name(end)?.clone(),
        found: target.object_name(path.end())?.clone(),
    })
}

/// The target arrows a source path's image is, concatenated.
///
/// # Specification
/// - ensures: on success the images of the path's arrows, in order.
/// - fails: [`SchemaError::UnknownOrdinal`] for an arrow past the images.
/// - panics: none.
/// - executable: none — the answer is the concatenation itself.
///
/// # Errors
/// [`MapError::Schema`].
///
/// # Adequacy
/// - hypothesis: L2 — the keyed view's equation images are the expected one-
///   and three-arrow paths, which the admitted map shows equal.
/// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
#[inline]
fn image_arrows(
    images: &[Path],
    path: &Path,
) -> Result<Vec<ArrowId>, MapError>
{
    let mut arrows = Vec::new();
    for &arrow in path.arrows() {
        let image = images
            .get(usize::from(arrow))
            .ok_or_else(|| SchemaError::UnknownOrdinal {
                kind: ElementKind::Arrow,
                ordinal: Ordinal(usize::from(arrow)),
            })?;
        arrows.extend_from_slice(image.arrows());
    }
    Ok(arrows)
}

/// Whether two target paths from one object are equal, or differ by one
/// target equation in context.
///
/// # Specification
/// - requires: both paths leave `start` and compose.
/// - ensures: true exactly when `left == right`, or some target equation `L =
///   R`, in either orientation, and split `left = u·L·v` with `u` reaching the
///   equation's start make `right == u·R·v`.
/// - fails: [`MapError::Schema`] for an identifier outside the target.
/// - panics: none.
/// - executable: none — the predicate is the search itself.
///
/// # Errors
/// [`MapError::Schema`].
///
/// # Adequacy
/// - hypothesis: L2/L3 — a one-step image is admitted, an image with no step is
///   refused.
/// - witness: `tests::migrate::a_pulled_back_store_satisfies_its_equations_by_construction`
/// - witness: `tests::migrate::a_map_that_breaks_an_equation_is_refused`
#[inline]
fn shown_equal(
    target: &Schema,
    start: ObjectId,
    left: &[ArrowId],
    right: &[ArrowId],
) -> Result<ShownEqual, MapError>
{
    if left == right {
        return Ok(ShownEqual::Equal);
    }
    let mut reached = Vec::with_capacity(left.len().saturating_add(1));
    reached.push(start);
    for &arrow in left {
        reached.push(target.arrow_at(arrow)?.target());
    }
    for equation in target.equations() {
        let spec = target.equation_at(equation)?;
        let sides = [(spec.left(), spec.right()), (spec.right(), spec.left())];
        for (from, to) in sides {
            for (position, &object) in reached.iter().enumerate() {
                if object != from.start() {
                    continue;
                }
                let Some(after) = position.checked_add(from.arrows().len())
                else {
                    continue;
                };
                if left.get(position .. after) != Some(from.arrows()) {
                    continue;
                }
                let (Some(prefix), Some(suffix)) = (left.get(.. position), left.get(after ..))
                else {
                    continue;
                };
                let rewritten = prefix.iter().chain(to.arrows()).chain(suffix);
                if rewritten.eq(right.iter()) {
                    return Ok(ShownEqual::Equal);
                }
            }
        }
    }
    Ok(ShownEqual::NotShown)
}

/// Whether [`shown_equal`] showed two paths equal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ShownEqual
{
    /// Equal, or one equation apart.
    Equal,
    /// Not shown equal; perhaps equal by more steps.
    NotShown,
}
