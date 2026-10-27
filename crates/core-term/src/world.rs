//! Located judgements: the worlds a judgement is meaningful at, the type of a
//! value held at one, the capability to move to one, and the three forms that
//! hold, open and migrate.
//!
//! In the storage picture each world runs its own LAMs and every world
//! reaches one CAM, the location- and content-addressable memories of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`:
//! a location means something at its own world alone, and a value crosses to
//! another by content. Its wall is validity: a judgement decides a crossing,
//! never a digest.
//!
//! A value crosses between worlds only when its type passes two judgements.
//! **Mobile** is authority: nothing the value holds is meaningful only where
//! it was made. **Open** is representation: the value names no location, so
//! its bytes read the same at every world, the precondition of committing it
//! by content. The checker decides both on every former, in
//! `gandr_core_checker::worlds`, and refuses a crossing that fails either by
//! the judgement's own name, `Immobile` or `NotOpen`.
//!
//! # A world is a locus, never a host
//!
//! A world is the place a judgement is meaningful at: typing is located,
//! `⊢_w`, and a hypothesis records the world it was bound at and is usable
//! only there. Which machine or tree a world denotes is the host's binding,
//! made outside the program and outside the checker; the core sees a world as
//! the admission position of the `world w ;` declaration that names it, so two
//! worlds are equal exactly when their declarations are, and a source names
//! each once. [`World::Host`] is the world a run stands at when its entry
//! names none, which no source names.
//!
//! **Choice.** A world is a declaration's position, as an abstract type's atom
//! is. **Alternatives.** Worlds as values of a type, with world variables,
//! which presupposes world identity answered and which no consumer needs yet;
//! a world named by its spelling in the core, which puts a name in a name-free
//! vocabulary. **Reversal.** World identity beyond names or an accessibility
//! relation: the declaration grows a checked body and its position stays.
//!
//! # The two types
//!
//! |former|written|meaning|
//! |---|---|---|
//! |[`WorldType::At`]|`A at w`|a handle to a value of `A` that is meaningful at `w`; usable anywhere, opened only at `w`|
//! |[`WorldType::Capability`]|no surface spelling|`cap_w`: the one-shot authority to migrate to `w`, resident in the linear zone|
//!
//! No term introduces `cap_w`: the checker's entry receives each one as a
//! linear hypothesis, and a migration spends it.
//!
//! # The three forms
//!
//! |form|written|binds|
//! |---|---|---|
//! |[`WorldForm::Hold`]|`hold v`|nothing; returns `v` held at the current world|
//! |[`WorldForm::Leta`]|`leta x = v ; t`|`x`, an intuitionistic hypothesis located at the handle's world, over `t`|
//! |[`WorldForm::Migrate`]|`migrate[w] { t }`|nothing; `t` runs at `w`|
//!
//! **Choice.** One computation former whose cases are the three forms, `hold`
//! among them as a computation returning the handle. **Alternative.** `hold v`
//! as a value former, which the staged record writes and which adds an arm to
//! every value walk for a form whose value reading the checker's nested bridge
//! already gives: `hold v` written where a value is read runs and stands for
//! the handle it returns. **Reversal.** A consumer that needs a held value in
//! a type, where no computation runs.
//!
//! # Binders
//!
//! A `leta`'s body stands under one intuitionistic binder; every other child
//! stands where the form stands. No case binds in the linear zone, so a
//! rewrite of the linear indices passes through a world form unchanged.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: the
//!   per-world LAMs and the one CAM a crossing passes through, and `Open`,
//!   the representation half of a crossing.

use anodized::spec;
use gandr_kernel_term::ConstantIndex;

use crate::Binders;
use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;
use crate::session::ChildOrder;

/// A world: a declared one, by the admission position of its declaration, or
/// the host's unnamed one.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum World
{
    /// The world a run stands at when its entry names none; no source names
    /// it.
    #[default]
    Host,
    /// The world the `world w ;` declaration at this position declares.
    Declared(ConstantIndex),
}

/// A value type that names a world: a handle held at one, or the capability
/// to migrate to one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WorldType<T = ValueTypeId>
{
    /// `A at w`: a value of `inner` meaningful at `world`.
    At
    {
        /// The type of the value held.
        inner: T,
        /// The world the value is meaningful at.
        world: World,
    },
    /// `cap_w`: the one-shot authority to migrate to the world.
    Capability(World),
}

impl<T: Copy> WorldType<T>
{
    /// The world the type names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn world(&self) -> World
    {
        match *self {
            Self::At { world, .. } | Self::Capability(world) => world,
        }
    }

    /// The value-type children: a handle's held type; nothing for a
    /// capability.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn types(&self) -> impl DoubleEndedIterator<Item = T> + '_
    {
        match *self {
            Self::At { inner, .. } => Some(inner),
            Self::Capability(_) => None,
        }
        .into_iter()
    }

    /// The same type over its child's image.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the case and the world are kept; a handle's held type is
    ///   replaced by its image.
    /// - fails: propagates the map's error.
    /// - panics: none.
    ///
    /// # Errors
    /// The map's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handle maps its held type and keeps its world, a
    ///   capability maps nothing.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped| match (*self, mapped) {
        | (Self::At { world: a, .. }, &WorldType::At { world: b, .. })
        | (Self::Capability(a), &WorldType::Capability(b)) => a == b,
        | _ => false,
    }))]
    #[inline]
    pub fn try_map<U, E, Types>(
        &self,
        mut map: Types,
    ) -> Result<WorldType<U>, E>
    where
        Types: FnMut(T) -> Result<U, E>,
    {
        Ok(match *self {
            Self::At { inner, world } => WorldType::At {
                inner: map(inner)?,
                world,
            },
            Self::Capability(world) => WorldType::Capability(world),
        })
    }

    /// The type with its held type erased: its case and its world, which is
    /// what two world types must share to be the same former.
    ///
    /// # Specification
    /// - ensures: the type with its child replaced by the unit, its world kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two handles at one world share a shape whatever they
    ///   hold; a handle and a capability at one world do not.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(ensures: |ret| ret.world() == self.world())]
    #[inline]
    #[must_use]
    pub fn shape(&self) -> WorldType<()>
    {
        match self.try_map(|_| Ok::<_, core::convert::Infallible>(())) {
            Ok(shape) => shape,
            Err(never) => match never {},
        }
    }
}

/// The case of a world form.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WorldKind
{
    /// `hold v`.
    Hold,
    /// `leta x = v ; t`.
    Leta,
    /// `migrate[w] { t }`.
    Migrate,
}

/// A world form: one computation former whose cases hold a value at the
/// current world, open a handle, or migrate to another world.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum WorldForm<V = ValueId, C = ComputationId>
{
    /// `hold v`: return `value` held at the current world.
    Hold
    {
        /// The value held.
        value: V,
    },
    /// `leta x = v ; t`: `body` runs with `x`, the value the handle `value`
    /// holds, bound at the handle's world.
    Leta
    {
        /// The handle opened, read where the form stands.
        value: V,
        /// The scope of the opened value, under one intuitionistic binder.
        body: C,
    },
    /// `migrate[w] { t }`: `body` runs at `world`.
    Migrate
    {
        /// The world migrated to.
        world: World,
        /// The computation run there.
        body: C,
    },
}

impl<V: Copy, C: Copy> WorldForm<V, C>
{
    /// The case the form is.
    ///
    /// # Specification
    /// - ensures: each case names its own kind.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every case's kind is asserted.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(ensures: |ret| matches!((self, ret),
        (&Self::Hold { .. }, WorldKind::Hold) | (&Self::Leta { .. }, WorldKind::Leta)
        | (&Self::Migrate { .. }, WorldKind::Migrate)))]
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> WorldKind
    {
        match *self {
            Self::Hold { .. } => WorldKind::Hold,
            Self::Leta { .. } => WorldKind::Leta,
            Self::Migrate { .. } => WorldKind::Migrate,
        }
    }

    /// The value children: the value a hold holds or the handle a `leta`
    /// opens.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = V> + '_
    {
        match *self {
            Self::Hold { value } | Self::Leta { value, .. } => Some(value),
            Self::Migrate { .. } => None,
        }
        .into_iter()
    }

    /// The computation child beside the intuitionistic binders the form opens
    /// over it: a `leta`'s body under one, a migration's body under none.
    ///
    /// # Specification
    /// - ensures: a `leta` yields its body under one binder, a migration its
    ///   body under none, a hold nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each case's child and binder count are asserted.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(ensures: |ret| ret.clone().count() == match *self {
        | Self::Hold { .. } => 0_usize,
        | Self::Leta { .. } | Self::Migrate { .. } => 1_usize,
    })]
    #[inline]
    pub fn scoped(&self) -> core::option::IntoIter<(C, Binders)>
    {
        match *self {
            Self::Hold { .. } => None,
            Self::Leta { body, .. } => Some((body, Binders::ONE)),
            Self::Migrate { body, .. } => Some((body, Binders::NONE)),
        }
        .into_iter()
    }

    /// The computation children: a `leta`'s or a migration's body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computations(&self) -> impl DoubleEndedIterator<Item = C> + '_
    {
        self.scoped().map(|(child, _)| child)
    }

    /// The form with every child erased: its case and the world it names,
    /// which is what two forms must share to be the same former.
    ///
    /// # Specification
    /// - ensures: the form with every child replaced by the unit.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two migrations to one world share a shape, two to
    ///   different worlds do not.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(ensures: |ret| ret.kind() == self.kind())]
    #[inline]
    #[must_use]
    pub fn shape(&self) -> WorldForm<(), ()>
    {
        match self.try_map(
            ChildOrder::Forward,
            &mut (),
            |&mut (), _| Ok::<_, core::convert::Infallible>(()),
            |&mut (), _| Ok(()),
        ) {
            Ok(shape) => shape,
            Err(never) => match never {},
        }
    }

    /// The same form over its children's images, the maps sharing `state` so
    /// a walk can feed them from one result stack.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the case and the world are kept; each child is replaced by
    ///   its image at its own position; [`ChildOrder::Forward`] visits a
    ///   `leta`'s value before its body, and [`ChildOrder::Reverse`] the
    ///   reverse.
    /// - fails: propagates the first error a map returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error of a map.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `leta` mapped in reverse visits its body before its
    ///   value and keeps each image at its own position; a migration keeps its
    ///   world.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped| match (self, mapped) {
        | (&Self::Migrate { world: a, .. }, &WorldForm::Migrate { world: b, .. }) => a == b,
        | (&Self::Hold { .. }, &WorldForm::Hold { .. }) | (&Self::Leta { .. }, &WorldForm::Leta { .. }) => true,
        | _ => false,
    }))]
    #[inline]
    pub fn try_map<S, V2, C2, E, Values, Computations>(
        &self,
        order: ChildOrder,
        state: &mut S,
        mut value: Values,
        mut computation: Computations,
    ) -> Result<WorldForm<V2, C2>, E>
    where
        Values: FnMut(&mut S, V) -> Result<V2, E>,
        Computations: FnMut(&mut S, C) -> Result<C2, E>,
    {
        Ok(match *self {
            Self::Hold { value: held } => WorldForm::Hold {
                value: value(state, held)?,
            },
            Self::Leta {
                value: opened,
                body,
            } => match order {
                ChildOrder::Forward => {
                    let opened = value(state, opened)?;
                    WorldForm::Leta {
                        value: opened,
                        body: computation(state, body)?,
                    }
                },
                ChildOrder::Reverse => {
                    let body = computation(state, body)?;
                    WorldForm::Leta {
                        value: value(state, opened)?,
                        body,
                    }
                },
            },
            Self::Migrate { world, body } => WorldForm::Migrate {
                world,
                body: computation(state, body)?,
            },
        })
    }
}

impl CoreArena
{
    /// Mint the world form `form`.
    ///
    /// # Specification
    /// - requires: every child of `form` resolves in this arena.
    /// - ensures: the node is `form` as given.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted `leta` reads back with its value and body.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(requires: form.values().all(|value| self.value(value).is_some())
            && form.computations().all(|computation| self.computation(computation).is_some()),
        ensures: |ret| matches!(self.computation(ret), Some(Computation::World(_))))]
    #[inline]
    pub fn computation_world(
        &mut self,
        form: WorldForm,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::World(form))
    }

    /// Mint the world type `ty`.
    ///
    /// # Specification
    /// - requires: a handle's held type resolves in this arena.
    /// - ensures: the node is `ty` as given.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted handle reads back with its held type and
    ///   world.
    /// - witness: `world::tests::forms_name_their_children_and_binders`
    #[spec(requires: ty.types().all(|inner| self.value_type(inner).is_some()),
        ensures: |ret| matches!(self.value_type(ret), Some(ValueType::World(_))))]
    #[inline]
    pub fn value_type_world(
        &mut self,
        ty: WorldType,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::World(ty))
    }
}

#[cfg(test)]
mod tests;
