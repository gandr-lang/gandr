//! Temporary access: a held value, the access that lends a place of it to a
//! view in a mode, the view's two eliminators, and the hold's end at a
//! consuming read.
//!
//! # The forms
//!
//! |form|written|binds|
//! |---|---|---|
//! |hold|`hold x = v; t`|`x`, a linear slot holding `v`, over `t`|
//! |hold at grade one|`hold[1] x = v; t`|`x`, a linear slot holding `v`, never copied, over `t`|
//! |access|`access x as w { t } unwind { u }`|the view `w`, a linear slot, over `t`|
//! |shared access|`access shared x as w { t }`|the view `w`, a linear slot, over `t`|
//! |access at a place|`access x[i] as w { t } unwind { u }`, `access shared x[i] as w { t }`|the view `w`, a linear slot, over `t`|
//! |resume|`resume(w, v)`|nothing; writes `v` back through `w`|
//! |abort|`abort(w)`|nothing; ends `w` with nothing written|
//! |consume|`s.f(a)`, `f`'s receiver consumed|nothing; moves the value `x` holds out|
//!
//! [`MemoryForm::Hold`] opens a slot of the linear zone `Σ` holding a value at
//! a [`HoldGrade`]: at grade `ω` a read of the slot copies the value it holds
//! now; at grade one the value entered with no other holder and is never
//! copied while held, so a write through an exclusive access of it needs no
//! holder count. [`MemoryForm::Access`] lends a [`Place`] of a held slot to a
//! view for the access's body, in the [`AccessMode`] it names: the held value
//! whole, or the element at an index read where the access stands. Lent
//! exclusively, the held slot is unreadable for the body, the view reads the
//! value at its place, and the body ends the view exactly once, by
//! [`MemoryForm::Resume`] (the new value is written back at the place when the
//! access ends) or by [`MemoryForm::Abort`] (the mode's `unwind` runs when the
//! access ends and the held slot keeps the value it had). Lent shared, the
//! held slot stays readable and is frozen for the body, the view reads the
//! same value, and the view ends with the body: a shared mode has no unwind,
//! and neither eliminator ends a shared view. An index in the linear zone is
//! lent with the place, never consumed by the access. [`MemoryForm::Consume`]
//! moves the value out of a held slot no access lends and returns it: the
//! hold ends there, so the slot is read or lent no more, and the hold's scope
//! closes over a spent slot. A method whose receiver is consumed is called on
//! the value it returns; no other source form writes it. The rules and the
//! refusals are `gandr-core-checker`'s `access` module.
//!
//! One computation former has the five forms as its cases, and every
//! resident is named by its linear de Bruijn index, so an access of something
//! that is not held, or an eliminator of something that is not a view,
//! cannot be written as a value. The unwind is a child of the exclusive mode
//! alone, so a shared access with an unwind cannot be written either.
//!
//! # Binders
//!
//! A hold's body and an access's body each stand under one linear binder,
//! the held slot and the view; every other child, an access's index among
//! them, stands where the form stands. No case binds in the intuitionistic
//! zone, so a rewrite of the intuitionistic indices passes through a memory
//! form unchanged.

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::Binders;
use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::ValueId;
use crate::session::ChildOrder;

quenchant_shape::reason_enum! {
    /// Why a memory form names no resident.
    pub mod resident {
        /// The reason a memory form names no linear slot of its own.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A hold binds its slot rather than naming one.
            Hold,
        }
    }
}

/// The mode an access lends its held slot in, with the one child a mode
/// carries: the unwind of an exclusive access. `AccessMode<()>` is the mode
/// alone.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AccessMode<C = ComputationId>
{
    /// The view is the one way to the held value for the body: the held slot
    /// is unreadable while lent, the body ends the view by `resume` or
    /// `abort`, and `unwind`, where the access stands, runs when an abort
    /// ends it.
    Exclusive
    {
        /// The unwind, where the access stands.
        unwind: C,
    },
    /// The view reads the held value, which stays readable and frozen for the
    /// body; the view ends with the body, nothing written back.
    Shared,
}

impl<C> AccessMode<C>
{
    /// The mode with its child erased.
    ///
    /// # Specification
    /// - ensures: [`AccessMode::Exclusive`] for an exclusive mode, whatever its
    ///   unwind, and [`AccessMode::Shared`] for a shared one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an exclusive access and a shared one name their own
    ///   modes.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| matches!((self, ret), (&Self::Exclusive { .. }, AccessMode::Exclusive { .. }) | (&Self::Shared, AccessMode::Shared)))]
    #[inline]
    #[must_use]
    pub const fn mode(&self) -> AccessMode<()>
    {
        match *self {
            Self::Exclusive { .. } => AccessMode::Exclusive { unwind: () },
            Self::Shared => AccessMode::Shared,
        }
    }
}

/// Where in its held slot an access lends: the held value whole, or the
/// element at an index. `Place<()>` is the place's shape alone.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Place<V = ValueId>
{
    /// The held value whole.
    Whole,
    /// The element of the held value at `index`, read where the access
    /// stands.
    At
    {
        /// The index: a plain value, or a linear resident the access lends
        /// with the place for its body.
        index: V,
    },
}

impl<V> Place<V>
{
    /// The place with its index erased.
    ///
    /// # Specification
    /// - ensures: [`Place::Whole`] for the whole value, and [`Place::At`] for
    ///   an index, whatever it is.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an access at an index and one of the whole value name
    ///   their own places.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| matches!((self, ret), (&Self::Whole, Place::Whole) | (&Self::At { .. }, Place::At { .. })))]
    #[inline]
    #[must_use]
    pub const fn shape(&self) -> Place<()>
    {
        match *self {
            Self::Whole => Place::Whole,
            Self::At { .. } => Place::At { index: () },
        }
    }
}

/// How many holders a held value may have while it is held.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HoldGrade
{
    /// Grade `ω`: a read of the slot copies the value it holds.
    #[default]
    Many,
    /// Grade one: the value entered with no other holder and is never copied
    /// while held.
    One,
}

/// The case of a memory form.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MemoryKind
{
    /// `hold x = v; t` or `hold[1] x = v; t`.
    Hold,
    /// `access x as w { t } unwind { u }` or `access shared x as w { t }`.
    Access,
    /// `resume(w, v)`.
    Resume,
    /// `abort(w)`.
    Abort,
    /// The hold's end at a consuming read.
    Consume,
}

/// A memory form: one computation former whose cases hold a value, access a
/// held value through a view, end a view, or move a held value out.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum MemoryForm<V = ValueId, C = ComputationId>
{
    /// `hold x = v; t` or `hold[1] x = v; t`: `body` runs with `x`, a linear
    /// slot holding `value` at `grade`.
    Hold
    {
        /// The value held, read where the hold stands.
        value: V,
        /// The scope of the held slot, under its linear binder.
        body: C,
        /// How many holders the value may have while held.
        grade: HoldGrade,
    },
    /// `access x as w { t } unwind { u }`, `access shared x as w { t }`, or
    /// either at an index, `x[i]`: `body` runs with the view `w` of `place`
    /// in the held slot `held`, under the view's linear binder, lent in
    /// `mode`.
    Access
    {
        /// The mode the slot is lent in, with an exclusive access's unwind.
        mode: AccessMode<C>,
        /// The held slot lent, a linear index.
        held: DeBruijnIndex,
        /// The place of the held value lent, with its index.
        place: Place<V>,
        /// The body, under the view's linear binder.
        body: C,
    },
    /// `resume(w, v)`: end the view `view`, writing `value` back, returning
    /// the unit.
    Resume
    {
        /// The view, a linear index.
        view: DeBruijnIndex,
        /// The value written back.
        value: V,
    },
    /// `abort(w)`: end the view `view` with nothing written, returning the
    /// unit.
    Abort
    {
        /// The view, a linear index.
        view: DeBruijnIndex,
    },
    /// The receiver of a consumed method call: move the value the held slot
    /// `held` holds out, ending the hold, and return it.
    Consume
    {
        /// The held slot, a linear index.
        held: DeBruijnIndex,
    },
}

/// The computation children of a form beside the binders each sits under,
/// as [`MemoryForm::scoped`] yields them: at most two.
pub type Scoped<C> =
    core::iter::Chain<core::option::IntoIter<(C, Binders)>, core::option::IntoIter<(C, Binders)>>;

impl<V: Copy, C: Copy> MemoryForm<V, C>
{
    /// The case the form is.
    ///
    /// # Specification
    /// - ensures: each case names its own kind.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every case's kind is asserted.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| matches!((self, ret),
        (&Self::Hold { .. }, MemoryKind::Hold) | (&Self::Access { .. }, MemoryKind::Access)
        | (&Self::Resume { .. }, MemoryKind::Resume) | (&Self::Abort { .. }, MemoryKind::Abort)
        | (&Self::Consume { .. }, MemoryKind::Consume)))]
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> MemoryKind
    {
        match *self {
            Self::Hold { .. } => MemoryKind::Hold,
            Self::Access { .. } => MemoryKind::Access,
            Self::Resume { .. } => MemoryKind::Resume,
            Self::Abort { .. } => MemoryKind::Abort,
            Self::Consume { .. } => MemoryKind::Consume,
        }
    }

    /// The linear slot the form names where it stands: the held slot an
    /// access lends or a consuming read ends, the view an eliminator ends.
    ///
    /// # Specification
    /// - ensures: the linear index every case but a hold names.
    /// - provides: [`resident::Absent::Hold`] for a hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every case's resident and the hold's absence are
    ///   asserted.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| matches!(*self, Self::Hold { .. }) == matches!(ret, Maybe::Absent(_)))]
    #[inline]
    pub const fn resident(&self) -> Maybe<DeBruijnIndex, resident::Absent>
    {
        match *self {
            Self::Access { held: index, .. }
            | Self::Consume { held: index }
            | Self::Resume { view: index, .. }
            | Self::Abort { view: index } => Maybe::Present(index),
            Self::Hold { .. } => Maybe::Absent(resident::Absent::Hold),
        }
    }

    /// The value children: the value a hold holds or a resume writes back,
    /// and an access's index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = V> + '_
    {
        match *self {
            Self::Hold { value, .. }
            | Self::Resume { value, .. }
            | Self::Access {
                place: Place::At { index: value },
                ..
            } => Some(value),
            Self::Access {
                place: Place::Whole,
                ..
            }
            | Self::Abort { .. }
            | Self::Consume { .. } => None,
        }
        .into_iter()
    }

    /// The computation children in canonical order, each beside the linear
    /// binders the form opens over it: a hold's body and an access's body
    /// under one, an exclusive access's unwind under none.
    ///
    /// # Specification
    /// - ensures: a hold yields its body under one binder; an access its body
    ///   under one, then, when exclusive, its unwind under none; an eliminator
    ///   and a consuming read nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an exclusive access yields its body before its
    ///   unwind, each with its own binder count, and a shared one its body
    ///   alone.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| ret.clone().count() == match *self {
        | Self::Hold { .. } | Self::Access { mode: AccessMode::Shared, .. } => 1_usize,
        | Self::Access { mode: AccessMode::Exclusive { .. }, .. } => 2_usize,
        | Self::Resume { .. } | Self::Abort { .. } | Self::Consume { .. } => 0_usize,
    })]
    #[inline]
    pub fn scoped(&self) -> Scoped<C>
    {
        let (first, second) = match *self {
            Self::Hold { body, .. }
            | Self::Access {
                mode: AccessMode::Shared,
                body,
                ..
            } => (Some((body, Binders::ONE)), None),
            Self::Access {
                mode: AccessMode::Exclusive { unwind },
                body,
                ..
            } => (Some((body, Binders::ONE)), Some((unwind, Binders::NONE))),
            Self::Resume { .. } | Self::Abort { .. } | Self::Consume { .. } => (None, None),
        };
        first.into_iter().chain(second)
    }

    /// The computation children in canonical order: a hold's body, an
    /// access's body then an exclusive access's unwind.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computations(&self) -> impl DoubleEndedIterator<Item = C> + '_
    {
        self.scoped().map(|(child, _)| child)
    }

    /// The form with every child erased: its case, the slot it names, a
    /// hold's grade, an access's mode and whether its place is indexed, which
    /// is what two forms must share to be the same former.
    ///
    /// # Specification
    /// - ensures: the form with every child replaced by the unit, kept at its
    ///   position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two resumes of one view differ in no shape, two
    ///   resumes of different views do, an exclusive access and a shared one of
    ///   one slot do, and so do an access of the whole value and one at an
    ///   index.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| ret.kind() == self.kind() && ret.resident() == self.resident())]
    #[inline]
    #[must_use]
    pub fn shape(&self) -> MemoryForm<(), ()>
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
    /// - ensures: the case, the slot it names, a hold's grade, an access's mode
    ///   and its place's shape are kept; each child is replaced by its image at
    ///   its own position; [`ChildOrder::Forward`] visits a hold's value before
    ///   its body, an access's index before its body and its body before an
    ///   exclusive access's unwind, and a resume's value, and
    ///   [`ChildOrder::Reverse`] exactly the reverse.
    /// - fails: propagates the first error a map returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error of a map.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold mapped in reverse visits its body before its
    ///   value, across families, and keeps each image at its own position; an
    ///   access at an index maps its index before its body forward and after it
    ///   in reverse.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped| match (self, mapped) {
        | (&Self::Access { held: a, mode: ref before, place: ref was, .. }, &MemoryForm::Access { held: b, mode: ref after, place: ref now, .. }) =>
            a == b && before.mode() == after.mode() && was.shape() == now.shape(),
        | (&Self::Resume { view: a, .. }, &MemoryForm::Resume { view: b, .. })
        | (&Self::Abort { view: a }, &MemoryForm::Abort { view: b })
        | (&Self::Consume { held: a }, &MemoryForm::Consume { held: b }) => a == b,
        | (&Self::Hold { grade: a, .. }, &MemoryForm::Hold { grade: b, .. }) => a == b,
        | _ => false,
    }))]
    #[inline]
    pub fn try_map<S, V2, C2, E, Values, Computations>(
        &self,
        order: ChildOrder,
        state: &mut S,
        mut value: Values,
        mut computation: Computations,
    ) -> Result<MemoryForm<V2, C2>, E>
    where
        Values: FnMut(&mut S, V) -> Result<V2, E>,
        Computations: FnMut(&mut S, C) -> Result<C2, E>,
    {
        Ok(match *self {
            Self::Hold {
                value: held,
                body,
                grade,
            } => match order {
                ChildOrder::Forward => {
                    let held = value(state, held)?;
                    MemoryForm::Hold {
                        value: held,
                        body: computation(state, body)?,
                        grade,
                    }
                },
                ChildOrder::Reverse => {
                    let body = computation(state, body)?;
                    MemoryForm::Hold {
                        value: value(state, held)?,
                        body,
                        grade,
                    }
                },
            },
            Self::Access {
                mode,
                held,
                place,
                body,
            } => match order {
                ChildOrder::Forward => {
                    let place = match place {
                        Place::Whole => Place::Whole,
                        Place::At { index } => Place::At {
                            index: value(state, index)?,
                        },
                    };
                    let body = computation(state, body)?;
                    let mode = match mode {
                        AccessMode::Shared => AccessMode::Shared,
                        AccessMode::Exclusive { unwind } => AccessMode::Exclusive {
                            unwind: computation(state, unwind)?,
                        },
                    };
                    MemoryForm::Access {
                        mode,
                        held,
                        place,
                        body,
                    }
                },
                ChildOrder::Reverse => {
                    let mode = match mode {
                        AccessMode::Shared => AccessMode::Shared,
                        AccessMode::Exclusive { unwind } => AccessMode::Exclusive {
                            unwind: computation(state, unwind)?,
                        },
                    };
                    let body = computation(state, body)?;
                    let place = match place {
                        Place::Whole => Place::Whole,
                        Place::At { index } => Place::At {
                            index: value(state, index)?,
                        },
                    };
                    MemoryForm::Access {
                        mode,
                        held,
                        place,
                        body,
                    }
                },
            },
            Self::Resume {
                view,
                value: written,
            } => MemoryForm::Resume {
                view,
                value: value(state, written)?,
            },
            Self::Abort { view } => MemoryForm::Abort { view },
            Self::Consume { held } => MemoryForm::Consume { held },
        })
    }
}

impl CoreArena
{
    /// Mint the memory form `form`.
    ///
    /// # Specification
    /// - requires: every child of `form` resolves in this arena.
    /// - ensures: the node is `form` as given.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted access reads back with its mode, slot, body
    ///   and unwind.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(requires: form.values().all(|value| self.value(value).is_some())
            && form.computations().all(|computation| self.computation(computation).is_some()),
        ensures: |ret| matches!(self.computation(ret), Some(Computation::Memory(_))))]
    #[inline]
    pub fn computation_memory(
        &mut self,
        form: MemoryForm,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Memory(form))
    }
}

#[cfg(test)]
mod tests;
