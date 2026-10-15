//! Temporary access: a value held exclusively, the access that lends it to a
//! view, and the view's two eliminators.
//!
//! # The forms
//!
//! |form|written|binds|
//! |---|---|---|
//! |hold|`hold x = v; t`|`x`, a linear slot holding `v`, over `t`|
//! |access|`access x as w { t } unwind { u }`|the view `w`, a linear slot, over `t`|
//! |resume|`resume(w, v)`|nothing; writes `v` back through `w`|
//! |abort|`abort(w)`|nothing; ends `w` with nothing written|
//!
//! [`MemoryForm::Hold`] opens a slot of the linear zone `Σ` holding a value;
//! a read of the slot copies the value it holds now. [`MemoryForm::Access`]
//! lends a held slot to a view for the access's body: the held slot is
//! unreadable while lent, the view reads the value it was lent, and the body
//! ends the view exactly once, by [`MemoryForm::Resume`] (the new value is
//! written back into the held slot when the access ends) or by
//! [`MemoryForm::Abort`] (the access's `unwind` runs when the access ends and
//! the held slot keeps the value it had). The rules, the refusals and the
//! decisions behind them are `gandr-core-checker`'s `access` module.
//!
//! **Choice.** One computation former whose cases are the four forms, every
//! resident named by its linear de Bruijn index, so an access of something
//! that is not held, or an eliminator of something that is not a view,
//! cannot be written as a value. **Alternative.** A computation former per
//! form, which adds an arm per form to every walk, as the session actions
//! decided before it.
//!
//! # Binders
//!
//! A hold's body and an access's body each stand under one linear binder,
//! the held slot and the view; every other child stands where the form
//! stands. No case binds in the intuitionistic zone, so a rewrite of the
//! intuitionistic indices passes through a memory form unchanged.

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

/// The case of a memory form.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MemoryKind
{
    /// `hold x = v; t`.
    Hold,
    /// `access x as w { t } unwind { u }`.
    Access,
    /// `resume(w, v)`.
    Resume,
    /// `abort(w)`.
    Abort,
}

/// A memory form: one computation former whose cases hold a value, access a
/// held value through a view, or end a view.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum MemoryForm<V = ValueId, C = ComputationId>
{
    /// `hold x = v; t`: `body` runs with `x`, a linear slot holding `value`.
    Hold
    {
        /// The value held, read where the hold stands.
        value: V,
        /// The scope of the held slot, under its linear binder.
        body: C,
    },
    /// `access x as w { t } unwind { u }`: `body` runs with the view `w` of
    /// the held slot `held`, under the view's linear binder; `unwind` runs
    /// when an abort ends the view.
    Access
    {
        /// The held slot lent, a linear index.
        held: DeBruijnIndex,
        /// The body, under the view's linear binder.
        body: C,
        /// The unwind, where the access stands.
        unwind: C,
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
        | (&Self::Resume { .. }, MemoryKind::Resume) | (&Self::Abort { .. }, MemoryKind::Abort)))]
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> MemoryKind
    {
        match *self {
            Self::Hold { .. } => MemoryKind::Hold,
            Self::Access { .. } => MemoryKind::Access,
            Self::Resume { .. } => MemoryKind::Resume,
            Self::Abort { .. } => MemoryKind::Abort,
        }
    }

    /// The linear slot the form names where it stands: the held slot an
    /// access lends, the view an eliminator ends.
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
            | Self::Resume { view: index, .. }
            | Self::Abort { view: index } => Maybe::Present(index),
            Self::Hold { .. } => Maybe::Absent(resident::Absent::Hold),
        }
    }

    /// The value children: the value a hold holds or a resume writes back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = V> + '_
    {
        match *self {
            Self::Hold { value, .. } | Self::Resume { value, .. } => Some(value),
            Self::Access { .. } | Self::Abort { .. } => None,
        }
        .into_iter()
    }

    /// The computation children in canonical order, each beside the linear
    /// binders the form opens over it: a hold's body and an access's body
    /// under one, an access's unwind under none.
    ///
    /// # Specification
    /// - ensures: a hold yields its body under one binder; an access its body
    ///   under one, then its unwind under none; an eliminator nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an access yields its body before its unwind, each
    ///   with its own binder count.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| ret.clone().count() == match *self {
        | Self::Hold { .. } => 1_usize,
        | Self::Access { .. } => 2_usize,
        | Self::Resume { .. } | Self::Abort { .. } => 0_usize,
    })]
    #[inline]
    pub fn scoped(&self) -> Scoped<C>
    {
        let (first, second) = match *self {
            Self::Hold { body, .. } => (Some((body, Binders::ONE)), None),
            Self::Access { body, unwind, .. } => {
                (Some((body, Binders::ONE)), Some((unwind, Binders::NONE)))
            },
            Self::Resume { .. } | Self::Abort { .. } => (None, None),
        };
        first.into_iter().chain(second)
    }

    /// The computation children in canonical order: a hold's body, an
    /// access's body then its unwind.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computations(&self) -> impl DoubleEndedIterator<Item = C> + '_
    {
        self.scoped().map(|(child, _)| child)
    }

    /// The form with every child erased: its case and the slot it names,
    /// which is what two forms must share to be the same former.
    ///
    /// # Specification
    /// - ensures: the form with every child replaced by the unit, kept at its
    ///   position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two resumes of one view differ in no shape, two
    ///   resumes of different views do.
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
    /// - ensures: the case and the slot it names are kept; each child is
    ///   replaced by its image at its own position; [`ChildOrder::Forward`]
    ///   visits a hold's value before its body, an access's body before its
    ///   unwind and a resume's value, and [`ChildOrder::Reverse`] exactly the
    ///   reverse.
    /// - fails: propagates the first error a map returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error of a map.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold mapped in reverse visits its body before its
    ///   value, across families, and keeps each image at its own position.
    /// - witness: `memory::tests::forms_name_their_resident_and_children`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped| match (self, mapped) {
        | (&Self::Access { held: a, .. }, &MemoryForm::Access { held: b, .. })
        | (&Self::Resume { view: a, .. }, &MemoryForm::Resume { view: b, .. })
        | (&Self::Abort { view: a }, &MemoryForm::Abort { view: b }) => a == b,
        | (&Self::Hold { .. }, &MemoryForm::Hold { .. }) => true,
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
            Self::Hold { value: held, body } => match order {
                ChildOrder::Forward => {
                    let held = value(state, held)?;
                    MemoryForm::Hold {
                        value: held,
                        body: computation(state, body)?,
                    }
                },
                ChildOrder::Reverse => {
                    let body = computation(state, body)?;
                    MemoryForm::Hold {
                        value: value(state, held)?,
                        body,
                    }
                },
            },
            Self::Access { held, body, unwind } => match order {
                ChildOrder::Forward => {
                    let body = computation(state, body)?;
                    MemoryForm::Access {
                        held,
                        body,
                        unwind: computation(state, unwind)?,
                    }
                },
                ChildOrder::Reverse => {
                    let unwind = computation(state, unwind)?;
                    MemoryForm::Access {
                        held,
                        body: computation(state, body)?,
                        unwind,
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
    /// - hypothesis: L3 — a minted access reads back with its slot, body and
    ///   unwind.
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
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_term::DeBruijnIndex;
    use quenchant_shape::shape::Maybe;

    use super::MemoryForm;
    use super::MemoryKind;
    use crate::Binders;
    use crate::Computation;
    use crate::CoreArena;
    use crate::session::ChildOrder;

    #[test]
    fn forms_name_their_resident_and_children()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let other = arena.value_tuple(&[unit, unit]);
        let body = arena.computation_return(unit);
        let unwind = arena.computation_return(unit);
        let held = DeBruijnIndex::from(1_u32);
        let hold: MemoryForm = MemoryForm::Hold { value: unit, body };
        assert_eq!(hold.kind(), MemoryKind::Hold, "a hold is a hold");
        assert!(
            matches!(hold.resident(), Maybe::Absent(_)),
            "and names no slot: it binds one"
        );
        assert_eq!(
            hold.values().collect::<Vec<_>>(),
            [unit],
            "its value is a child"
        );
        let mut seen = Vec::new();
        let mapped = hold
            .try_map(
                ChildOrder::Reverse,
                &mut seen,
                |seen: &mut Vec<&str>, value| {
                    seen.push("value");
                    Ok::<_, ()>(value)
                },
                |seen, computation| {
                    seen.push("body");
                    Ok(computation)
                },
            )
            .expect("identity maps succeed");
        assert_eq!(
            seen,
            ["body", "value"],
            "a reverse map is the canonical order reversed, across families"
        );
        assert_eq!(mapped, hold, "and keeps each child in its place");
        let access: MemoryForm = MemoryForm::Access { held, body, unwind };
        assert_eq!(access.kind(), MemoryKind::Access, "an access is an access");
        assert_eq!(
            access.resident(),
            Maybe::Present(held),
            "and names the slot it lends"
        );
        assert_eq!(
            access.scoped().collect::<Vec<_>>(),
            [(body, Binders::ONE), (unwind, Binders::NONE)],
            "its body stands under the view's binder, its unwind under none"
        );
        let view = DeBruijnIndex::from(0_u32);
        let resume: MemoryForm = MemoryForm::Resume { view, value: unit };
        assert_eq!(
            resume.resident(),
            Maybe::Present(view),
            "a resume names its view"
        );
        assert_eq!(
            resume.shape(),
            MemoryForm::<_>::Resume { view, value: other }.shape(),
            "two values written back through one view are one shape"
        );
        assert_ne!(
            resume.shape(),
            MemoryForm::<_>::Resume {
                view: held,
                value: unit
            }
            .shape(),
            "two views are not"
        );
        let abort: MemoryForm = MemoryForm::Abort { view };
        assert_eq!(abort.kind(), MemoryKind::Abort, "an abort is an abort");
        assert_eq!(
            abort
                .values()
                .chain(abort.computations().map(|_| unit))
                .count(),
            0_usize,
            "and has no child"
        );
        let minted = arena.computation_memory(access.clone());
        assert_eq!(
            arena.computation(minted),
            Some(&Computation::Memory(access)),
            "a minted access reads back whole"
        );
    }
}
