//! The computations the judgement decides at a row of operations.
//!
//! A declaration whose type carries a row of operations crosses the bridge
//! as a program of the row's free model (#6642). The bridge reads three
//! facts that the judgement decides on the way: each computation checked at
//! a returner over such a row, each computation synthesised at one, and the
//! level of each such returner's result. [`Rows`] records them, as
//! [`crate::handler::Handled`] records the types of a handler.
//!
//! A row of operations names at least one interface, each by its default
//! label. It names no instance, no tail and no divergence: the bridge has no
//! model of a row variable, and the model of `Partial` is the delay model of
//! the second unit of #2742.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectLabel;
use gandr_core_term::effect::EffectRow;
use gandr_kernel_strata::Level;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a computation type is no returner over a row of operations.
    pub mod unprogrammed {
        /// The reason the type is no such returner.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The type is no returner at its head, or names no node.
            NoReturner,
            /// The returner's row is pure.
            Pure,
            /// The row is open through a tail.
            Open,
            /// The row names an instance of an interface.
            Instance,
            /// The row names divergence.
            Divergent,
        }
    }
}

/// The result and the row of `ty` when it is a returner over a row of
/// operations, read at its head.
///
/// # Specification
/// - ensures: the returner's result and row when `ty` is a returner whose row
///   names at least one interface, each by its default label, and no tail and
///   no `Partial`.
/// - fails: absent, naming why, for any other type.
/// - panics: none.
/// - executable: none — the reason is the classification the body makes, so a
///   predicate restates it.
///
/// # Adequacy
/// - hypothesis: L3 — a returner over one host interface, a pure returner, an
///   open row and a row of `Partial` separate the four answers.
/// - witness: `program::tests::a_returner_over_a_row_of_operations_is_programmed_6642`
#[inline]
pub fn programmed(
    arena: &CoreArena,
    ty: CompTypeId,
) -> Maybe<(ValueTypeId, &EffectRow), unprogrammed::Absent>
{
    let Some(&gandr_core_term::CompType::Returner {
        result,
        ref effects,
    }) = arena.comp_type(ty)
    else {
        return Maybe::Absent(unprogrammed::Absent::NoReturner);
    };
    if effects.purity() == gandr_core_term::effect::Purity::Pure {
        return Maybe::Absent(unprogrammed::Absent::Pure);
    }
    if effects.tail().is_some() {
        return Maybe::Absent(unprogrammed::Absent::Open);
    }
    if effects
        .instances()
        .any(|(label, _)| !matches!(*label, EffectLabel::Interface(_)))
    {
        return Maybe::Absent(unprogrammed::Absent::Instance);
    }
    if effects
        .signatures()
        .any(|signature| signature.name().as_ref() == gandr_core_term::effect::host::PARTIAL)
    {
        return Maybe::Absent(unprogrammed::Absent::Divergent);
    }
    Maybe::Present((result, effects))
}

/// What the judgement decided of the computations at a row of operations:
/// what the bridge reads them as programs of the row's free model by.
///
/// # Specification
/// - executable: none — data declaration; the judgement writes it and the
///   bridge reads it.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration at a row whose body requests an operation,
///   binds a call and returns crosses as a program of the row's model at the
///   recorded types.
/// - witness: `bridge::tests::two_declarations_at_one_row_read_one_model_6642`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Rows
{
    /// Each computation checked at a returner over a row of operations, by
    /// node, with that returner: the first the judgement checked it at.
    checked: BTreeMap<ComputationId, CompTypeId>,
    /// Each computation synthesised at a returner over a row of operations,
    /// by node, with that returner: a bound computation, or one the
    /// computation bridge crossed to the type it was checked at.
    synthesised: BTreeMap<ComputationId, CompTypeId>,
    /// The level of the result of each returner over a row of operations the
    /// judgement formed or checked at, by node: the level of the row's model.
    levels: BTreeMap<CompTypeId, Level>,
}

/// A record that [`Rows`] added: the key [`Rows::forget`] removes.
///
/// # Specification
/// - executable: none — data declaration; [`Rows`] writes it and
///   [`Rows::forget`] reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Rows::forget`].
/// - witness: `bridge::tests::a_case_on_a_run_at_a_row_crosses_at_its_second_run_6672`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Gained
{
    /// The returner that a computation was checked at.
    Checked(ComputationId),
    /// The returner that a computation synthesised.
    Synthesised(ComputationId),
    /// The level of a returner's result.
    Level(CompTypeId),
}

impl Rows
{
    /// The returner over a row of operations `at` was checked at, when the
    /// judgement checked it at one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn checked(
        &self,
        at: ComputationId,
    ) -> Option<CompTypeId>
    {
        self.checked.get(&at).copied()
    }

    /// The returner over a row of operations `at` synthesised, when it
    /// synthesised one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn synthesised(
        &self,
        at: ComputationId,
    ) -> Option<CompTypeId>
    {
        self.synthesised.get(&at).copied()
    }

    /// The level of the result of the returner `ty`, when the judgement
    /// formed or checked at it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn level(
        &self,
        ty: CompTypeId,
    ) -> Option<&Level>
    {
        self.levels.get(&ty)
    }

    /// Record that the judgement checked `at` against `ty`, a returner over a
    /// row of operations whose result stands at `level`.
    ///
    /// # Specification
    /// - ensures: `at` reads the first returner it was checked at, and `ty`
    ///   reads the first level recorded for it; `gained` names each of the two
    ///   records that this call adds.
    /// - panics: none.
    /// - executable: none — the record is the statement; the witness crosses
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration at a row crosses as a program of the
    ///   row's model at the recorded returner.
    /// - witness: `bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    pub fn check(
        &mut self,
        at: ComputationId,
        (ty, level): (CompTypeId, Level),
        gained: &mut Vec<Gained>,
    )
    {
        if let Entry::Vacant(vacant) = self.checked.entry(at) {
            let _kept = vacant.insert(ty);
            gained.push(Gained::Checked(at));
        }
        self.keep_level(ty, level, gained);
    }

    /// Record that `at` synthesised `ty`, a returner over a row of operations
    /// whose result stands at `level`, or a type that crosses to one.
    ///
    /// # Specification
    /// - ensures: `at` reads the first returner it synthesised, and `ty` reads
    ///   the first level recorded for it; `gained` names each of the two
    ///   records that this call adds.
    /// - panics: none.
    /// - executable: none — the record is the statement; the witness crosses
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call of a declaration at a row binds its program
    ///   into the caller's.
    /// - witness: `bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    pub fn synthesise(
        &mut self,
        at: ComputationId,
        (ty, level): (CompTypeId, Option<Level>),
        gained: &mut Vec<Gained>,
    )
    {
        if let Entry::Vacant(vacant) = self.synthesised.entry(at) {
            let _kept = vacant.insert(ty);
            gained.push(Gained::Synthesised(at));
        }
        if let Some(level) = level {
            self.keep_level(ty, level, gained);
        }
    }

    /// Record that the judgement formed `ty`, a returner over a row of
    /// operations whose result stands at `level`.
    ///
    /// # Specification
    /// - ensures: `ty` reads the first level recorded for it; `gained` names
    ///   the record when this call adds it.
    /// - panics: none.
    /// - executable: none — the record is the statement; the witness crosses
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared type at a row crosses as a returner of the
    ///   row's model at this level.
    /// - witness: `bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    pub fn form(
        &mut self,
        ty: CompTypeId,
        level: Level,
        gained: &mut Vec<Gained>,
    )
    {
        self.keep_level(ty, level, gained);
    }

    /// Record `level` as the level of `ty`'s result, when no level reads for
    /// it, and name the record in `gained`.
    ///
    /// # Specification
    /// trivial.
    fn keep_level(
        &mut self,
        ty: CompTypeId,
        level: Level,
        gained: &mut Vec<Gained>,
    )
    {
        if let Entry::Vacant(vacant) = self.levels.entry(ty) {
            let _kept = vacant.insert(level);
            gained.push(Gained::Level(ty));
        }
    }

    /// Forget each record that `gained` names.
    ///
    /// # Specification
    /// - requires: `gained` names records that this record added.
    /// - ensures: no record that `gained` names reads here; every other record
    ///   reads as before.
    /// - panics: none.
    /// - executable: none — the records are the statement; the witness crosses
    ///   them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case on a run, at a row and over a type variable,
    ///   crosses at the records of the run that judges its elaborated body.
    /// - witness: `bridge::tests::a_case_on_a_run_at_a_row_crosses_at_its_second_run_6672`
    pub fn forget(
        &mut self,
        gained: impl IntoIterator<Item = Gained>,
    )
    {
        for record in gained {
            match record {
                Gained::Checked(at) => {
                    let _forgotten = self.checked.remove(&at);
                },
                Gained::Synthesised(at) => {
                    let _forgotten = self.synthesised.remove(&at);
                },
                Gained::Level(ty) => {
                    let _forgotten = self.levels.remove(&ty);
                },
            }
        }
    }

    /// Absorb `other`'s records, each fact this record holds kept.
    ///
    /// # Specification
    /// - ensures: every fact of either record reads here, this record's first
    ///   where both hold one.
    /// - panics: none.
    /// - executable: none — the records are the statement; the witness crosses
    ///   them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested elaboration's records reach the bridge, and
    ///   a rest that reads an outer binder crosses at them.
    /// - witness: `bridge::tests::a_call_folds_into_a_rest_that_reads_a_parameter_6642`
    pub fn absorb(
        &mut self,
        other: &Self,
    )
    {
        for (&at, &ty) in &other.checked {
            let _first = self.checked.entry(at).or_insert(ty);
        }
        for (&at, &ty) in &other.synthesised {
            let _first = self.synthesised.entry(at).or_insert(ty);
        }
        for (&ty, level) in &other.levels {
            let _first = self.levels.entry(ty).or_insert_with(|| level.clone());
        }
    }
}

#[cfg(test)]
mod tests;
