//! A program's entry: the `main` a source declares at its top level. An entry
//! is a computation returning the exit code, `U (F^e Integer)`, or the unit,
//! `U (F^e Unit)`, whose run exits with zero, or a function returning either
//! of the arguments, `U (List(String) → F^e …)`, or of the ambient authority,
//! `U (Cap {…} → F^e …)`: the capability the host hands the run once, from
//! which `std.authority` opens each host module's root capability. The
//! interfaces `e` it may perform are its own. A `main` at any other type is
//! refused by name where it is declared, so a program never starts at an
//! entry no run can read an exit code from.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Sink;
use crate::error::LoweringRefusal;
use crate::module::Container;
use crate::module::DeclarationOutcome;
use crate::module::Role;
use crate::module::SlotIndex;

/// The name a source declares its program's entry under.
pub const ENTRY: &str = "main";

quenchant_shape::reason_enum! {
    /// Why a type is no entry's.
    pub mod entry_shape {
        /// The type is not the thunk of a computation returning an integer or
        /// the unit, directly or after the arguments or the authority.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Another type.
            Misshapen,
        }
    }
}

/// What an entry takes when it runs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Arguments
{
    /// Nothing: the entry is a computation, forced.
    Unread,
    /// The program's arguments, as one `List(String)`, applied after the
    /// force.
    Read,
    /// The ambient authority, a capability the host holds, applied after the
    /// force.
    Authority,
}

/// The arguments the entry type `declared` takes, when it is an entry's.
///
/// # Specification
/// - requires: `declared` is a value type of `arena`.
/// - ensures: [`Arguments::Unread`] for `U (F^e R)`, [`Arguments::Read`] for `U
///   (List(String) → F^e R)` and [`Arguments::Authority`] for `U (Cap {…} → F^e
///   R)`, each function written as an arrow or a Pi, each under any row `e`,
///   where `R` is `Integer` or the unit; the misshapen absence for every other
///   type, a type `arena` does not hold included.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the three entry types under the empty row and a row of
///   one interface, each returning an integer and the unit, beside a returner
///   of a string, a function of an integer and a bare integer.
/// - witness: `lower::entry::tests::an_entry_returns_an_integer_after_its_arguments_1881`
/// - witness: `lower::entry::tests::an_entry_returns_the_unit_2279`
/// - witness: `lower::entry::tests::an_entry_takes_the_ambient_authority_2970`
#[spec(ensures: |ret| match ret {
    Maybe::Present(Arguments::Unread) => matches!(arena.value_type(declared), Some(&ValueType::Thunk(body))
        if matches!(arena.comp_type(body), Some(&CompType::Returner { .. }))),
    Maybe::Present(Arguments::Read | Arguments::Authority) => matches!(arena.value_type(declared), Some(&ValueType::Thunk(body))
        if matches!(arena.comp_type(body), Some(&(CompType::Arrow { .. } | CompType::Pi { .. })))),
    Maybe::Absent(_) => true,
})]
#[inline]
pub fn entry_shape(
    arena: &CoreArena,
    declared: ValueTypeId,
) -> Maybe<Arguments, entry_shape::Absent>
{
    let misshapen = Maybe::Absent(entry_shape::Absent::Misshapen);
    let Some(&ValueType::Thunk(body)) = arena.value_type(declared)
    else {
        return misshapen;
    };
    let returns_code = |computation: CompTypeId| {
        matches!(arena.comp_type(computation), Some(&CompType::Returner { result, .. })
            if matches!(arena.value_type(result),
                Some(&ValueType::Base(BaseType::Integer)))
                || matches!(arena.value_type(result), Some(&ValueType::Product(ref fields)) if fields.is_empty()))
    };
    if returns_code(body) {
        return Maybe::Present(Arguments::Unread);
    }
    let Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) =
        arena.comp_type(body)
    else {
        return misshapen;
    };
    if !returns_code(codomain) {
        return misshapen;
    }
    match arena.value_type(domain) {
        Some(&ValueType::List(element))
            if arena.value_type(element) == Some(&ValueType::Base(BaseType::String)) =>
        {
            Maybe::Present(Arguments::Read)
        },
        Some(&ValueType::Capability { .. }) => Maybe::Present(Arguments::Authority),
        _ => misshapen,
    }
}

impl Lowerer<'_, '_>
{
    /// Refuse each `main` the current source declares at its top level whose
    /// declared type no entry has, or that declares no type.
    ///
    /// # Specification
    /// - requires: the current source's declarations are minted into `sink`.
    /// - ensures: a declared slot named [`ENTRY`] at the current source's top
    ///   level, whose own outcome holds a declared type [`entry_shape()`] finds
    ///   misshapen, or whose outcome is a body with no signature, a type
    ///   declaration or a world, is refused [`LoweringRefusal::EntryType`] at
    ///   its name; every other slot, a refused one among them, is as it was.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause is [`entry_shape()`]'s over each slot's
    ///   outcome; the witness reads the refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `main` of each entry type checks; one returning a
    ///   string, one of an integer argument and one with no signature are
    ///   refused at their names; a module's member named `main` is no entry.
    /// - witness: `lower::entry::tests::a_main_of_another_type_is_refused_by_name_1881`
    pub(super) fn refuse_misshapen_entries(
        &mut self,
        sink: &Sink<'_>,
    )
    {
        let top = Container::TopLevel(self.current.source);
        let misshapen: Vec<(SlotIndex, ByteSpan)> = self
            .collected
            .slots
            .iter()
            .enumerate()
            .skip(self.current.slots)
            .filter(|&(_, slot)| {
                slot.role == Role::Declared && slot.container == top && slot.name.as_ref() == ENTRY
            })
            .filter_map(|(position, slot)| {
                let position = SlotIndex::from(position);
                match self.own_outcome(position, slot) {
                    Maybe::Present(
                        DeclarationOutcome::Completed { declared_type, .. }
                        | DeclarationOutcome::Uncompleted { declared_type },
                    ) => match entry_shape(sink.arena, declared_type) {
                        Maybe::Present(_) => None,
                        Maybe::Absent(_) => Some((position, slot.named.span)),
                    },
                    Maybe::Present(
                        DeclarationOutcome::Bodied { .. }
                        | DeclarationOutcome::Data(_)
                        | DeclarationOutcome::Codata(_)
                        | DeclarationOutcome::Abstract(_)
                        | DeclarationOutcome::World,
                    ) => Some((position, slot.named.span)),
                    Maybe::Present(DeclarationOutcome::Refused(_)) | Maybe::Absent(_) => None,
                }
            })
            .collect();
        for (position, span) in misshapen {
            let _first = self
                .faults
                .insert(position, LoweringRefusal::EntryType { span });
        }
    }
}

#[cfg(test)]
mod tests;
