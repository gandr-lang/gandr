//! The `export` mark, as the lowering reads it.
//!
//! An export is a definition that a caller outside gandr calls by its key in
//! the export table of its program. The mark stands before the definition:
//!
//! ```text
//! @[export]
//! def fnv_step(hash : u64, byte : u64) -> u64 = …;
//! ```
//!
//! The type of an export is in the fragment of an export: the definition
//! states it, each parameter and the result is a fixed-width integer, and the
//! row is empty. The lowering refuses the mark by name at each other
//! definition: [`FragmentBoundary::Export`] at a type outside the fragment, and
//! [`FragmentBoundary::ExportRow`] at a row that is open or names an
//! interface. The declaration of an admitted mark lowers as it does with no
//! mark.

use alloc::vec::Vec;

use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::Purity;
use gandr_kernel_term::BaseType;
use gandr_surface_lowering_base::lower::lowered;
use quenchant_shape::shape::Maybe;

use super::Expressions;
use super::Families;
use super::Sink;
use crate::attribute::RegisteredAttribute;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::module::Half;
use crate::module::Operand;
use crate::module::SlotIndex;

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Refuse each `export` mark of the current source whose definition is
    /// outside the fragment of an export.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so each signature's type is minted.
    /// - ensures: each slot of the current source that holds no refusal and no
    ///   fault, and that carries an `export` mark, takes the fault of its mark
    ///   when [`export_fault()`] finds one in its declared type; a slot with no
    ///   declared type takes [`FragmentBoundary::Export`]. Each other slot is
    ///   unchanged.
    /// - panics: none.
    /// - executable: none — the faults are a table of the context, and a
    ///   predicate would read every type again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an export of two `u64` lowers to its definition, and
    ///   an export of an `Integer`, an export with an open row, an export with
    ///   a named interface and an export with no stated type each take the
    ///   fault of its own boundary.
    /// - witness: `gandr-surface-lowering::lower::export::tests::an_export_of_fixed_width_integers_lowers`
    /// - witness: `gandr-surface-lowering::lower::export::tests::each_export_outside_the_fragment_is_refused_by_name`
    ///
    /// # Cost
    /// - allocation: the refusals, growth within the source's slots
    #[inline]
    pub fn refuse_exports(
        &mut self,
        sink: &Sink<'_>,
    )
    {
        let cx = self.cx_mut();
        let mut refused = Vec::new();
        for (index, slot) in cx.collected.slots.iter().enumerate().skip(cx.current.slots) {
            let position = SlotIndex::from(index);
            if let Maybe::Present(_) = slot.refusal {
                continue;
            }
            if cx.faults.contains_key(&position) {
                continue;
            }
            let Some(mark) = slot
                .attributes
                .iter()
                .find(|written| written.name.as_ref() == RegisteredAttribute::EXPORT.as_ref())
            else {
                continue;
            };
            let declared = match slot.signature {
                Maybe::Present(Half {
                    operand: Operand::Written(written),
                    ..
                }) => cx.value_type_at(written.node),
                Maybe::Present(Half {
                    operand: Operand::Function,
                    declaration,
                    ..
                }) => cx.signature_at(declaration.node),
                Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
            };
            let fault = match declared {
                Maybe::Present(declared) => export_fault(sink.arena, declared),
                Maybe::Absent(_) => Maybe::Present(FragmentBoundary::Export),
            };
            if let Maybe::Present(boundary) = fault {
                refused.push((position, LoweringRefusal::OutOfFragment {
                    span: mark.span,
                    form: FormName::ATTRIBUTE,
                    sort: FragmentSort::Declaration,
                    boundary,
                }));
            }
        }
        for (position, refusal) in refused {
            let _first = cx.faults.insert(position, refusal);
        }
    }
}

/// The boundary an export of the declared type `declared` crosses, or none
/// when the type is in the fragment of an export.
///
/// # Specification
/// - requires: `declared` is minted in `arena`.
/// - ensures: none exactly when `declared` is the thunk of a chain of zero or
///   more functions, each over a fixed-width integer, that ends in the returner
///   of a fixed-width integer whose row is pure;
///   [`FragmentBoundary::ExportRow`] when the chain binds a row, or when each
///   type of the chain is a fixed-width integer and the row is not pure;
///   [`FragmentBoundary::Export`] for each other type.
/// - panics: none.
///
/// # Termination
/// - reason: each step reads the codomain of one function of a finite type.
/// - measure: the functions of the chain that are left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Expressions::refuse_exports`].
/// - witness: `gandr-surface-lowering::lower::export::tests::an_export_of_fixed_width_integers_lowers`
/// - witness: `gandr-surface-lowering::lower::export::tests::each_export_outside_the_fragment_is_refused_by_name`
///
/// # Cost
/// - allocation: none
#[inline]
pub fn export_fault(
    arena: &CoreArena,
    declared: ValueTypeId,
) -> Maybe<FragmentBoundary, export_fault::Absent>
{
    let fixed = |id: ValueTypeId| {
        matches!(
            arena.value_type(id),
            Some(&ValueType::Base(BaseType::Fixed(_)))
        )
    };
    let Some(&ValueType::Thunk(mut computation)) = arena.value_type(declared)
    else {
        return Maybe::Present(FragmentBoundary::Export);
    };
    loop {
        match arena.comp_type(computation) {
            Some(&CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain })
                if fixed(domain) =>
            {
                computation = codomain;
            },
            // A row binder leaves the row of the returner open.
            Some(&CompType::Arrow { domain, .. } | &CompType::Pi { domain, .. })
                if matches!(arena.value_type(domain), Some(&ValueType::Row)) =>
            {
                return Maybe::Present(FragmentBoundary::ExportRow);
            },
            Some(&CompType::Returner {
                result,
                ref effects,
            }) if fixed(result) => {
                return match effects.purity() {
                    Purity::Pure => Maybe::Absent(export_fault::Absent::InFragment),
                    Purity::Effectful => Maybe::Present(FragmentBoundary::ExportRow),
                };
            },
            Some(_) | None => return Maybe::Present(FragmentBoundary::Export),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an export crosses no boundary.
    pub mod export_fault {
        /// The declared type is in the fragment of an export.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Each parameter and the result is a fixed-width integer, and the
            /// row is pure.
            InFragment,
        }
    }
}
