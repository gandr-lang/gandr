//! The comonoid of a type: the copy and the discard that let a binder of the
//! intuitionistic zone hold a value of the type.
//!
//! A binder of the intuitionistic zone at grade ω uses its value any number of
//! times. It copies and discards the value, so the value's type needs a
//! comonoid. A binder at grade 0 holds its value in types only, and the run
//! discards it, so the type needs a counit. The qubit type has neither, so
//! only a linear function's parameter holds a qubit.
//!
//! A type carries a comonoid when each component it holds carries one. The
//! components are those of a product, a sum, a record, a patched record, a
//! list, a dependent pair, and a staged, kept or lifted type. Every other
//! former carries one. A thunk captures only values whose types carry one. A
//! universe admits a quoted type only when the type carries one, so the
//! arguments of a data type and the type a code decodes to carry one too.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::QubitPrecedence;
use gandr_core_term::ValueTypeId;

use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::session::LinearityDefect;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// The grade of a binder of the intuitionistic zone, which needs a comonoid or
/// a counit of its type.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Grade
{
    /// `0`: the binder holds its value in types only, so its type needs a
    /// counit to discard the value.
    Zero,
    /// `ω`: the binder uses its value any number of times, so its type needs a
    /// comonoid to copy and discard the value.
    Many,
}

/// How a type formation's binder holds its domain while the formation reads
/// the codomain under it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Held
{
    /// A binder at grade 0 of the type formed at the node: the codomain reads
    /// the domain's value in types only, so the domain needs a counit.
    Erased(CoreNode),
    /// A linear parameter's shadow: the copy of the parameter that a linear
    /// arrow's codomain reads in types only. The linear zone holds the
    /// parameter itself.
    Shadow,
}

/// Refuse a binder at `grade` whose type `ty` holds a type with no comonoid.
///
/// # Specification
/// - requires: nothing; a dangling node refuses.
/// - ensures: nothing changes. A type minted before the arena's first qubit
///   type returns at once, with no walk. A leaf or a chain of one-component
///   formers costs no allocation; the queue and the visited set grow only under
///   a former of several components, each visited once.
/// - fails: [`CheckRefusal::Linearity`] naming
///   [`LinearityDefect::ComonoidAbsent`] with `ty` and `grade` at `at`, when
///   `ty` or a component it holds is the qubit type; the view's refusal when a
///   node dangles.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a qubit at each grade, a record and a sum that hold one,
///   a gate's thunk, and a product of types minted before the first qubit.
/// - witness: `comonoid::tests::a_qubit_is_refused_at_each_grade_5739`
/// - witness: `comonoid::tests::a_type_that_holds_a_qubit_is_refused_by_its_own_name_5739`
/// - witness: `comonoid::tests::a_gate_and_a_type_before_the_first_qubit_carry_a_comonoid_5739`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::ComonoidAbsent { ty: named, grade: graded } }) => {
        refused == at && named == ty && graded == grade
    },
    | _ => true,
})]
pub fn require(
    arena: &CoreArena,
    at: CoreNode,
    ty: ValueTypeId,
    grade: Grade,
) -> Result<(), CheckRefusal>
{
    let mut pending = Vec::new();
    let mut seen = BTreeSet::new();
    let mut next = Some(ty);
    while let Some(held) = next.take().or_else(|| pending.pop()) {
        if arena.value_type_qubit_precedence(held) == QubitPrecedence::Before {
            continue;
        }
        match value_type_view(arena, held)? {
            ValueTypeView::Qubit => {
                return Err(CheckRefusal::Linearity {
                    at,
                    defect: LinearityDefect::ComonoidAbsent { ty, grade },
                });
            },
            ValueTypeView::Product(parts) | ValueTypeView::Sum(parts) => {
                if seen.insert(held) {
                    pending.extend_from_slice(parts);
                }
            },
            ValueTypeView::Record(fields) => {
                if seen.insert(held) {
                    pending.extend(fields.values().copied());
                }
            },
            ValueTypeView::Sigma { first, second } => {
                if seen.insert(held) {
                    pending.extend([first, second]);
                }
            },
            ValueTypeView::Patched { base: part, .. }
            | ValueTypeView::List(part)
            | ValueTypeView::Lift { inner: part, .. }
            | ValueTypeView::Kept { value: part, .. }
            | ValueTypeView::Staged { base: part, .. } => next = Some(part),
            ValueTypeView::Data { .. }
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Bridge { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_)
            | ValueTypeView::Row
            | ValueTypeView::RowTail(_)
            | ValueTypeView::Unknown => {},
        }
    }
    Ok(())
}
