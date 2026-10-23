//! The forgetting maps the checker applies that the explicit form writes,
//! `forget[sort C = A, …](m) at Model(T)`, and the sugared form leaves to
//! the checker, `m`.
//!
//! A theory `T` with a model whose sorts are manifest takes a forgetting map
//! from those models to the models of `T`, and the checker applies it, at the
//! carriers it solves from the model's type, where such a model stands where
//! a model of `T` is asked. The explicit form writes each application whose
//! carriers a type position spells — each a type the checker quotes — around
//! the value it is made at. An application whose carrier is a sort selected
//! off a model, which the core holds by its position in the model's bundle
//! rather than by the sort's name, and one whose map returns a model of a
//! theory `T` includes, which a reduct then carries further, are left to the
//! checker in both forms.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Crossing;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering::Forgetting as Minted;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::Forgetting;
use gandr_surface_pretty::Name;

/// The forgetting maps among the checker's `crossings` that the explicit
/// form writes, ascending by the value crossed.
///
/// Each is the map's theory and each sort beside its carrier's type, read off
/// `crossings` over `module` lowered into `arena`.
///
/// # Specification
/// - requires: `crossings` were read off the elaboration of `module` into
///   `arena`.
/// - ensures: one entry per crossing by a map `module` mints whose theory is
///   the theory it returns a model of and whose every carrier is a quoted type,
///   its sorts in the map's order beside the types quoted; ascending by the
///   value.
/// - provides: the forgetting maps the printer writes in the explicit form and
///   the formatter spells.
/// - fails: never.
/// - panics: none.
/// - executable: none — the selection reads the arena's values, which the
///   witness's golden reads back.
///
/// # Adequacy
/// - hypothesis: L3 — a map at a quoted carrier and one of two sorts read in
///   order are written; a carrier that is no quote, a map a reduct carries
///   further and a constant that is no forgetting map are not.
/// - witness: `tests::forget::a_forgetting_map_is_written_only_at_quoted_carriers_onto_its_own_theory_2130`
#[inline]
#[must_use]
pub fn forgettings<'module>(
    module: &'module LoweredModule<'_>,
    arena: &CoreArena,
    crossings: &BTreeMap<ValueId, Crossing>,
) -> Vec<(ValueId, Forgetting<'module>)>
{
    let minted: BTreeMap<ConstantIndex, &Minted> = module
        .forgettings()
        .iter()
        .map(|forgetting| (forgetting.map, forgetting))
        .collect();
    let mut found = Vec::new();
    for (&value, crossing) in crossings {
        let Some(&forgetting) = minted.get(&crossing.by)
        else {
            continue;
        };
        let onto_its_own = forgetting.onto == forgetting.theory;
        let every_carrier = forgetting.sorts.len() == crossing.carriers.len();
        if !onto_its_own || !every_carrier {
            continue;
        }
        let sorts: Option<Vec<(Name<'module>, CoreNode)>> = forgetting
            .sorts
            .iter()
            .zip(&crossing.carriers)
            .map(|(sort, &carrier)| match arena.value(carrier) {
                Some(&Value::Quote(quoted)) => {
                    Some((Name::from(sort.as_ref()), CoreNode::ValueType(quoted)))
                },
                Some(_) | None => None,
            })
            .collect();
        if let Some(sorts) = sorts {
            found.push((value, Forgetting {
                theory: forgetting.theory,
                sorts,
            }));
        }
    }
    found
}
