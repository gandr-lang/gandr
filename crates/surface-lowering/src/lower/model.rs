//! The model family's names in the lowering. The family lives in
//! `gandr-surface-lowering-model`, which compiles over the base beside the rest
//! of the lowering. The lowering is its host: a call into the family builds
//! `Models::new(self)`, and a reading of the lowering builds
//! `ModelsRef::new(self)`. The family's tests stay here, because each case
//! lowers a source.

pub(super) use gandr_surface_lowering_model::lower::model::Models;
pub(super) use gandr_surface_lowering_model::lower::model::ModelsRef;

#[cfg(test)]
mod opening;
