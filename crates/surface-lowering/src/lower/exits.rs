//! The exits family's names in the lowering. The family lives in
//! `gandr-surface-lowering-exits`, which compiles over the base beside the
//! rest of the lowering. The lowering is its host: a call into the family
//! builds `Exits::new(self)`, and a reading of the lowering builds
//! `ExitsRef::new(self)`. The family's tests stay here, because each case
//! lowers a source.

pub use gandr_surface_lowering_base::lower::exits::ElidableExit;
pub use gandr_surface_lowering_base::lower::exits::Exit;
pub use gandr_surface_lowering_base::lower::exits::Explicitness;
pub use gandr_surface_lowering_base::lower::exits::InferredExit;
pub(super) use gandr_surface_lowering_base::lower::exits::Leaves;
pub(super) use gandr_surface_lowering_base::lower::exits::Rest;
pub use gandr_surface_lowering_base::lower::exits::Returned;
pub(super) use gandr_surface_lowering_base::lower::exits::mark_copies;
pub(super) use gandr_surface_lowering_base::lower::exits::record_copies;
pub(super) use gandr_surface_lowering_exits::lower::exits::Exits;
pub(super) use gandr_surface_lowering_exits::lower::exits::ExitsRef;

#[cfg(test)]
pub(in crate::lower) mod tests;
