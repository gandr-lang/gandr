//! The capability family's names in the lowering. The family lives in
//! `gandr-surface-lowering-capability`, which compiles over the base beside
//! the rest of the lowering. The lowering is its host: a call into the family
//! builds `Capability::new(self)`, and a reading of the lowering builds
//! `CapabilityRef::new(self)`. The family's tests stay here, because each case
//! lowers a source.

pub(super) use gandr_surface_lowering_base::lower::capability::Interface;
pub(super) use gandr_surface_lowering_base::lower::capability::Standing;
pub(super) use gandr_surface_lowering_base::lower::capability::Stated;
pub(super) use gandr_surface_lowering_capability::lower::capability::Capability;
pub(super) use gandr_surface_lowering_capability::lower::capability::CapabilityRef;
pub(super) use gandr_surface_lowering_capability::lower::capability::Reply;

#[cfg(test)]
mod tests;
