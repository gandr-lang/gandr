//! The identity family's names in the lowering. The family lives in
//! `gandr-surface-lowering-identity`, which compiles over the base beside the
//! rest of the lowering. The lowering is its host: a call into the family
//! builds `Identities::new(self)`, and a reading of the lowering builds
//! `IdentitiesRef::new(self)`. The family's tests stay here, because each case
//! lowers a source.

pub(super) use gandr_surface_lowering_identity::lower::identity::Identities;
pub(super) use gandr_surface_lowering_identity::lower::identity::IdentitiesRef;
#[cfg(test)]
use gandr_surface_lowering_identity::lower::identity::as_endpoint;
#[cfg(test)]
use gandr_surface_lowering_identity::lower::identity::telescope;

#[cfg(test)]
pub(super) mod tests;
