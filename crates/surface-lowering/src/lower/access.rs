//! The accesses of the capability family, in the lowering. The family lives
//! in `gandr-surface-lowering-capability`. The tests of an access stay here,
//! because each case lowers a source.

pub(super) use gandr_surface_lowering_capability::lower::access::ASSIGNING;

#[cfg(test)]
pub(in crate::lower) mod tests;
