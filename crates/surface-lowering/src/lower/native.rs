//! The native family's names in the lowering. The family lives in
//! `gandr-surface-lowering-native`, which compiles over the base beside the
//! rest of the lowering. The lowering is its host: a call into the family
//! builds `Native::new(self)`. The family's tests stay here, because each
//! case lowers a source.

#[cfg(test)]
pub(super) use gandr_surface_lowering_base::lower::native::ParameterAt;
pub(super) use gandr_surface_lowering_native::lower::native::Native;
pub(super) use gandr_surface_lowering_native::lower::native::NativeRef;

#[cfg(test)]
pub(super) mod tests;
