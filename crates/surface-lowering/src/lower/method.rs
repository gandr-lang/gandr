//! The method calls of the capability family, in the lowering. The family
//! lives in `gandr-surface-lowering-capability`. The tests of a method call
//! stay here, because each case lowers a source.

pub(super) use gandr_surface_lowering_base::lower::method::unheld;

#[cfg(test)]
mod tests;
