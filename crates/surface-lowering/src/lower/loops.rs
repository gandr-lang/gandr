//! The loops of the exits family, in the lowering. The family lives in
//! `gandr-surface-lowering-exits`. The tests of a loop stay here, because each
//! case lowers a source.

pub(super) use gandr_surface_lowering_exits::lower::loops::again;

#[cfg(test)]
mod tests;
