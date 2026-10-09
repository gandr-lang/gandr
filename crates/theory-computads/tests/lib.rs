//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::eta::…`) instead of a file. The circuit suites read the
//! toy alphabet and its withheld-convexity adversary from the test-only tools
//! crate, because a sequent command has one command position and so carries no
//! two applications that could commute; the description suites read the
//! sequent alphabet, which is what a description elaborates into.

extern crate alloc;

/// A toy position from child indices, read from the root outward.
macro_rules! at {
    ($($step:expr),* $(,)?) => {
        <gandr_theory_cell_complexes_tools::ToyAlphabet as gandr_theory_cell_complexes::CellAlphabet>::position_at_path(&[$({
            let step: usize = $step;
            gandr_theory_cell_complexes::PositionStep::from(step)
        }),*])
    };
}

#[cfg(test)]
mod circuit_instantiation;
#[cfg(test)]
mod convexity_supply;
#[cfg(test)]
mod eta;
#[cfg(test)]
mod fixture;
#[cfg(test)]
mod linearity;
#[cfg(test)]
mod order;
#[cfg(test)]
mod workspace;
