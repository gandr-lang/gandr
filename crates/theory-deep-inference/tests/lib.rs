//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::shift::…`) instead of a file. The suites read the toy
//! alphabet and its adversaries from the test-only tools crate, because the
//! sequent alphabet has one command position per term and so no two
//! applications that could commute; the oracle suite reads the sequent
//! alphabet, because it checks the engine's own fixtures.

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
mod adversarial_alphabet;
#[cfg(test)]
mod asynchronous_axioms;
#[cfg(test)]
mod causal_web;
#[cfg(test)]
mod content_faithfulness;
#[cfg(test)]
mod deep_derivation;
#[cfg(test)]
mod fixture;
#[cfg(test)]
mod flow;
#[cfg(test)]
mod footprint;
#[cfg(test)]
mod normal_form;
#[cfg(test)]
mod oracle;
#[cfg(test)]
mod shift;
#[cfg(test)]
mod template;
