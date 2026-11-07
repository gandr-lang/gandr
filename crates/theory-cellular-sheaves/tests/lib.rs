//! The integration tests of `gandr-theory-cellular-sheaves`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.
//!
//! `rational!` spells an exact rational, which the areas share.

/// The rational `numerator / denominator` of two 128-bit integers, which the
/// test knows to be in range.
#[cfg(test)]
macro_rules! rational {
    ($numerator:expr, $denominator:expr) => {{
        let numerator: i128 = $numerator;
        let denominator: i128 = $denominator;
        gandr_theory_cellular_sheaves::Rational::new(
            gandr_theory_cellular_sheaves::Integer::from(numerator),
            gandr_theory_cellular_sheaves::Integer::from(denominator),
        )
        .expect("a rational in range")
    }};
}

#[cfg(test)]
mod cochains;
#[cfg(test)]
mod junction;
#[cfg(test)]
mod rational;
#[cfg(test)]
mod reduce;
#[cfg(test)]
mod sheaf;
#[cfg(test)]
mod towers;
