//! The integration tests of `gandr-theory-probability`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.
//!
//! The generated distributions and kernels are in `strategy`, which the
//! areas share, and `rational!` spells an exact weight.

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
mod canonical;
#[cfg(test)]
mod condition;
#[cfg(test)]
mod joint;
#[cfg(test)]
mod monad;
#[cfg(test)]
mod strategy;
