//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::laws::…`) instead of a file. `amplitude!` and `real!`
//! spell an exact amplitude from integers the test knows.

/// The amplitude `(a + b√2 + (c + d√2)i) / 2^k`.
#[cfg(test)]
macro_rules! amplitude {
    ($a:expr, $b:expr, $c:expr, $d:expr; $k:expr) => {{
        let coefficients: [i128; 4] = [$a, $b, $c, $d];
        let scale: u32 = $k;
        let [a, b, c, d] = coefficients.map(gandr_theory_ordered_algebras::Coefficient::from);
        gandr_theory_ordered_algebras::Amplitude::new(
            a,
            b,
            c,
            d,
            gandr_theory_ordered_algebras::Scale::from(scale),
        )
    }};
}

/// The real amplitude `(a + b√2) / 2^k`.
#[cfg(test)]
macro_rules! real {
    ($a:expr, $b:expr; $k:expr) => {{
        let coefficients: [i128; 2] = [$a, $b];
        let scale: u32 = $k;
        let [a, b] = coefficients.map(gandr_theory_ordered_algebras::Coefficient::from);
        gandr_theory_ordered_algebras::RealAmplitude::new(
            a,
            b,
            gandr_theory_ordered_algebras::Scale::from(scale),
        )
    }};
}

#[cfg(test)]
mod amplitudes;
#[cfg(test)]
mod gates;
#[cfg(test)]
mod laws;
