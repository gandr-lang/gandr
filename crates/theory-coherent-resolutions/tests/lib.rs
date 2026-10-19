//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::overlap::…`) instead of a file. The second-inhabitant
//! and adversary suites read the toy alphabet from the test-only tools crate;
//! the differential suite needs `std` for the property runner.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

#[cfg(test)]
mod adversarial_alphabet;
#[cfg(test)]
mod completion;
#[cfg(test)]
mod differential;
#[cfg(test)]
mod fixture;
#[cfg(test)]
mod overlap;
#[cfg(test)]
mod second_inhabitant;
