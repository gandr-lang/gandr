//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::normal_form::…`) instead of a file. The generated cases
//! live here rather than beside the code because the property runner needs
//! `std`.

#[cfg(test)]
mod normal_form;
