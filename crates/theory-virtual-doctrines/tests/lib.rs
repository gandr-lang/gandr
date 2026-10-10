//! Public-API law witnesses.

extern crate alloc;

#[cfg(test)]
mod crdc;
#[cfg(test)]
mod directed;
#[cfg(test)]
mod laws;
#[cfg(test)]
mod overlap_factoring;

/// Require availability at a witness boundary, retaining refusal evidence.
#[cfg(test)]
#[track_caller]
/// Extract the fixture value or report its absence reason.
///
/// # Specification
/// trivial.
fn require_present<Value, Reason>(value: quenchant_shape::shape::Maybe<Value, Reason>) -> Value
where
    Reason: core::fmt::Debug,
{
    match value {
        | quenchant_shape::shape::Maybe::Present(value) => value,
        | quenchant_shape::shape::Maybe::Absent(reason) => {
            panic!("required witness is absent: {reason:?}")
        },
    }
}

#[cfg(test)]
mod constructor_menu;
