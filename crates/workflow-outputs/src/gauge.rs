//! The gauges of the store, their bounds, and the event when a gauge passes
//! its bound.
//!
//! The store is a shared resource. Two gauges watch it: its size in bytes,
//! and the count of the values of the base that a run computes again. A
//! count above its bound says that the store does not hold what the runs
//! before it computed. Each bound is a number of the unit of its gauge, and
//! the environment can set it.
//!
//! When a gauge passes its bound, the run writes one line with the priority
//! `err` (`<3>`, which the journal reads on standard error), and runs the
//! command that `GANDR_OUTPUT_EVENT` names one time, with the name of the
//! gauge, its value and its bound as its arguments.

use std::fs;
use std::io;
use std::process::Command;
use std::process::Stdio;

use anodized::spec;

use crate::store::Store;

/// The bound of the size of the store, in bytes, when
/// `GANDR_OUTPUT_STORE_BOUND` sets none: 4 GiB.
pub const STORE_BOUND: u64 = 0x1_0000_0000;

/// The bound of the values of the base that one run computes again.
///
/// `GANDR_OUTPUT_RECOMPUTED_BOUND` sets another. The default is above the
/// count of the sources of the corpus, which one change of the parser
/// computes again.
pub const RECOMPUTED_BOUND: u64 = 1024;

/// One gauge: its name, its value and its bound, in the unit of the gauge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Gauge
{
    /// The name of the gauge.
    pub name: &'static str,
    /// The value that the run read.
    pub value: u64,
    /// The bound of the value.
    pub bound: u64,
}

impl Gauge
{
    /// Whether the value is past the bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn passed(&self) -> bool
    {
        self.value > self.bound
    }

    /// The line that the run writes when the gauge passes its bound.
    ///
    /// # Specification
    /// - ensures: the line starts with the priority `<3>` and names the gauge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a gauge at its bound passes nothing, and a gauge one
    ///   above it names its value and its bound.
    /// - witness: `gauge::tests::a_gauge_above_its_bound_complains`
    #[spec(ensures: |ret| ret.starts_with("<3>") && ret.contains(self.name))]
    #[inline]
    #[must_use]
    pub fn complaint(&self) -> String
    {
        format!(
            "<3>outputs: the gauge `{}` is {}, past its bound of {}",
            self.name, self.value, self.bound
        )
    }
}

/// The bound that the variable `name` sets, or `default`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn bound(
    name: &str,
    default: u64,
) -> u64
{
    std::env::var(name)
        .ok()
        .and_then(|text| text.trim().parse().ok())
        .unwrap_or(default)
}

/// The size of `store` in bytes: each file below its directory.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A directory of the store that exists and cannot be read.
#[inline]
pub fn size(store: &Store) -> io::Result<u64>
{
    let mut total = 0_u64;
    let mut pending = vec![store.root().to_path_buf()];
    while let Some(directory) = pending.pop() {
        let entries = match fs::read_dir(&directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error),
        };
        for entry in entries {
            let entry = entry?;
            let kind = entry.file_type()?;
            if kind.is_dir() {
                pending.push(entry.path());
            }
            else {
                total = total.saturating_add(entry.metadata()?.len());
            }
        }
    }
    Ok(total)
}

/// For each gauge of `gauges` past its bound: its line, and one run of the
/// command that `GANDR_OUTPUT_EVENT` names. Returns the lines.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn complain(gauges: &[Gauge]) -> Vec<String>
{
    let event = std::env::var_os("GANDR_OUTPUT_EVENT");
    gauges
        .iter()
        .filter(|gauge| gauge.passed())
        .map(|gauge| {
            if let Some(ref command) = event {
                let _posted = Command::new(command)
                    .args([
                        gauge.name.to_owned(),
                        gauge.value.to_string(),
                        gauge.bound.to_string(),
                    ])
                    .stdin(Stdio::null())
                    .stdout(Stdio::null())
                    .status();
            }
            gauge.complaint()
        })
        .collect()
}

#[cfg(test)]
mod tests
{
    use super::Gauge;

    /// A gauge at its bound passes nothing, and a gauge one above it names
    /// its value and its bound.
    #[test]
    fn a_gauge_above_its_bound_complains()
    {
        let at = Gauge {
            name: "recomputed base values",
            value: 1024,
            bound: 1024,
        };
        assert!(!at.passed(), "a gauge at its bound passes nothing");
        let above = Gauge { value: 1025, ..at };
        assert!(above.passed(), "a gauge above its bound passes it");
        assert_eq!(
            above.complaint(),
            "<3>outputs: the gauge `recomputed base values` is 1025, past its bound of 1024"
        );
    }
}
