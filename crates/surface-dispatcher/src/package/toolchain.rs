//! What a package asks of the toolchain that checks it, and whether the
//! running toolchain meets it.
//!
//! # Three constraints, each checked at `gandr check`
//!
//! A package's model includes `std.package`'s `Toolchain` and states three
//! fields, each a string:
//!
//! - `gandr`, the least language version its sources are written for, `>= 0.3`
//!   or `>= 0.3.1`, met by a running version at or above it; empty for any.
//! - `features`, the features its sources use, `,`-separated keys of gandr's
//!   features ledger, each met when the ledger the binary was built with holds
//!   it [`Status::Implemented`] or [`Status::Partial`].
//! - `systems`, the systems it is built on, `,`-separated, each
//!   `<architecture>-<os>` as Rust names the host's, `x86_64-linux`; met when
//!   the host is one of them, or when none is named.
//!
//! Each constraint left unmet is refused by its clause, `ToolchainUnmet.gandr`,
//! `ToolchainUnmet.feature.<key>` or `ToolchainUnmet.system`, naming the field,
//! what it asks and what the toolchain has. A constraint is never satisfied by
//! fetching a toolchain: it is checked, and the package is refused.
//!
//! **Lists are strings.** `features` and `systems` are one line each, as
//! `authors` is, until an operation's port can be a list (#2993).
//!
//! **The ledger is the authority.** What the toolchain has is what its own
//! features ledger says it implements, read from the copy the binary was
//! built with, so a package checked outside gandr's tree is held to the same
//! rows. The alternative was a list of feature names kept beside the ledger,
//! which the ledger's gate would not hold. The choice reverses if a feature a
//! package can ask for stops being a ledger row.

use core::fmt;
use core::str::FromStr;
use std::env::consts::ARCH;
use std::env::consts::OS;

use anodized::spec;

use super::Basic;
use super::Listed;
use crate::FeatureId;
use crate::FeatureLedger;
use crate::Status;

/// The comparison a `gandr` constraint is written with.
const AT_LEAST: &str = ">=";

/// A language version, `major.minor.patch`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Version
{
    /// The major version.
    major: u64,
    /// The minor version.
    minor: u64,
    /// The patch version.
    patch: u64,
}

impl FromStr for Version
{
    type Err = Unconstrained;

    /// The version `text` spells, `major.minor` or `major.minor.patch`, each a
    /// decimal number; a missing patch is `0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the version whose numbers `text` spells, `.`-separated, two
    ///   or three of them.
    /// - fails: [`Unconstrained`] for any other text.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unconstrained`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two and three numbers read, a missing patch reads as
    ///   `0`, and one number, four, a sign and an empty part are refused.
    /// - witness: `package::toolchain::tests::a_version_reads_two_or_three_numbers`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |version| version.to_string().split('.').count() == 3_usize))]
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let mut parts = text.split('.');
        let number = |part: Option<&str>| {
            let digits = part
                .filter(|part| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit()))
                .ok_or(Unconstrained)?;
            digits.parse::<u64>().map_err(|_overflow| Unconstrained)
        };
        let major = number(parts.next())?;
        let minor = number(parts.next())?;
        let patch = match parts.next() {
            None => 0,
            some @ Some(_) => number(some)?,
        };
        if parts.next().is_some() {
            return Err(Unconstrained);
        }
        Ok(Self {
            major,
            minor,
            patch,
        })
    }
}

impl Version
{
    /// The version of the running toolchain: this crate's, which the workspace
    /// gives every crate of the binary.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn running() -> Self
    {
        env!("CARGO_PKG_VERSION").parse().unwrap_or_default()
    }
}

impl fmt::Display for Version
{
    /// Writes `major.minor.patch`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// A model's line of `,`-separated entries, as its field states it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Separated<'line>(pub &'line str);

/// What a package's model asks of the toolchain.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Toolchain
{
    /// `gandr`, as written.
    gandr: String,
    /// The least version `gandr` admits, when it names one.
    least: Option<Version>,
    /// `features`, one key per entry, in order.
    features: Vec<FeatureId>,
    /// `systems`, one system per entry, in order.
    systems: Vec<String>,
}

/// Why a model's `gandr`, or the version in it, states no constraint the
/// check can read.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Unconstrained;

impl Toolchain
{
    /// The constraints a model states as its three fields' strings.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `gandr` kept as written, its least version the one after
    ///   [`AT_LEAST`], none when it is blank; `features` and `systems` each its
    ///   line's entries, split at `,`, trimmed, the blank ones left out.
    /// - fails: [`Unconstrained`] for a `gandr` that is neither blank nor `>=`
    ///   and a version [`Version`] reads.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unconstrained`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a blank `gandr` and blank lists ask nothing; a
    ///   version after `>=`, with or without spaces, is the least; entries are
    ///   trimmed; a version with no `>=`, a `<=`, and a `>=` before no version
    ///   are refused.
    /// - witness: `package::toolchain::tests::a_model_s_strings_read_as_its_constraints`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |toolchain| toolchain.systems.iter().map(String::as_str)
        .chain(toolchain.features.iter().map(|key| key.0.as_str()))
        .all(|entry| !entry.is_empty() && entry.trim() == entry)))]
    #[inline]
    pub fn read(
        gandr: String,
        features: Separated<'_>,
        systems: Separated<'_>,
    ) -> Result<Self, Unconstrained>
    {
        let least = match gandr.trim() {
            "" => None,
            written => Some(
                written
                    .strip_prefix(AT_LEAST)
                    .ok_or(Unconstrained)?
                    .trim()
                    .parse::<Version>()?,
            ),
        };
        let each = |line: Separated<'_>| -> Vec<String> {
            line.0
                .split(',')
                .map(str::trim)
                .filter(|entry| !entry.is_empty())
                .map(String::from)
                .collect()
        };
        Ok(Self {
            gandr,
            least,
            features: each(features).into_iter().map(FeatureId).collect(),
            systems: each(systems),
        })
    }

    /// Each constraint `running` leaves unmet, in the order the fields are
    /// written.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Unmet::Gandr`] when the least version is above the running
    ///   one; then one [`Unmet::Feature`] per key, in order, the running ledger
    ///   holds at no status [`Status::Implemented`] or [`Status::Partial`];
    ///   then [`Unmet::System`] when systems are named and the running one is
    ///   none of them. Nothing else.
    /// - provides: the toolchain step of `gandr check`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — constraints the running toolchain meets ask nothing;
    ///   a version above it, a key no row holds, a planned feature and a
    ///   foreign system are each unmet by their clause, in field order; a
    ///   version equal to the running one, an implemented and a partial key,
    ///   and the running system among others are met.
    /// - witness: `package::toolchain::tests::each_unmet_constraint_is_refused_by_its_clause_3135`
    #[spec(ensures: |ref ret| ret.len() <= self.features.len().saturating_add(2_usize))]
    #[must_use]
    #[inline]
    pub fn unmet(
        &self,
        running: &Running<'_>,
    ) -> Vec<Unmet>
    {
        let mut unmet = Vec::new();
        if let Some(least) = self.least
            && least > running.version
        {
            unmet.push(Unmet::Gandr {
                asked: self.gandr.trim().to_owned(),
                running: running.version,
            });
        }
        unmet.extend(
            self.features
                .iter()
                .filter(|&key| {
                    !matches!(
                        running.ledger.status(key),
                        Ok(Status::Implemented | Status::Partial)
                    )
                })
                .map(|key| Unmet::Feature { key: key.clone() }),
        );
        if !self.systems.is_empty() && !self.systems.contains(&running.system) {
            unmet.push(Unmet::System {
                asked: self.systems.join(", "),
                running: running.system.clone(),
            });
        }
        unmet
    }
}

impl fmt::Display for Toolchain
{
    /// Writes the manifest's `[toolchain]` table after a blank line: `gandr`
    /// as written, a TOML basic string, and `features` and `systems` arrays of
    /// their entries, one per line, or `[]` when there are none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "\n[toolchain]\ngandr = {}\nfeatures = {}\nsystems = {}\n",
            Basic(&self.gandr),
            Listed(&self.features),
            Listed(&self.systems)
        )
    }
}

/// The toolchain a package is checked by: its version, the features its
/// ledger implements and the system it runs on.
#[derive(Clone, Debug)]
pub struct Running<'ledger>
{
    /// Its version.
    version: Version,
    /// The features ledger it was built with.
    ledger: &'ledger FeatureLedger,
    /// Its system, `<architecture>-<os>`.
    system: String,
}

impl<'ledger> Running<'ledger>
{
    /// The running toolchain, its features those of `ledger`, the one it was
    /// built with.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn this(ledger: &'ledger FeatureLedger) -> Self
    {
        Self {
            version: Version::running(),
            ledger,
            system: format!("{ARCH}-{OS}"),
        }
    }
}

/// A constraint the running toolchain leaves unmet.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unmet
{
    /// `gandr` asks for a version above the running one.
    Gandr
    {
        /// What `gandr` asks, as written.
        asked: String,
        /// The running version.
        running: Version,
    },
    /// A key of `features` the running ledger does not implement.
    Feature
    {
        /// The key.
        key: FeatureId,
    },
    /// `systems` names none the toolchain runs on.
    System
    {
        /// The systems named, joined.
        asked: String,
        /// The system the toolchain runs on.
        running: String,
    },
}

impl fmt::Display for Unmet
{
    /// Writes the clause the constraint is refused by, then what the field
    /// asks and what the toolchain has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Gandr { ref asked, running } => write!(
                f,
                "ToolchainUnmet.gandr: `Package.gandr` asks for gandr `{asked}`, and this \
                 toolchain is gandr {running}"
            ),
            Self::Feature {
                key: FeatureId(ref key),
            } => write!(
                f,
                "ToolchainUnmet.feature.{key}: `Package.features` asks for `{key}`, which this \
                 toolchain's features ledger does not implement"
            ),
            Self::System {
                ref asked,
                ref running,
            } => write!(
                f,
                "ToolchainUnmet.system: `Package.systems` asks for one of `{asked}`, and this \
                 toolchain runs on `{running}`"
            ),
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::FeatureId;
    use super::FeatureLedger;
    use super::Running;
    use super::Separated;
    use super::Toolchain;
    use super::Unconstrained;
    use super::Unmet;
    use super::Version;

    /// The version `$written` spells.
    macro_rules! version {
        ($written:literal) => {
            $written.parse::<Version>().expect("a version")
        };
    }

    #[test]
    fn a_version_reads_two_or_three_numbers()
    {
        assert_eq!(["0.3", "0.3.1", "12.0.07"].map(str::parse::<Version>), [
            Ok(Version {
                major: 0,
                minor: 3,
                patch: 0,
            }),
            Ok(Version {
                major: 0,
                minor: 3,
                patch: 1,
            }),
            Ok(Version {
                major: 12,
                minor: 0,
                patch: 7,
            }),
        ]);
        for written in ["1", "1.2.3.4", "+1.2", "1..2", "", "a.b"] {
            assert_eq!(
                written.parse::<Version>(),
                Err(Unconstrained),
                "`{written}` spells no version"
            );
        }
    }

    #[test]
    fn a_model_s_strings_read_as_its_constraints()
    {
        let read = Toolchain::read(String::from(">=0.3"), Separated(" a , ,b "), Separated(""))
            .expect("the constraints read");
        assert_eq!(
            (read.least, read.features, read.systems),
            (
                Some(version!("0.3")),
                vec![FeatureId(String::from("a")), FeatureId(String::from("b"))],
                Vec::<String>::new()
            ),
            "the least version after `>=`, and the entries trimmed"
        );
        let blank = Toolchain::read(String::from("  "), Separated(""), Separated(" , "))
            .expect("blank reads");
        assert_eq!(
            (blank.least, blank.features.len(), blank.systems.len()),
            (None, 0_usize, 0_usize),
            "a blank constraint asks nothing"
        );
        for written in ["0.3", "<= 0.3", ">= ", ">= three"] {
            assert_eq!(
                Toolchain::read(String::from(written), Separated(""), Separated("")),
                Err(Unconstrained),
                "`{written}` states no constraint"
            );
        }
    }

    #[test]
    fn each_unmet_constraint_is_refused_by_its_clause_3135()
    {
        let ledger = FeatureLedger::built_in().expect("the built-in ledger reads");
        let running = Running {
            version: version!("0.3"),
            ledger: &ledger,
            system: String::from("x86_64-linux"),
        };
        let met = Toolchain::read(
            String::from(">= 0.3"),
            Separated("strict-corpus-root, std-package"),
            Separated("aarch64-macos, x86_64-linux"),
        )
        .expect("the constraints read");
        assert_eq!(
            met.unmet(&running),
            [],
            "the running version, an implemented and a partial feature, and the running \
             system among others are met"
        );
        let unmet = Toolchain::read(
            String::from(">= 0.3.1"),
            Separated("not-a-feature, strict-corpus-root, first-class-environments"),
            Separated("aarch64-macos"),
        )
        .expect("the constraints read");
        assert_eq!(
            unmet.unmet(&running),
            [
                Unmet::Gandr {
                    asked: String::from(">= 0.3.1"),
                    running: version!("0.3"),
                },
                Unmet::Feature {
                    key: FeatureId(String::from("not-a-feature")),
                },
                Unmet::Feature {
                    key: FeatureId(String::from("first-class-environments")),
                },
                Unmet::System {
                    asked: String::from("aarch64-macos"),
                    running: String::from("x86_64-linux"),
                },
            ],
            "a later version, a key no row holds, a planned feature and a foreign system, \
             each by its clause"
        );
        assert_eq!(
            unmet
                .unmet(&running)
                .iter()
                .map(ToString::to_string)
                .map(|line| line.split(':').next().unwrap_or_default().to_owned())
                .collect::<Vec<_>>(),
            [
                "ToolchainUnmet.gandr",
                "ToolchainUnmet.feature.not-a-feature",
                "ToolchainUnmet.feature.first-class-environments",
                "ToolchainUnmet.system",
            ],
            "each refusal is named by its clause"
        );
    }
}
