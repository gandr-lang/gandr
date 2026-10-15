//! How much of its inputs a sweep visits: its sample under every
//! pull-request profile, everything under the nightly one.

use anodized::spec;

/// The nextest profile that runs every sweep whole.
pub const SWEEPS_PROFILE: &str = "sweeps";

/// The variable nextest names the running profile in.
const PROFILE: &str = "NEXTEST_PROFILE";

/// How much of its inputs a sweep visits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Coverage
{
    /// The stated sample: every pull-request profile, `cargo test`, and any
    /// run outside nextest.
    Sampled,
    /// Every input: the `sweeps` profile, nightly.
    Full,
}

/// A nextest profile's name, as `NEXTEST_PROFILE` spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Profile<'name>(pub &'name str);

impl Coverage
{
    /// The coverage of a run under `profile`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Coverage::Full`] exactly under [`SWEEPS_PROFILE`].
    /// - provides: the one knob between a sweep's two budgets.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sweeps profile, each pull-request profile and an
    ///   empty name; a prefix match or a default of full changes an answer.
    /// - witness: `coverage::tests::only_the_sweeps_profile_runs_whole`
    #[spec(ensures: |ret| (ret == Self::Full) == (profile.0 == SWEEPS_PROFILE))]
    #[inline]
    #[must_use]
    pub fn of(profile: Profile<'_>) -> Self
    {
        if profile.0 == SWEEPS_PROFILE {
            Self::Full
        }
        else {
            Self::Sampled
        }
    }

    /// The coverage the running nextest profile asks for; sampled outside
    /// nextest.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Coverage::of`] the profile `NEXTEST_PROFILE` names, which
    ///   nextest sets for every test it runs; [`Coverage::Sampled`] when the
    ///   variable is unset or not Unicode.
    /// - provides: what a sweep test reads before choosing its inputs.
    /// - panics: none.
    /// - executable: none — the outcome is the environment's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — [`Coverage::of`] carries the decision; this reads the
    ///   variable nextest documents.
    /// - witness: `coverage::tests::only_the_sweeps_profile_runs_whole`
    #[inline]
    #[must_use]
    pub fn asked() -> Self
    {
        std::env::var(PROFILE).map_or(Self::Sampled, |profile| Self::of(Profile(&profile)))
    }
}

#[cfg(test)]
mod tests
{
    use super::Coverage;
    use super::Profile;

    #[test]
    fn only_the_sweeps_profile_runs_whole()
    {
        assert_eq!(Coverage::of(Profile("sweeps")), Coverage::Full);
        for profile in [
            "default",
            "ci",
            "ci-enforcing",
            "coverage",
            "sweeps-old",
            "",
        ] {
            assert_eq!(
                Coverage::of(Profile(profile)),
                Coverage::Sampled,
                "{profile}"
            );
        }
    }
}
