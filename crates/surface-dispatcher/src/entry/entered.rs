//! A program's entry run: the declaration that it starts at, the quotas of
//! the exact reals that it holds, and what it came to.
//!
//! The run stage finds the entry and runs it (`evaluate::entry`). The script
//! and the driver give a run its profile and read what it came to, so these
//! types stay below the run stage.

use core::fmt;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Sign;
use gandr_surface_lowering::Arguments;

use crate::entry::evaluation::Evaluation;

/// The declaration a program starts at, and what it takes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Entry
{
    /// The entry's admission position.
    pub constant: ConstantIndex,
    /// Whether it reads the program's arguments.
    pub arguments: Arguments,
}

/// The status a process leaves with: the low eight bits of the integer an
/// entry returns or exits with, as a POSIX `exit` keeps them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExitStatus(u8);

impl From<ExitStatus> for u8
{
    /// The status's byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(status: ExitStatus) -> Self
    {
        status.0
    }
}

impl From<u8> for ExitStatus
{
    /// The status of the byte `code`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(code: u8) -> Self
    {
        Self(code)
    }
}

impl From<&IntegerLiteral> for ExitStatus
{
    /// The low eight bits of `literal`, read in two's complement, so `-1` is
    /// `255` and `256` is `0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the integer modulo 256, taken non-negative.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, a small code, 255, 256, a long magnitude and a
    ///   negative integer.
    /// - witness: `gandr-surface-evaluate::evaluate::entry::tests::an_exit_status_keeps_the_low_byte_1881`
    #[spec(
        captures: [odd = literal.magnitude().as_ref().bytes().last().is_some_and(|digit| digit % 2 == 1)],
        ensures: |ret| (ret.0 % 2 == 1) == odd,
    )]
    #[inline]
    fn from(literal: &IntegerLiteral) -> Self
    {
        let residue = literal
            .magnitude()
            .as_ref()
            .bytes()
            .fold(0_u16, |held, digit| {
                held.saturating_mul(10)
                    .saturating_add(u16::from(digit.saturating_sub(b'0')))
                    .rem_euclid(256)
            });
        let residue = match literal.sign() {
            Sign::NonNegative => residue,
            Sign::Negative => 256_u16.saturating_sub(residue).rem_euclid(256),
        };
        Self(u8::try_from(residue).unwrap_or(u8::MAX))
    }
}

/// What running a program's entry came to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Entered<'source>
{
    /// The entry returned an integer, or exited with one.
    Exited(ExitStatus),
    /// The run ended short of an exit status: unrunnable, blamed, stuck at a
    /// hole or elsewhere, or unfinished, or it returned no integer.
    Ended(Evaluation<'source>),
}

/// The quotas of the exact reals of a run.
///
/// `[reals] profile` in the configuration of the driver names a profile, and a
/// run with no configuration takes [`Self::Default`]. A profile sets every
/// quota of `theory-exact-reals`: the sizes of a plan and of a certificate, the
/// finest precision of `enclose` and the quanta of one `decide`. It also sets
/// the most plans and machines that a run holds.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum RealsProfile
{
    /// The quotas of stage A for a plan, and the default quotas of the
    /// checker. An `enclose` goes to `2^-4096`, and a `decide` runs at most
    /// 1024 quanta. A run holds at most 64 plans and 64 machines.
    #[default]
    Default,
    /// The quotas of a host that serves plans that it does not trust. A plan
    /// holds at most 64 KiB, 4096 nodes, a height of 256 and 16 binders. Its
    /// mantissas hold at most 4096 bits, and its powers go up to 64. A
    /// certificate holds at most 4096 steps and mantissas of 4096 bits. An
    /// `enclose` goes to `2^-256`, a `decide` runs at most 256 quanta, and a
    /// run holds at most 16 plans and 16 machines.
    Bounded,
}

impl RealsProfile
{
    /// Each profile, in the order that a refusal of an unknown name lists
    /// them.
    pub const ALL: [Self; 2] = [Self::Default, Self::Bounded];
}

impl fmt::Display for RealsProfile
{
    /// Write the name of the profile, as the configuration names it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Default => "default",
            Self::Bounded => "bounded",
        })
    }
}

quenchant_shape::reason_enum! {
    /// Why a program has no entry.
    pub mod program_entry {
        /// The program's source declares no `main` at its top level at an
        /// entry's type.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `main` stands at the top level of the source run.
            Undeclared,
        }
    }
}
