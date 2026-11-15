//! The simulator of faults: torn, lost, misdirected and corrupt IO, drawn
//! from a seed, so a fault is a seed.
//!
//! An `Io` with faults draws once for each write and each read that it
//! stages, the same draws under the ring and under the blocking form. A
//! torn write writes a prefix of its buffer. A lost write writes nothing
//! and completes as whole. A misdirected write writes its buffer at another
//! position. A corrupt read flips one byte of what it read. The `Io` keeps
//! a log of each fault it drew, so a witness checks the file against it.
//!
//! An `Io` with no faults draws nothing: the check is one branch on an
//! absent value at each stage.

use alloc::vec::Vec;
use core::num::NonZeroU32;

use crate::io::Pending;
use crate::ring::Moved;
use crate::ring::Position;

/// The seed that draws a run's faults.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Seed(pub u64);

/// The odds of a fault: one stage in this many draws one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Odds(pub NonZeroU32);

/// One fault that an `Io` drew for one submission.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fault
{
    /// The write wrote the first `kept` bytes of its buffer alone.
    Torn
    {
        /// The write.
        pending: Pending,
        /// The bytes that it wrote.
        kept: Moved,
    },
    /// The write wrote nothing, and completed as whole.
    Lost
    {
        /// The write.
        pending: Pending,
    },
    /// The write wrote its buffer at `at`, and completed as whole.
    Misdirected
    {
        /// The write.
        pending: Pending,
        /// The position that it wrote at.
        at: Position,
    },
    /// The read gave back its bytes with the byte at `at` flipped.
    Corrupt
    {
        /// The read.
        pending: Pending,
        /// The flipped byte's place in the buffer.
        at: Moved,
    },
}

/// What a drawn fault does to its submission.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Injected
{
    /// Write the first bytes alone.
    Torn(Moved),
    /// Write nothing, and complete as whole.
    Lost,
    /// Write at another position.
    Misdirected(Position),
    /// Flip one byte of what the read gave.
    Corrupt(Moved),
}

/// The state of the draws, and the log of each fault drawn.
#[derive(Debug)]
pub struct Faults
{
    /// The state of the generator.
    state: u64,
    /// One stage in this many draws a fault.
    odds: u32,
    /// Each fault drawn, in the order of its stage.
    log: Vec<Fault>,
}

/// One draw of the generator, below a bound.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Draw(u32);

impl Faults
{
    /// The draws of `seed` at `odds`, with an empty log.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        seed: Seed,
        odds: Odds,
    ) -> Self
    {
        Self {
            state: seed.0,
            odds: odds.0.get(),
            log: Vec::new(),
        }
    }

    /// The next draw of the generator, `splitmix64`, below `bound`, which is
    /// above zero.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &mut self,
        bound: Draw,
    ) -> Draw
    {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut word = self.state;
        word = (word ^ (word >> 30_u32)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        word = (word ^ (word >> 27_u32)).wrapping_mul(0x94d0_49bb_1331_11eb);
        word ^= word >> 31_u32;
        let drawn = word.checked_rem(u64::from(bound.0)).unwrap_or_default();
        Draw(u32::try_from(drawn).unwrap_or_default())
    }

    /// Some when this stage draws a fault.
    ///
    /// # Specification
    /// trivial.
    fn strike(&mut self) -> Option<()>
    {
        (self.below(Draw(self.odds)).0 == 0).then_some(())
    }

    /// The fault of the write `pending` of `asked` bytes at `at`, if the
    /// draw gives one; the log keeps it.
    ///
    /// # Specification
    /// - ensures: a torn write keeps fewer bytes than it asks; a misdirected
    ///   write lands past its own bytes, so it overlaps nothing it was meant to
    ///   write.
    /// - panics: none.
    /// - executable: none — the draw is the generator's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the file after a run holds what the log of its faults
    ///   says, and one seed gives the same log and the same file under each
    ///   form.
    /// - witness: `tests::faults::a_seed_gives_one_log_and_one_file_under_each_form`
    #[inline]
    pub fn write(
        &mut self,
        pending: Pending,
        asked: Moved,
        at: Position,
    ) -> Option<Injected>
    {
        self.strike()?;
        let (injected, fault) = match self.below(Draw(3)).0 {
            0 => {
                let kept = Moved::from(self.below(Draw(u32::from(asked).max(1))).0);
                (Injected::Torn(kept), Fault::Torn { pending, kept })
            },
            1 => (Injected::Lost, Fault::Lost { pending }),
            _ => {
                let away = at.plus(asked).plus(asked);
                (Injected::Misdirected(away), Fault::Misdirected {
                    pending,
                    at: away,
                })
            },
        };
        self.log.push(fault);
        Some(injected)
    }

    /// The fault of the read `pending` of `asked` bytes, if the draw gives
    /// one; the log keeps it.
    ///
    /// # Specification
    /// - ensures: a corrupt read flips a byte inside the bytes it asks.
    /// - panics: none.
    /// - executable: none — the draw is the generator's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Faults::write`].
    /// - witness: `tests::faults::a_seed_gives_one_log_and_one_file_under_each_form`
    #[inline]
    pub fn read(
        &mut self,
        pending: Pending,
        asked: Moved,
    ) -> Option<Injected>
    {
        if u32::from(asked) == 0 {
            return None;
        }
        self.strike()?;
        let at = Moved::from(self.below(Draw(u32::from(asked))).0);
        self.log.push(Fault::Corrupt { pending, at });
        Some(Injected::Corrupt(at))
    }

    /// Each fault drawn, in the order of its stage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn log(&self) -> &[Fault]
    {
        &self.log
    }
}
