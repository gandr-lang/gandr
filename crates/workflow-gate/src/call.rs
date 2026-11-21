//! The boundary to another program: one call, its answer, and the parts of a
//! run.

use alloc::collections::BTreeMap;
use core::fmt;
use core::time::Duration;
use std::io::Write as _;
use std::path::Path;
use std::process::Child;
use std::process::Command;
use std::process::Stdio;
use std::sync::Mutex;
use std::time::Instant;

use crate::error::GateError;

/// The name of a part of a run, or of a text that a run reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Part(&'static str);

impl From<&'static str> for Part
{
    /// Names the part `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the line of a part ends with its name, so an emptied
    ///   name changes the asserted line.
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    fn from(name: &'static str) -> Self
    {
        Self(name)
    }
}

impl fmt::Display for Part
{
    /// Writes the part's name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the line of a part ends with its name, so writing
    ///   nothing changes the asserted line.
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// The bytes that a program printed, or that a file holds.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Answer(Vec<u8>);

impl From<Vec<u8>> for Answer
{
    /// The answer whose bytes are `bytes`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each line of a list comes from an answer of git, so
    ///   an emptied answer changes the list of the script.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for Answer
{
    /// The bytes of the answer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each line of a list comes from an answer of git, so
    ///   an empty slice changes the list of the script.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// A time of a run, written as milliseconds with one decimal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Elapsed(Duration);

impl From<Duration> for Elapsed
{
    /// The time `time`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — 1,250 microseconds read as `1.2 ms`, which a time
    ///   read as zero does not.
    /// - witness: `call::tests::a_time_is_milliseconds_with_one_decimal`
    #[inline]
    fn from(time: Duration) -> Self
    {
        Self(time)
    }
}

impl fmt::Display for Elapsed
{
    /// Writes the time as milliseconds with one decimal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the whole milliseconds in six columns from the right, a
    ///   point, the tenths of a millisecond with no rounding up, and ` ms`.
    /// - provides: one form for each time that a run prints.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — 1,250 microseconds, 99 microseconds and 2 seconds;
    ///   tenths taken from the whole microseconds, or a width of another count,
    ///   changes an asserted text.
    /// - witness: `call::tests::a_time_is_milliseconds_with_one_decimal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let tenths = self.0.as_micros().checked_div(100).unwrap_or_default();
        let whole = tenths.checked_div(10).unwrap_or_default();
        let part = tenths.checked_rem(10).unwrap_or_default();
        write!(f, "{whole:>6}.{part} ms")
    }
}

/// The parts of a run: the name of each call and its time.
#[repr(transparent)]
#[derive(Debug, Default)]
pub struct Parts(Mutex<Vec<(Part, Duration)>>);

impl Parts
{
    /// Adds one call of `part` that took `elapsed`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: one row for each call, growth within the calls of the run
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count of a part is the count of its calls, so a
    ///   call that adds no row changes the asserted count.
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    pub fn add(
        &self,
        part: Part,
        elapsed: Duration,
    )
    {
        if let Ok(mut rows) = self.0.lock() {
            rows.push((part, elapsed));
        }
    }
}

impl fmt::Display for Parts
{
    /// Writes one line for each part: the sum of its times, the count of its
    /// calls and its name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the parts in the order of their names, each as `gate:`, its
    ///   time, its count before `call(s)` and its name. The time of a call runs
    ///   from its start to its answer in the run's hands.
    /// - provides: the cost of a run beside its work, part by part.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Cost
    /// - allocation: one sum for each part, diagnostic
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run of two commits with one tree and a run with two
    ///   trees; a count that is the sum of all calls, or a part with no line,
    ///   changes the asserted lines.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let mut sums: BTreeMap<Part, (u32, Duration)> = BTreeMap::new();
        if let Ok(rows) = self.0.lock() {
            for &(part, elapsed) in rows.iter() {
                let sum = sums.entry(part).or_default();
                sum.0 = sum.0.saturating_add(1);
                sum.1 = sum.1.saturating_add(elapsed);
            }
        }
        for (part, (count, elapsed)) in sums {
            writeln!(
                f,
                "gate: {}  {count:>3} call(s)  {part}",
                Elapsed::from(elapsed)
            )?;
        }
        Ok(())
    }
}

/// One call of a program: its part of the run, its name, its arguments and
/// the text for its standard input.
#[derive(Clone, Copy, Debug)]
pub struct Program<'call>
{
    /// The part of the run that the call is.
    pub part: Part,
    /// The program.
    pub name: &'call str,
    /// The arguments.
    pub arguments: &'call [&'call str],
    /// The text for the standard input. An empty text gives the program no
    /// input.
    pub input: &'call str,
}

/// A program that runs, from its start to its answer.
#[derive(Debug)]
pub struct Running<'call>
{
    /// The call.
    program: Program<'call>,
    /// When the program started.
    start: Instant,
    /// The process.
    child: Child,
}

impl<'call> Program<'call>
{
    /// The refusal of this call for `reason`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the text of the command, error path
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the refusal of a fake Cargo that fails names the
    ///   program and its arguments, so a refusal with no command changes the
    ///   asserted message.
    /// - witness: `tests::cli::a_failed_cargo_is_refused_by_its_command`
    #[inline]
    fn refused(
        &self,
        reason: String,
    ) -> GateError
    {
        GateError::Command {
            command: format!("{} {}", self.name, self.arguments.join(" ")),
            reason,
        }
    }

    /// Starts the program in `cwd`, and does not wait for it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the program runs, with its standard output and its standard
    ///   error held for [`Running::finish`].
    /// - provides: two programs at the same time with no thread, since the
    ///   caller starts each one before it takes an answer.
    /// - fails: [`GateError::Command`] with the program and its arguments when
    ///   it does not start.
    /// - panics: none.
    /// - executable: none — the outcome is the external process's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the command of the process, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the lists of the script, each line from a started
    ///   program; a program that never starts changes each list.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    pub fn start(
        self,
        cwd: &Path,
    ) -> Result<Running<'call>, GateError>
    {
        let start = Instant::now();
        let child = Command::new(self.name)
            .args(self.arguments)
            .current_dir(cwd)
            .stdin(if self.input.is_empty() {
                Stdio::null()
            }
            else {
                Stdio::piped()
            })
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| self.refused(error.to_string()))?;
        Ok(Running {
            program: self,
            start,
            child,
        })
    }
}

impl Running<'_>
{
    /// Waits for the program and gives what it printed. The call is one row
    /// of its part in `parts`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the standard output of the program when it ends with success.
    ///   `git grep` ends with 1 when no file holds its pattern, and that end is
    ///   a success with an empty answer.
    /// - provides: the one boundary of this crate to another program.
    /// - fails: [`GateError::Command`] with the program, its arguments and its
    ///   standard error when it ends with a failure, and [`GateError::Thread`]
    ///   when the thread of its input does not start.
    /// - panics: none.
    /// - executable: none — the outcome is the external process's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the answer of the program, growth within what the program
    ///   prints
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fake Cargo that fails, and a grep whose pattern no
    ///   file of crate `c` holds at tree three; a failure read as an answer
    ///   changes the exit status, and an end with 1 read as a failure refuses
    ///   the run of tree three.
    /// - witness: `tests::cli::a_failed_cargo_is_refused_by_its_command`
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "io: the thread writes the program's input while this one reads its output, so neither pipe fills; the tool holds no pool"
        )
    )]
    #[inline]
    pub fn finish(
        mut self,
        parts: &Parts,
    ) -> Result<Answer, GateError>
    {
        let program = self.program;
        let waited = match self.child.stdin.take() {
            Some(mut pipe) => std::thread::scope(|scope| {
                let writer = std::thread::Builder::new()
                    .spawn_scoped(scope, move || pipe.write_all(program.input.as_bytes()))
                    .map_err(|_error| GateError::Thread {
                        part: program.part.to_string(),
                    });
                let waited = self.child.wait_with_output();
                let _sent = writer?.join();
                Ok(waited)
            })?,
            None => self.child.wait_with_output(),
        };
        let output = waited.map_err(|error| program.refused(error.to_string()))?;
        parts.add(program.part, self.start.elapsed());
        let no_file =
            program.arguments.first() == Some(&"grep") && output.status.code() == Some(1_i32);
        if output.status.success() || no_file {
            Ok(Answer::from(output.stdout))
        }
        else {
            Err(program.refused(String::from_utf8_lossy(&output.stderr).trim().to_owned()))
        }
    }
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;

    use super::Elapsed;

    #[test]
    fn a_time_is_milliseconds_with_one_decimal()
    {
        assert_eq!(
            Elapsed::from(Duration::from_micros(1_250)).to_string(),
            "     1.2 ms"
        );
        assert_eq!(
            Elapsed::from(Duration::from_micros(99)).to_string(),
            "     0.0 ms"
        );
        assert_eq!(
            Elapsed::from(Duration::from_secs(2)).to_string(),
            "  2000.0 ms"
        );
    }
}
