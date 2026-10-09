//! The meta-commands: lines opening with `:` that speak to the loop rather
//! than to the session.

use std::path::Path;

use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a line is no meta-command.
    pub mod commanded {
        /// The reason the line is source text.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The line does not open with `:` once leading space is skipped.
            Source,
        }
    }
}

/// The lines `:help` answers with, one per command.
pub const HELP: [&str; 6] = [
    "Enter declarations; a buffer is submitted once the parser expects no further token.",
    ":type <expression>  the type of an expression, as `def it = <expression> ;` checks it",
    ":load <file>        submit a file's declarations as one chunk",
    ":reset              forget every declaration",
    ":help               this list",
    ":quit, :q           leave",
];

/// A command missing its argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Missing
{
    /// `:load` without a path.
    Path,
    /// `:type` without an expression.
    Expression,
}

/// A meta-command line, read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Command<'line>
{
    /// `:help`: list the commands.
    Help,
    /// `:quit` or `:q`: leave the loop.
    Quit,
    /// `:reset`: forget every declaration.
    Reset,
    /// `:load <file>`: submit the file's text as one chunk.
    Load(&'line Path),
    /// `:type <expression>`: the expression's type, by a probe never kept.
    TypeOf(SourceText<'line>),
    /// A known command without the argument it needs.
    Usage(Missing),
    /// A word no command answers to, as typed.
    Unknown(SourceText<'line>),
}

/// The meta-command `line` spells.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a line whose first non-space character is `:` is read as a
///   command: its word is the text up to the first space, its argument the rest
///   with surrounding space trimmed. `:help`, `:quit`, `:q` and `:reset` ignore
///   an argument; `:load` and `:type` take theirs, or are a usage answer
///   without one; any other word is unknown. Every other line is source text.
/// - provides: the loop's reading of a line typed while no buffer waits.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every command, each argument-taking command bare, an
///   unknown word and a source line are asserted at their exact reading.
/// - witness: `meta::tests::every_command_reads_exactly`
pub fn command(line: SourceText<'_>) -> Maybe<Command<'_>, commanded::Absent>
{
    let Some(rest) = <&str>::from(line).trim_start().strip_prefix(':')
    else {
        return Maybe::Absent(commanded::Absent::Source);
    };
    let (word, argument) = match rest.split_once(char::is_whitespace) {
        | Some((word, argument)) => (word, argument.trim()),
        | None => (rest.trim_end(), ""),
    };
    Maybe::Present(match (word, argument.is_empty()) {
        | ("help", _) => Command::Help,
        | ("quit" | "q", _) => Command::Quit,
        | ("reset", _) => Command::Reset,
        | ("load", false) => Command::Load(Path::new(argument)),
        | ("load", true) => Command::Usage(Missing::Path),
        | ("type", false) => Command::TypeOf(SourceText::from(argument)),
        | ("type", true) => Command::Usage(Missing::Expression),
        | (..) => Command::Unknown(SourceText::from(rest.trim_end())),
    })
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Command;
    use super::Missing;
    use super::command;
    use super::commanded;

    /// Each command reads as itself, an argument-taking command without its
    /// argument as a usage answer, an unknown word as unknown, and a line not
    /// opening with `:` as source.
    #[test]
    fn every_command_reads_exactly()
    {
        assert_eq!(command(":help".into()), Maybe::Present(Command::Help));
        assert_eq!(command("  :quit  ".into()), Maybe::Present(Command::Quit));
        assert_eq!(command(":q".into()), Maybe::Present(Command::Quit));
        assert_eq!(command(":reset now".into()), Maybe::Present(Command::Reset));
        assert_eq!(
            command(":load  dir/a file.gandr ".into()),
            Maybe::Present(Command::Load(Path::new("dir/a file.gandr")))
        );
        assert_eq!(
            command(":load".into()),
            Maybe::Present(Command::Usage(Missing::Path))
        );
        assert_eq!(
            command(":type answer".into()),
            Maybe::Present(Command::TypeOf(SourceText::from("answer")))
        );
        assert_eq!(
            command(":type   ".into()),
            Maybe::Present(Command::Usage(Missing::Expression))
        );
        assert_eq!(
            command(":quux 1".into()),
            Maybe::Present(Command::Unknown(SourceText::from("quux 1")))
        );
        assert_eq!(
            command("def a = 1 ;".into()),
            Maybe::Absent(commanded::Absent::Source)
        );
    }
}
