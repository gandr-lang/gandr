//! The session loop: lines in, transcript blocks out.
//!
//! # The loop reads declarations, expressions and types
//!
//! The fragment's source is declarations. A line that opens a declaration —
//! its first token a declaration head — is submitted as declarations. A line
//! that is no declaration is read as an expression or a type: the loop
//! submits the probe `def it = <line> ;` — under the first of `it`, `it1`, …
//! that no accepted declaration carries — and keeps it when nothing is
//! refused, so the next line may use the name. The probe's type answers the
//! line: a value's type, a type's sort; where the session evaluates it, its
//! value follows. A refusal is re-ranged to the line, so the diagnostics
//! renderer quotes the line and marks the line's bytes, not the probe.
//! `:type <expression>` answers an expression's type by the same probe,
//! keeping nothing. A goal is a declaration owing its body: a signature with
//! no definition, answered with a goal line `name : T`; a later definition of
//! the same name settles it, and its line becomes a type line. A hole inside
//! a body is outside the fragment, so goals over sub-term holes arrive with
//! the hole surface.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Spelling;
use gandr_surface_grammar::built_in;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_session::Session;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::completeness::completeness;
use crate::completeness::first_token_is_declaration;
use crate::encode::Disposition;
use crate::encode::Echo;
use crate::encode::Naming;
use crate::encode::Offer;
use crate::encode::Standings;
use crate::encode::Subject;
use crate::encode::encode_submission;
use crate::highlight::highlight_source;
use crate::meta::Command;
use crate::meta::HELP;
use crate::meta::Missing;
use crate::meta::command;

quenchant_shape::reason_enum! {
    /// Why finishing the loop submitted nothing.
    pub mod finished {
        /// The reason nothing was submitted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No buffer was waiting.
            Empty,
        }
    }
}

/// What the loop did with one offered line.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoopEvent
{
    /// The line joined a buffer the parser still expects more of, or was
    /// blank.
    Continue,
    /// A block to draw: a submission's results, or a meta-command's answer.
    Block(TranscriptBlock),
    /// The user asked to leave.
    Quit,
}

/// Which prompt a face shows before the next line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Prompt
{
    /// No buffer waits: the next line starts a submission or is a command.
    Fresh,
    /// A buffer waits for the parser's expected tokens.
    Continuing,
}

/// A session fault, rendered: an engine fault, never a verdict about the
/// text.
///
/// The fault borrows the revision it was raised over, which the loop owns
/// only for the submission's duration, so it is carried as its rendering.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Faulted(String);

impl fmt::Display for Faulted
{
    /// Writes the fault's rendering.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Why the loop cannot go on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoopError
{
    /// The session faulted on a revision.
    Fault(Faulted),
}

impl fmt::Display for LoopError
{
    /// Writes what stopped the loop.
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
            Self::Fault(ref fault) => write!(f, "the session faulted: {fault}"),
        }
    }
}

impl core::error::Error for LoopError
{
}

/// The backend identity the loop's checkpoints are stored under.
///
/// # Specification
/// trivial.
fn backend() -> BackendArtifact
{
    BackendArtifact::from(concat!("gandr-surface-repl ", env!("CARGO_PKG_VERSION")).as_bytes())
}

/// A session over the strict root, its checkpoints and kernel records kept in
/// memory.
///
/// # Specification
/// trivial.
fn fresh(grammar: Pbg) -> Session<MemoryCheckpointStore, InMemoryBlockStore>
{
    Session::new(
        grammar,
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
    )
}

/// A block answering `echo` with one line of `kind`.
///
/// # Specification
/// trivial.
fn answer(
    echo: SourceText<'_>,
    kind: OutKind,
    line: String,
) -> TranscriptBlock
{
    TranscriptBlock {
        source: echo.to_string(),
        source_hl: Vec::new(),
        lines: Vec::from([(kind, line)]),
    }
}

/// A file `:load` kept, and the bytes of the accepted text its chunk is, its
/// closing newline left out.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Loaded
{
    /// The file, as `:load` named it.
    path: PathBuf,
    /// Where its chunk starts in the accepted text.
    start: ByteOffset,
    /// Where its chunk ends, before its newline.
    end: ByteOffset,
}

/// What judging a revision did with its chunk.
#[derive(Debug)]
enum Revision
{
    /// The chunk was kept, and the accepted text is the revision.
    Kept(TranscriptBlock),
    /// The chunk was refused, and the accepted text is unchanged.
    Refused(TranscriptBlock),
}

/// The notice a face shows when `path`, a file the loop loaded, changes on
/// disk.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn disk_notice(path: &Path) -> TranscriptBlock
{
    TranscriptBlock {
        source: String::new(),
        source_hl: Vec::new(),
        lines: Vec::from([(
            OutKind::Info,
            format!("`{}` changed on disk; :reload to resubmit", path.display()),
        )]),
    }
}

/// The read-evaluate loop over one session.
///
/// The loop owns the accepted text — every chunk kept so far, each ended by a
/// newline — and the buffer of lines waiting to be submitted; the session
/// judges the accepted text with each new chunk after it.
#[derive(Debug)]
pub struct SessionLoop
{
    /// The session every chunk is submitted to.
    session: Session<MemoryCheckpointStore, InMemoryBlockStore>,
    /// The role table the echo is highlighted with.
    roles: RoleTable,
    /// Every chunk kept so far.
    accepted: String,
    /// Each file `:load` kept, in the order loaded, with its chunk's bytes.
    loaded: Vec<Loaded>,
    /// What each declaration of the accepted text produced.
    standings: Standings,
    /// The lines waiting to be submitted.
    pending: String,
    /// How refusals are rendered.
    style: RenderStyle,
    /// The spelling its types and values are written in.
    spelling: Spelling,
}

impl SessionLoop
{
    /// A loop over a fresh session under the built-in grammar, rendering
    /// refusals under `style`, its types and values in [`Spelling::Unicode`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a loop with nothing accepted and nothing pending, its session
    ///   under the strict root, so each submission is judged as `gandr check
    ///   --goals` judges a strict source.
    /// - provides: the loop every face drives.
    /// - fails: [`PbgError`] when the built-in grammar or its role table does
    ///   not build.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError`] when the built-in grammar or its role table does not build.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh loop has no pending submission, so finishing
    ///   it yields no transcript; its first open form changes the fresh prompt.
    /// - witness: `tests::repl_loop::finishing_an_empty_loop_yields_nothing`
    /// - witness: `tests::repl_loop::an_open_form_continues`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|repl|
        repl.accepted.is_empty() && repl.loaded.is_empty() && repl.pending.is_empty() && repl.standings == Standings::default()
            && repl.style == style && repl.spelling == Spelling::Unicode && matches!(repl.session.last(), Maybe::Absent(_))))]
    #[inline]
    pub fn new(style: RenderStyle) -> Result<Self, PbgError>
    {
        let grammar = built_in()?;
        let roles = RoleTable::build(&grammar)?;
        Ok(Self {
            session: fresh(grammar),
            roles,
            accepted: String::new(),
            loaded: Vec::new(),
            standings: Standings::default(),
            pending: String::new(),
            style,
            spelling: Spelling::Unicode,
        })
    }

    /// This loop, the types its refusals name and the values its runs reach
    /// written in `spelling`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later submission is encoded in `spelling`; nothing
    ///   accepted or pending changes.
    /// - provides: the reader's spelling for every face the loop drives.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a word value printed in each spelling.
    /// - witness: `tests::repl_loop::a_value_is_written_in_the_spelling_asked_782`
    #[spec(ensures: |ref ret| ret.spelling == spelling)]
    #[inline]
    #[must_use]
    pub fn spelling(
        mut self,
        spelling: Spelling,
    ) -> Self
    {
        self.spelling = spelling;
        self
    }

    /// Which prompt a face shows before the next line.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: fresh exactly when no text is pending.
    /// - provides: the prompt and command-admission state.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open form changes the prompt until it is closed.
    /// - witness: `tests::repl_loop::an_open_form_continues`
    #[spec(ensures: |ret| (ret == Prompt::Fresh) == self.pending.is_empty())]
    #[inline]
    #[must_use]
    pub fn prompt(&self) -> Prompt
    {
        if self.pending.is_empty() {
            Prompt::Fresh
        }
        else {
            Prompt::Continuing
        }
    }

    /// Each file `:load` kept, in the order loaded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn loaded(&self) -> impl Iterator<Item = &Path>
    {
        self.loaded.iter().map(|loaded| loaded.path.as_path())
    }

    /// Drop the waiting buffer, as an interrupt at the prompt does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no text waits; accepted declarations remain available.
    /// - provides: interruption without resetting the accepted session.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interrupting an open form prevents its echo while the
    ///   next complete declaration is submitted normally, retaining
    ///   declarations accepted before the interruption.
    /// - witness: `tests::repl_loop::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`
    /// - witness: `tests::repl_loop::multiline_and_interrupted_buffers_preserve_accepted_declarations`
    #[spec(captures: [accepted = self.accepted.len()],
        ensures: self.pending.is_empty() && self.accepted.len() == accepted)]
    #[inline]
    pub fn discard(&mut self)
    {
        self.pending.clear();
    }

    /// Take offered text, normally one line, including pasted line breaks.
    ///
    /// # Specification
    /// - requires: nothing; embedded line terminators are preserved.
    /// - ensures: while no buffer waits, a line opening with `:` is a
    ///   meta-command and answered at once, and a blank line is passed over.
    ///   Any other line joins the buffer; once the buffer is parse-complete it
    ///   is submitted as the next chunk and its block returned, and otherwise
    ///   the loop continues. `:quit` answers [`LoopEvent::Quit`]; `:help` its
    ///   list; `:reset` empties the session; `:load` submits the file's text as
    ///   one chunk, or answers why it could not be read; `:type` submits a
    ///   probe declaration around its expression and answers its type, keeping
    ///   nothing.
    /// - provides: the one entry point every face feeds.
    /// - fails: [`LoopError::Fault`] when the session faults on a revision.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults on a revision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the gate's continue and submit sides, each
    ///   meta-command, a refused chunk, a definition used on the next line, and
    ///   a goal completed later are asserted at their exact events; pasted line
    ///   breaks survive and pending text does not dispatch meta-commands.
    /// - witness: `tests::repl_loop::an_open_form_continues`
    /// - witness: `tests::repl_loop::a_complete_atom_submits`
    /// - witness: `tests::repl_loop::quit_stops_the_loop`
    /// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
    /// - witness: `tests::repl_loop::a_refused_chunk_is_not_kept`
    /// - witness: `tests::repl_loop::multiline_and_interrupted_buffers_preserve_accepted_declarations`
    /// - witness: `tests::repl_loop::the_meta_commands_answer`
    /// - witness: `tests::repl_loop::the_type_command_answers_without_keeping_the_probe`
    /// - witness: `tests::repl_loop::a_loaded_file_is_one_chunk`
    #[spec(captures: [accepted = self.accepted.len()],
        ensures: |ret| match ret {
            Ok(LoopEvent::Continue) => self.accepted.len() == accepted
                && (self.pending.is_empty() || self.pending.ends_with(<&str>::from(line))),
            Ok(LoopEvent::Quit) | Err(_) => self.pending.is_empty() && self.accepted.len() == accepted,
            Ok(LoopEvent::Block(_)) => self.pending.is_empty(),
        })]
    #[inline]
    pub fn offer(
        &mut self,
        line: SourceText<'_>,
    ) -> Result<LoopEvent, LoopError>
    {
        let text = <&str>::from(line);
        if self.pending.is_empty() {
            if let Maybe::Present(command) = command(line) {
                return self.meta(line, command);
            }
            if text.trim().is_empty() {
                return Ok(LoopEvent::Continue);
            }
        }
        else {
            self.pending.push('\n');
        }
        self.pending.push_str(text);
        let status = completeness(
            self.session.grammar(),
            SourceText::from(self.pending.as_str()),
        );
        if !bool::from(status) {
            return Ok(LoopEvent::Continue);
        }
        let chunk = core::mem::take(&mut self.pending);
        if !bool::from(first_token_is_declaration(
            self.session.grammar(),
            SourceText::from(chunk.as_str()),
        )) {
            return self
                .prompt_probe(SourceText::from(chunk.as_str()))
                .map(LoopEvent::Block);
        }
        self.declarations(SourceText::from(chunk.as_str()))
            .map(LoopEvent::Block)
    }

    /// Submit whatever buffer still waits, as the end of input does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a waiting buffer, complete or not, is submitted as a chunk
    ///   and its block answered, and the buffer is then empty; with no buffer
    ///   waiting, the absence says so.
    /// - provides: end-of-input handling, so a buffer left open at the end of a
    ///   pipe is reported rather than dropped.
    /// - fails: [`LoopError::Fault`] when the session faults on the revision.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults on the revision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open buffer is submitted at the end, an empty loop
    ///   answers the absence, and a second finish answers it too.
    /// - witness: `tests::repl_loop::an_incomplete_buffer_is_submitted_at_end_of_input`
    /// - witness: `tests::repl_loop::finishing_an_empty_loop_yields_nothing`
    /// - witness: `tests::repl_loop::finishing_twice_reports_once`
    #[spec(captures: [empty = self.pending.trim().is_empty(), accepted = self.accepted.len()],
        ensures: |ret| self.pending.is_empty() && if empty {
            self.accepted.len() == accepted && matches!(ret, Ok(Maybe::Absent(finished::Absent::Empty)))
        } else {
            match ret {
                Ok(Maybe::Present(_)) => self.accepted.len() >= accepted,
                Ok(Maybe::Absent(_)) => false,
                Err(_) => self.accepted.len() == accepted,
            }
        })]
    #[inline]
    pub fn finish(&mut self) -> Result<Maybe<TranscriptBlock, finished::Absent>, LoopError>
    {
        if self.pending.trim().is_empty() {
            self.pending.clear();
            return Ok(Maybe::Absent(finished::Absent::Empty));
        }
        let chunk = core::mem::take(&mut self.pending);
        self.declarations(SourceText::from(chunk.as_str()))
            .map(Maybe::Present)
    }

    /// Answer the meta-command `command`, typed as `line`.
    ///
    /// # Specification
    /// - requires: no buffer waits.
    /// - ensures: as [`Self::offer`] states for each command.
    /// - provides: the meta-command half of [`Self::offer`].
    /// - fails: [`LoopError::Fault`] when a submission the command makes
    ///   faults.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when a submission the command makes faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Self::offer`]'s meta-command witnesses,
    ///   each answer asserted exactly.
    /// - witness: `tests::repl_loop::the_meta_commands_answer`
    /// - witness: `tests::repl_loop::a_loaded_file_is_one_chunk`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "bounded: the standings are compared with the empty default, which map equality settles at the length"
        )
    )]
    #[spec(requires: self.pending.is_empty(),
        captures: [accepted = self.accepted.len()],
        ensures: |ret| self.pending.is_empty() && match ret {
            Ok(LoopEvent::Quit) => matches!(command, Command::Quit) && self.accepted.len() == accepted,
            Ok(LoopEvent::Continue) => false,
            Ok(LoopEvent::Block(ref block)) => block.source == <&str>::from(line).trim()
                && block.source_hl.is_empty() && match command {
                    Command::Quit => false,
                    Command::Reset => self.accepted.is_empty() && self.loaded.is_empty() && self.standings == Standings::default()
                        && matches!(self.session.last(), Maybe::Absent(_))
                        && matches!(block.lines.as_slice(), [(OutKind::Info, _)]),
                    Command::Help => self.accepted.len() == accepted && block.lines.len() == HELP.len()
                        && block.lines.iter().zip(HELP).all(|(row, expected)|
                            row.0 == OutKind::Info && row.1 == expected),
                    Command::Usage(_) | Command::Unknown(_) => self.accepted.len() == accepted
                        && matches!(block.lines.as_slice(), [(OutKind::Info, _)]),
                    Command::TypeOf(_) => self.accepted.len() == accepted,
                    Command::Load(_) => self.accepted.len() >= accepted,
                    Command::Reload => !block.lines.is_empty(),
                },
            Err(_) => matches!(command, Command::TypeOf(_) | Command::Load(_) | Command::Reload)
                && (self.accepted.len() == accepted || matches!(command, Command::Reload)),
        })]
    fn meta(
        &mut self,
        line: SourceText<'_>,
        command: Command<'_>,
    ) -> Result<LoopEvent, LoopError>
    {
        let echo = SourceText::from(<&str>::from(line).trim());
        let block = match command {
            Command::Quit => return Ok(LoopEvent::Quit),
            Command::Help => TranscriptBlock {
                source: echo.to_string(),
                source_hl: Vec::new(),
                lines: HELP
                    .iter()
                    .map(|row| (OutKind::Info, String::from(*row)))
                    .collect(),
            },
            Command::Reset => {
                self.session = fresh(self.session.grammar().clone());
                self.accepted.clear();
                self.loaded.clear();
                self.standings = Standings::default();
                answer(
                    echo,
                    OutKind::Info,
                    String::from("every declaration is forgotten"),
                )
            },
            Command::Load(path) => match std::fs::read_to_string(path) {
                Ok(text) => {
                    let start = ByteOffset::from(self.accepted.len());
                    let block = self.submit(
                        Echo::new(echo.to_string(), Vec::new()),
                        SourceText::from(text.as_str()),
                        Subject::Declarations,
                    )?;
                    if self.accepted.len() > usize::from(start) {
                        self.loaded.push(Loaded {
                            path: path.to_path_buf(),
                            start,
                            end: ByteOffset::from(usize::from(start).saturating_add(text.len())),
                        });
                    }
                    block
                },
                Err(error) => answer(
                    echo,
                    OutKind::Diag,
                    format!("cannot read `{}`: {error}", path.display()),
                ),
            },
            Command::Reload => self.reload(echo)?,
            Command::TypeOf(expression) => {
                let probe = self.probe_name();
                let chunk = format!("def {probe} = {expression} ;");
                self.submit(
                    Echo::new(echo.to_string(), Vec::new()),
                    SourceText::from(chunk.as_str()),
                    Subject::Probe { name: &probe },
                )?
            },
            Command::Usage(missing) => {
                let usage = match missing {
                    Missing::Path => ":load needs a file: :load <file>",
                    Missing::Expression => ":type needs an expression: :type <expression>",
                };
                answer(echo, OutKind::Info, String::from(usage))
            },
            Command::Unknown(word) => answer(
                echo,
                OutKind::Info,
                format!("no command `:{word}`; :help lists them"),
            ),
        };
        Ok(LoopEvent::Block(block))
    }

    /// A name no accepted declaration carries, for a `:type` probe.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `it` when no accepted declaration is named so, otherwise the
    ///   first of `it1`, `it2`, … that none is.
    /// - provides: a probe that shadows nothing the expression may name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a probe after a declaration named `it` still answers
    ///   the expression's type.
    /// - witness: `tests::repl_loop::the_type_command_answers_without_keeping_the_probe`
    /// - witness: `tests::repl_loop::a_refused_type_probe_is_reported_under_the_first_free_probe_name`
    #[spec(ensures: |ret|
        self.standings.names(SourceFragment::from(ret.as_str())) == Naming::Free
            && if self.standings.names(SourceFragment::from("it")) == Naming::Free { ret == "it" }
            else { ret.strip_prefix("it").is_some_and(|suffix|
                !suffix.starts_with('0') && suffix.parse::<usize>().is_ok_and(|number| number > 0)) })]
    fn probe_name(&self) -> String
    {
        let mut name = String::from("it");
        let mut suffix = 0_usize;
        while self.standings.names(SourceFragment::from(name.as_str())) == Naming::Taken {
            suffix = suffix.saturating_add(1);
            name = format!("it{suffix}");
        }
        name
    }

    /// Submit `chunk`, typed by the user, as declarations.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chunk is echoed with its highlight spans and submitted as
    ///   [`Self::submit`] states.
    /// - provides: the submission of a typed buffer.
    /// - fails: [`LoopError::Fault`] when the session faults.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Self::offer`]'s witnesses, the echo and its
    ///   spans asserted.
    /// - witness: `tests::repl_loop::a_submission_carries_highlight_spans`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|block|
        block.source == <&str>::from(chunk) && block.source_hl.iter().all(|span|
            block.source.is_char_boundary(usize::from(span.range.start()))
                && block.source.is_char_boundary(usize::from(span.range.end()))))) ]
    fn declarations(
        &mut self,
        chunk: SourceText<'_>,
    ) -> Result<TranscriptBlock, LoopError>
    {
        let highlights = highlight_source(self.session.grammar(), &self.roles, chunk);
        let echo = Echo::new(chunk.to_string(), highlights);
        self.submit(echo, chunk, Subject::Declarations)
    }

    /// Submit a complete buffer that is no declaration as a kept probe.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the buffer is wrapped in the probe `def {name} = {buffer} ;`
    ///   under the first free probe name, submitted as a prompt probe, and
    ///   echoed as the buffer the user typed; the probe is kept when nothing is
    ///   refused, so the next line may use the name.
    /// - provides: the prompt's reading of an expression or a type.
    /// - fails: [`LoopError::Fault`] when the session faults.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an expression at the prompt is kept and its name is
    ///   usable on the next line.
    /// - witness: `tests::repl_loop::an_expression_is_read_as_a_probe`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|block|
        block.source == <&str>::from(chunk)))]
    fn prompt_probe(
        &mut self,
        chunk: SourceText<'_>,
    ) -> Result<TranscriptBlock, LoopError>
    {
        let probe = self.probe_name();
        let highlights = highlight_source(self.session.grammar(), &self.roles, chunk);
        let echo = Echo::new(<&str>::from(chunk).to_owned(), highlights);
        let capacity = probe
            .len()
            .saturating_add(<&str>::from(chunk).len())
            .saturating_add("def ".len())
            .saturating_add(" = ".len())
            .saturating_add(" ;".len());
        let mut wrapped = String::with_capacity(capacity);
        wrapped.push_str("def ");
        wrapped.push_str(&probe);
        wrapped.push_str(" = ");
        let line_start = ByteOffset::from(wrapped.len());
        wrapped.push_str(<&str>::from(chunk));
        wrapped.push_str(" ;");
        self.submit(echo, SourceText::from(wrapped.as_str()), Subject::Prompt {
            name: &probe,
            line_start,
        })
    }

    /// Submit the accepted text with `chunk` after it, and keep the chunk when
    /// the encoder says so.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the session judges the revision of the accepted text followed
    ///   by `chunk`; the block is the encoder's for that answer; when the
    ///   encoder keeps the chunk, the accepted text gains it and a newline and
    ///   the standings become the revision's; otherwise both are unchanged.
    /// - provides: the one path every submission takes.
    /// - fails: [`LoopError::Fault`] when the session faults; the accepted text
    ///   is then unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Self::offer`]'s witnesses, a kept and a
    ///   dropped chunk each asserted by what the next submission sees.
    /// - witness: `tests::repl_loop::a_refused_chunk_is_not_kept`
    /// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
    #[spec(captures: [accepted = self.accepted.len()],
        ensures: |ret| if ret.is_err() || matches!(subject, Subject::Probe { .. }) {
            self.accepted.len() == accepted
        } else {
            self.accepted.len() == accepted
                || (self.accepted.len() == accepted.saturating_add(<&str>::from(chunk).len()).saturating_add(1)
                    && self.accepted.strip_suffix('\n').is_some_and(|text| text.ends_with(<&str>::from(chunk))))
        })]
    fn submit(
        &mut self,
        echo: Echo,
        chunk: SourceText<'_>,
        subject: Subject<'_>,
    ) -> Result<TranscriptBlock, LoopError>
    {
        let end = ByteOffset::from(self.accepted.len());
        Ok(match self.revise(echo, end, end, chunk, subject)? {
            Revision::Kept(block) | Revision::Refused(block) => block,
        })
    }

    /// Submit the accepted text with `chunk` in place of the bytes from
    /// `start` to `end`, and keep the revision when the encoder says so.
    ///
    /// # Specification
    /// - requires: `start` and `end` are character boundaries of the accepted
    ///   text, `start` no later than `end`, and `end` is its length or the
    ///   offset of the newline closing a chunk.
    /// - ensures: the session judges the accepted text with `chunk` in place of
    ///   those bytes, the text after them following it; the encoder reads every
    ///   report from `start` on as the chunk's, so the declarations after it
    ///   are judged again with it. When the encoder keeps it, the accepted text
    ///   becomes the revision, closed by a newline, and the standings the
    ///   revision's; otherwise both are unchanged.
    /// - provides: the one path every submission and resubmission takes.
    /// - fails: [`LoopError::Fault`] when the session faults; the accepted text
    ///   is then unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chunk kept at the end and one dropped, each
    ///   asserted by what the next submission sees, and a reloaded file's chunk
    ///   replaced in the middle with the declaration after it judged again.
    /// - witness: `tests::repl_loop::a_refused_chunk_is_not_kept`
    /// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
    /// - witness: `tests::repl_loop::a_reloaded_file_replaces_its_chunk`
    #[spec(requires: start <= end && usize::from(end) <= self.accepted.len(),
        ensures: |ret| !matches!(ret, Ok(Revision::Kept(_)))
            || (!matches!(subject, Subject::Probe { .. })
                && self.accepted.ends_with('\n')
                && self.accepted.get(usize::from(start)..).is_some_and(|after| after.starts_with(<&str>::from(chunk)))),
    )]
    fn revise(
        &mut self,
        echo: Echo,
        start: ByteOffset,
        end: ByteOffset,
        chunk: SourceText<'_>,
        subject: Subject<'_>,
    ) -> Result<Revision, LoopError>
    {
        let chunk = <&str>::from(chunk);
        let before = self.accepted.get(.. usize::from(start)).unwrap_or_default();
        let after = self.accepted.get(usize::from(end) ..).unwrap_or_default();
        let after = after.strip_suffix('\n').unwrap_or(after);
        let mut revision = String::with_capacity(
            before
                .len()
                .saturating_add(chunk.len())
                .saturating_add(after.len())
                .saturating_add(1),
        );
        revision.push_str(before);
        revision.push_str(chunk);
        revision.push_str(after);
        let encoded = {
            let submission = self
                .session
                .submit(SourceText::from(revision.as_str()))
                .map_err(|fault| LoopError::Fault(Faulted(fault.to_string())))?;
            encode_submission(
                Offer {
                    echo,
                    chunk: start,
                    subject,
                },
                submission,
                self.session.last(),
                &self.standings,
                self.style,
                self.spelling,
            )
        };
        Ok(match encoded.disposition {
            Disposition::Kept(standings) => {
                revision.push('\n');
                self.accepted = revision;
                self.standings = standings;
                Revision::Kept(encoded.block)
            },
            Disposition::Dropped => Revision::Refused(encoded.block),
        })
    }

    /// Resubmit each loaded file whose text on disk differs from its chunk, in
    /// the order loaded, in place of that chunk; answer `echo`.
    ///
    /// # Specification
    /// - requires: no buffer waits.
    /// - ensures: each loaded file is read again; one that cannot be read
    ///   answers why and keeps its chunk; one whose text is its chunk's is left
    ///   alone; any other is submitted as [`Self::revise`] states, in place of
    ///   its chunk, the declarations after it judged again. A kept file answers
    ///   that it was resubmitted, then the encoder's lines, and the chunks
    ///   after it move by the change in its length; a refused one answers the
    ///   encoder's lines, then that it keeps its earlier chunk. With nothing to
    ///   resubmit, the answer says so.
    /// - provides: `:reload`.
    /// - fails: [`LoopError::Fault`] when a resubmission faults; the files
    ///   resubmitted before it stay resubmitted.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when a resubmission faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loaded file rewritten on disk, reloaded, answers
    ///   its new type with the declaration after it judged again; a rewrite the
    ///   declaration after it refuses keeps the earlier chunk; reloading an
    ///   unchanged file answers that nothing changed.
    /// - witness: `tests::repl_loop::a_reloaded_file_replaces_its_chunk`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|block|
        block.source == <&str>::from(echo) && !block.lines.is_empty()))]
    fn reload(
        &mut self,
        echo: SourceText<'_>,
    ) -> Result<TranscriptBlock, LoopError>
    {
        let mut lines: Vec<(OutKind, String)> = Vec::new();
        // The files move out for the walk, as resubmitting borrows the loop;
        // they move back however it ends.
        let mut files = core::mem::take(&mut self.loaded);
        let walked = 'files: {
            for index in 0 .. files.len() {
                let Some(file) = files.get(index)
                else {
                    break;
                };
                let (start, end_before) = (file.start, file.end);
                let text = match std::fs::read_to_string(&file.path) {
                    Ok(text) => text,
                    Err(error) => {
                        lines.push((
                            OutKind::Diag,
                            format!("cannot read `{}`: {error}", file.path.display()),
                        ));
                        continue;
                    },
                };
                if self
                    .accepted
                    .get(usize::from(start) .. usize::from(end_before))
                    == Some(text.as_str())
                {
                    continue;
                }
                let echoed = Echo::new(echo.to_string(), Vec::new());
                let revised = match self.revise(
                    echoed,
                    start,
                    end_before,
                    SourceText::from(text.as_str()),
                    Subject::Declarations,
                ) {
                    Ok(revised) => revised,
                    Err(fault) => break 'files Err(fault),
                };
                match revised {
                    Revision::Kept(block) => {
                        lines.push((
                            OutKind::Info,
                            format!("`{}` resubmitted", file.path.display()),
                        ));
                        lines.extend(block.lines);
                        let end = usize::from(start).saturating_add(text.len());
                        for later in &mut files {
                            if later.start >= end_before {
                                later.start = ByteOffset::from(
                                    usize::from(later.start)
                                        .saturating_sub(usize::from(end_before))
                                        .saturating_add(end),
                                );
                                later.end = ByteOffset::from(
                                    usize::from(later.end)
                                        .saturating_sub(usize::from(end_before))
                                        .saturating_add(end),
                                );
                            }
                        }
                        if let Some(reloaded) = files.get_mut(index) {
                            reloaded.end = ByteOffset::from(end);
                        }
                    },
                    Revision::Refused(block) => {
                        lines.extend(block.lines);
                        lines.push((
                            OutKind::Info,
                            format!("`{}` keeps its earlier chunk", file.path.display()),
                        ));
                    },
                }
            }
            Ok(())
        };
        self.loaded = files;
        walked?;
        if lines.is_empty() {
            lines.push((
                OutKind::Info,
                String::from("no loaded file changed on disk"),
            ));
        }
        Ok(TranscriptBlock {
            source: echo.to_string(),
            source_hl: Vec::new(),
            lines,
        })
    }
}
