//! The session loop: lines in, transcript blocks out.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::built_in;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_session::Session;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::completeness::completeness;
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
            | Self::Fault(ref fault) => write!(f, "the session faulted: {fault}"),
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
    /// What each declaration of the accepted text produced.
    standings: Standings,
    /// The lines waiting to be submitted.
    pending: String,
    /// How refusals are rendered.
    style: RenderStyle,
}

impl SessionLoop
{
    /// A loop over a fresh session under the built-in grammar, rendering
    /// refusals under `style`.
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
    /// - hypothesis: L3 — every loop witness starts here.
    /// - witness: `loop::tests::finishing_an_empty_loop_yields_nothing`
    #[inline]
    pub fn new(style: RenderStyle) -> Result<Self, PbgError>
    {
        let grammar = built_in()?;
        let roles = RoleTable::build(&grammar)?;
        Ok(Self {
            session: fresh(grammar),
            roles,
            accepted: String::new(),
            standings: Standings::default(),
            pending: String::new(),
            style,
        })
    }

    /// Which prompt a face shows before the next line.
    ///
    /// # Specification
    /// trivial.
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

    /// Drop the waiting buffer, as an interrupt at the prompt does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn discard(&mut self)
    {
        self.pending.clear();
    }

    /// Take one line.
    ///
    /// # Specification
    /// - requires: `line` carries no line terminator.
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
    ///   a goal completed later are asserted at their exact events.
    /// - witness: `loop::tests::an_open_form_continues`
    /// - witness: `loop::tests::a_complete_atom_submits`
    /// - witness: `loop::tests::quit_stops_the_loop`
    /// - witness: `loop::tests::a_definition_is_visible_on_the_next_line`
    /// - witness: `loop::tests::a_refused_chunk_is_not_kept`
    /// - witness: `loop::tests::the_meta_commands_answer`
    /// - witness: `loop::tests::the_type_command_answers_without_keeping_the_probe`
    /// - witness: `loop::tests::a_loaded_file_is_one_chunk`
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
    /// - witness: `loop::tests::an_incomplete_buffer_is_submitted_at_end_of_input`
    /// - witness: `loop::tests::finishing_an_empty_loop_yields_nothing`
    /// - witness: `loop::tests::finishing_twice_reports_once`
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
    /// - witness: `loop::tests::the_meta_commands_answer`
    /// - witness: `loop::tests::a_loaded_file_is_one_chunk`
    fn meta(
        &mut self,
        line: SourceText<'_>,
        command: Command<'_>,
    ) -> Result<LoopEvent, LoopError>
    {
        let echo = SourceText::from(<&str>::from(line).trim());
        let block = match command {
            | Command::Quit => return Ok(LoopEvent::Quit),
            | Command::Help => TranscriptBlock {
                source: echo.to_string(),
                source_hl: Vec::new(),
                lines: HELP
                    .iter()
                    .map(|row| (OutKind::Info, String::from(*row)))
                    .collect(),
            },
            | Command::Reset => {
                self.session = fresh(self.session.grammar().clone());
                self.accepted.clear();
                self.standings = Standings::default();
                answer(
                    echo,
                    OutKind::Info,
                    String::from("every declaration is forgotten"),
                )
            },
            | Command::Load(path) => match std::fs::read_to_string(path) {
                | Ok(text) => self.submit(
                    Echo::new(echo.to_string(), Vec::new()),
                    SourceText::from(text.as_str()),
                    Subject::Declarations,
                )?,
                | Err(error) => answer(
                    echo,
                    OutKind::Diag,
                    format!("cannot read `{}`: {error}", path.display()),
                ),
            },
            | Command::TypeOf(expression) => {
                let probe = self.probe_name();
                let chunk = format!("def {probe} = {expression} ;");
                self.submit(
                    Echo::new(echo.to_string(), Vec::new()),
                    SourceText::from(chunk.as_str()),
                    Subject::Probe { name: &probe },
                )?
            },
            | Command::Usage(missing) => {
                let usage = match missing {
                    | Missing::Path => ":load needs a file: :load <file>",
                    | Missing::Expression => ":type needs an expression: :type <expression>",
                };
                answer(echo, OutKind::Info, String::from(usage))
            },
            | Command::Unknown(word) => answer(
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
    /// - witness: `loop::tests::the_type_command_answers_without_keeping_the_probe`
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
    /// - witness: `loop::tests::a_submission_carries_highlight_spans`
    fn declarations(
        &mut self,
        chunk: SourceText<'_>,
    ) -> Result<TranscriptBlock, LoopError>
    {
        let highlights = highlight_source(self.session.grammar(), &self.roles, chunk);
        let echo = Echo::new(chunk.to_string(), highlights);
        self.submit(echo, chunk, Subject::Declarations)
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
    /// - witness: `loop::tests::a_refused_chunk_is_not_kept`
    /// - witness: `loop::tests::a_definition_is_visible_on_the_next_line`
    fn submit(
        &mut self,
        echo: Echo,
        chunk: SourceText<'_>,
        subject: Subject<'_>,
    ) -> Result<TranscriptBlock, LoopError>
    {
        let chunk = <&str>::from(chunk);
        let mut revision = String::with_capacity(self.accepted.len().saturating_add(chunk.len()));
        revision.push_str(&self.accepted);
        let start = ByteOffset::from(revision.len());
        revision.push_str(chunk);
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
            )
        };
        if let Disposition::Kept(standings) = encoded.disposition {
            revision.push('\n');
            self.accepted = revision;
            self.standings = standings;
        }
        Ok(encoded.block)
    }
}
