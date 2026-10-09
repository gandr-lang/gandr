//! What one step prints, in order: its reports and its ledger lines.
//!
//! # The verb decides, the dispatcher's `shown` decides it
//!
//! Which declaration a verb prints, and whether as a goal, is the dispatcher's
//! [`shown`]; this module reads it and nothing else. A declaration a verb
//! prints that is unsettled becomes a [`Report`]; a settled fixture `test`
//! prints, a pending source's refusal and a pending source the lowering read
//! are ledger [`Line`]s, one line each, because they record a source's
//! standing rather than a fault in it.

use core::fmt;
use core::slice;
use std::path::Path;

use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Settlement;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::produced_refusal;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Shown;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::shown;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::report::Report;
use crate::report::Subject;
use crate::report::Unsettlement;

quenchant_shape::reason_enum! {
    /// Why a declaration has no entry.
    mod unshown {
        /// The reason a declaration prints nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The verb counts the declaration and prints no line for it.
            Counted,
        }
    }
}

/// One thing a step prints.
#[derive(Clone, Copy, Debug)]
pub enum Entry<'step>
{
    /// A refusal, an unsettled declaration or a goal: a source snippet.
    Report(Report<'step>),
    /// A ledger line: a settled fixture under `test`, a pending source's
    /// refusal under `test`, or a pending source the lowering read.
    Line(Line<'step>),
}

/// A ledger line one source prints beside its reports.
#[derive(Clone, Copy, Debug)]
pub struct Line<'step>
{
    /// The source's path, as the walk reached it.
    path: &'step Path,
    /// What the line records.
    kind: LineKind<'step>,
}

/// What a ledger line records.
#[derive(Clone, Copy, Debug)]
enum LineKind<'step>
{
    /// A fixture that settled, printed by `test`.
    Fixture(&'step DeclarationReport<'step>),
    /// A refusal a pending source carries, printed by `test`.
    Pending(LoweringRefusal<'step>),
    /// A pending source the lowering read, carrying no refusal an expectation
    /// cannot state.
    Lowered,
}

impl fmt::Display for Line<'_>
{
    /// Writes the source's path, then the settled fixture's report, the
    /// pending refusal, or the note that a pending source belongs under the
    /// fixture root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let path = self.path.display();
        match self.kind {
            | LineKind::Fixture(declaration) => write!(f, "{path}: {declaration}"),
            | LineKind::Pending(refusal) => write!(f, "{path}: pending: {refusal}"),
            | LineKind::Lowered => write!(
                f,
                "{path}: unsettled: a pending source whose every expectation can be stated; it \
                 belongs under the fixture root"
            ),
        }
    }
}

/// What remains of one step to print.
#[derive(Clone, Debug)]
enum Cursor<'step>
{
    /// Nothing.
    Done,
    /// One last entry: a source refused as a whole, or a pending source's
    /// refusal of it as a whole.
    Last(Entry<'step>),
    /// The note on a pending source the lowering read, then its declarations.
    Lowered
    {
        /// The declarations, in admission order.
        declarations: slice::Iter<'step, DeclarationReport<'step>>,
        /// The table their core nodes are located through.
        origins: &'step OriginTable,
    },
    /// The declarations still to visit.
    Declarations
    {
        /// The declarations, in admission order.
        declarations: slice::Iter<'step, DeclarationReport<'step>>,
        /// The table their core nodes are located through.
        origins: &'step OriginTable,
    },
    /// The refusals of a pending source still to print.
    Unstatable(slice::Iter<'step, LoweringRefusal<'step>>),
}

/// The entries of one step, in the order its verb prints them.
#[derive(Clone, Debug)]
pub struct Entries<'step>
{
    /// The source's path.
    path: &'step Path,
    /// The source's text.
    text: SourceText<'step>,
    /// The verb the walk runs under.
    verb: Verb,
    /// What remains.
    cursor: Cursor<'step>,
}

/// What `step` prints under `verb`, in order.
///
/// # Specification
/// - requires: nothing; every step is admissible.
/// - ensures: a fault prints nothing here: its line is the caller's. A source
///   the lowering refused as a whole where its root expects declarations is one
///   refusal report. A pending source prints its refusals under `test`, as
///   ledger lines, and nothing under `check`. A pending source the lowering
///   read prints its ledger line, then its declarations as any source does.
///   Each declaration is printed as [`shown`] decides under `verb`: nothing
///   when it is counted; a goal report when it is a goal; when it has a line, a
///   ledger line if it settled, a refusal report if it produced a refusal, and
///   an unsettled report otherwise. Declarations keep admission order.
/// - provides: the one pass a face prints a step through, so no refusal a step
///   carries can reach the walk without reaching the renderer.
/// - fails: never.
/// - panics: none.
/// - intension: borrows the step; allocates nothing until an entry is rendered.
///
/// # Adequacy
/// - hypothesis: L2 — real steps from the dispatcher's walk over sources of
///   every kind: a refused declaration of each producer, an unsettled and a
///   goal-shaped declaration under each verb, a settled fixture, a whole-source
///   refusal, and a pending source under each verb, each asserted at its exact
///   entries, the driver's own witnesses observing the same through the binary.
/// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
/// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
#[inline]
#[must_use]
pub fn entries<'step>(
    step: &'step Step<'step>,
    verb: Verb,
) -> Entries<'step>
{
    let (path, text, cursor) = match *step {
        | Step::Fault { path, .. } => (path, SourceText::from(""), Cursor::Done),
        | Step::Source {
            path,
            text,
            ref composed,
            standing,
            ..
        } => (path, text, cursor(path, text, verb, standing, composed)),
    };
    Entries {
        path,
        text,
        verb,
        cursor,
    }
}

/// The first cursor over a source at `path` that became `composed`.
///
/// # Specification
/// trivial.
fn cursor<'step>(
    path: &'step Path,
    text: SourceText<'step>,
    verb: Verb,
    standing: Standing,
    composed: &'step Composed<'step>,
) -> Cursor<'step>
{
    match (standing, composed) {
        | (Standing::Pending, &Composed::Refused(refusal)) => match verb {
            | Verb::Test => Cursor::Last(Entry::Line(Line {
                path,
                kind: LineKind::Pending(refusal),
            })),
            | Verb::Check(_) => Cursor::Done,
        },
        | (Standing::Pending, &Composed::Settled { ref unstatable, .. }) => match verb {
            | Verb::Test => Cursor::Unstatable(unstatable.iter()),
            | Verb::Check(_) => Cursor::Done,
        },
        | (
            Standing::Settled | Standing::Unsettled | Standing::Refused | Standing::Lowered,
            &Composed::Refused(refusal),
        ) => Cursor::Last(Entry::Report(Report::new(
            path,
            text,
            Subject::Source(refusal),
        ))),
        | (
            Standing::Lowered,
            &Composed::Settled {
                ref report,
                ref origins,
                ..
            },
        ) => Cursor::Lowered {
            declarations: report.declarations().iter(),
            origins,
        },
        | (
            Standing::Settled | Standing::Unsettled | Standing::Refused,
            &Composed::Settled {
                ref report,
                ref origins,
                ..
            },
        ) => Cursor::Declarations {
            declarations: report.declarations().iter(),
            origins,
        },
    }
}

impl<'step> Entries<'step>
{
    /// The entry `declaration` prints, when its verb prints one.
    ///
    /// # Specification
    /// trivial.
    fn declaration(
        &self,
        declaration: &'step DeclarationReport<'step>,
        origins: &'step OriginTable,
    ) -> Maybe<Entry<'step>, unshown::Absent>
    {
        let subject = match (shown(declaration, self.verb), declaration.settlement()) {
            | (Shown::Counted, _) => return Maybe::Absent(unshown::Absent::Counted),
            | (Shown::Line, Settlement::Settled) => {
                return Maybe::Present(Entry::Line(Line {
                    path: self.path,
                    kind: LineKind::Fixture(declaration),
                }));
            },
            | (Shown::Goal, _) => Subject::Goal(declaration),
            | (Shown::Line, Settlement::Unsettled) => match declaration.produced().refusal() {
                | Maybe::Present(refusal) => Subject::Refused {
                    declaration,
                    refusal,
                    origins,
                },
                | Maybe::Absent(produced_refusal::Absent::Unrefused) => Subject::Unsettled {
                    declaration,
                    unsettlement: match (declaration.stated(), declaration.outcome()) {
                        | (&Stated::Verdict(Outcome::Checks(_)), _)
                        | (&Stated::Verdict(Outcome::Runs(_)), Outcome::Checks(_)) => {
                            Unsettlement::Obligations
                        },
                        | (&Stated::Verdict(Outcome::Refuses(_)), _) => Unsettlement::Unproduced,
                        | (
                            &Stated::Verdict(Outcome::Runs(_)),
                            Outcome::Runs(_) | Outcome::Refuses(_),
                        ) => Unsettlement::RunOutcome,
                        | (&Stated::Malformed(_), _) => Unsettlement::Malformed,
                    },
                },
            },
        };
        Maybe::Present(Entry::Report(Report::new(self.path, self.text, subject)))
    }
}

impl<'step> Iterator for Entries<'step>
{
    type Item = Entry<'step>;

    /// The next entry, in the order [`entries`] states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        match core::mem::replace(&mut self.cursor, Cursor::Done) {
            | Cursor::Done => None,
            | Cursor::Last(entry) => Some(entry),
            | Cursor::Lowered {
                declarations,
                origins,
            } => {
                self.cursor = Cursor::Declarations {
                    declarations,
                    origins,
                };
                Some(Entry::Line(Line {
                    path: self.path,
                    kind: LineKind::Lowered,
                }))
            },
            | Cursor::Unstatable(mut refusals) => {
                let refusal = refusals.next();
                self.cursor = Cursor::Unstatable(refusals);
                refusal.map(|&refusal| {
                    Entry::Line(Line {
                        path: self.path,
                        kind: LineKind::Pending(refusal),
                    })
                })
            },
            | Cursor::Declarations {
                mut declarations,
                origins,
            } => {
                while let Some(declaration) = declarations.next() {
                    if let Maybe::Present(entry) = self.declaration(declaration, origins) {
                        self.cursor = Cursor::Declarations {
                            declarations,
                            origins,
                        };
                        return Some(entry);
                    }
                }
                None
            },
        }
    }
}
