//! What one step prints, in order: its reports and its ledger lines.
//!
//! # The verb decides, the dispatcher's `shown` decides it
//!
//! Which declaration a verb prints, and whether as a goal, is the dispatcher's
//! [`shown`]; this module reads it and nothing else. A declaration a verb
//! prints that is unsettled becomes a [`Report`]; a settled fixture `test`
//! prints, a pending source's refusal and a pending source the lowering read
//! are ledger entries because they record a source's standing rather than a
//! fault in it.

use core::fmt;
use core::slice;
use std::path::Path;

use anodized::spec;
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
    /// - requires: nothing.
    /// - ensures: writes the source path, a separator and the kind-specific
    ///   record, propagating destination failure. Adds no line terminator;
    ///   embedded controls in producer text or paths are not escaped.
    /// - provides: the ledger representation beside located reports.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written buffer or
    ///   independent destination-failure observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fixture and pending-source entries expose their path
    ///   prefix and record category through real walks. Arbitrary producer text
    ///   and destination failures are outside these finite formatting fixtures.
    /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
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
/// - hypothesis: L3 — finite real steps under every verb expose entry category
///   and admission order. Interleaved counted declarations and an empty source
///   exercise progress and exhaustion; an empty-path fault exercises silence.
///   Other malformed step/standing combinations are not enumerated by these
///   fixtures.
/// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
/// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
/// - witness: `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`
/// - witness: `entry::tests::faults_and_empty_sources_stay_exhausted`
#[spec(ensures: |ref ret| ret.verb == verb && match *step {
    Step::Fault { path, .. } => core::ptr::eq(core::ptr::from_ref(ret.path), core::ptr::from_ref(path))
        && ret.text.as_ref().is_empty() && matches!(ret.cursor, Cursor::Done),
    Step::Source { path, text, .. } => core::ptr::eq(core::ptr::from_ref(ret.path), core::ptr::from_ref(path)) && core::ptr::eq(core::ptr::from_ref(ret.text.as_ref()), core::ptr::from_ref(text.as_ref())),
})]
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
/// - requires: nothing; any standing and composition are admissible.
/// - ensures: pending refusals are ledger entries only under test; other
///   whole-source refusals are reports. A lowered source starts with its ledger
///   entry; other settled compositions start at their declarations. Borrowed
///   declaration and refusal slices retain their complete order.
/// - provides: the first state of a lazy entry traversal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite source roots under every verb distinguish
///   ledger/report selection and declaration admission. Empty settled
///   compositions expose the zero-length slice boundary. Contradictory
///   standing/composition pairs are outside the produced-step witnesses.
/// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
/// - witness: `entry::tests::faults_and_empty_sources_stay_exhausted`
#[spec(ensures: |ref ret| match (standing, composed, ret) {
    (Standing::Pending, _, &Cursor::Done) => matches!(verb, Verb::Check(_)),
    (Standing::Pending, &Composed::Refused(expected), &Cursor::Last(Entry::Line(Line {
        path: actual, kind: LineKind::Pending(refusal),
    }))) => verb == Verb::Test && core::ptr::eq(core::ptr::from_ref(actual), core::ptr::from_ref(path)) && refusal == expected,
    (Standing::Pending, expected, actual) => {
        let Composed::Settled { ref unstatable, .. } = *expected else { return false; };
        let Cursor::Unstatable(ref held) = *actual else { return false; };
        verb == Verb::Test && core::ptr::eq(core::ptr::from_ref(held.as_slice()), core::ptr::from_ref(unstatable.as_slice()))
    },
    (Standing::Settled | Standing::Unsettled | Standing::Refused | Standing::Lowered,
        &Composed::Refused(refusal), &Cursor::Last(Entry::Report(report))) =>
        core::ptr::eq(core::ptr::from_ref(report.path()), core::ptr::from_ref(path)) && report.class() == crate::Class::Refusal(refusal.classify()),
    (Standing::Lowered, &Composed::Settled { ref report, origins: ref expected, .. },
        &Cursor::Lowered { ref declarations, origins })
    | (Standing::Settled | Standing::Unsettled | Standing::Refused,
        &Composed::Settled { ref report, origins: ref expected, .. },
        &Cursor::Declarations { ref declarations, origins }) =>
        core::ptr::eq(core::ptr::from_ref(declarations.as_slice()), core::ptr::from_ref(report.declarations())) && core::ptr::eq(core::ptr::from_ref(origins), core::ptr::from_ref(expected)),
    _ => false,
})]
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
    /// - requires: the declaration and origins belong to this entry stream.
    /// - ensures: counted declarations have no entry; goals are goal reports. A
    ///   shown settled declaration is a fixture ledger entry; an unsettled
    ///   declaration is a refusal report when one was produced, otherwise an
    ///   unsettled report describing the failed expectation.
    /// - provides: verb-directed selection without changing declaration order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real declarations distinguish counted, goal
    ///   and ledger selection from refused or unproduced expectations. Ordered
    ///   refusal spans expose skipping and substitution. Run-result mismatches
    ///   and malformed expectations are not enumerated by these fixtures.
    /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`
    #[spec(ensures: |ref ret| match (shown(declaration, self.verb), ret) {
        (Shown::Counted, &Maybe::Absent(unshown::Absent::Counted)) => true,
        (Shown::Goal, &Maybe::Present(Entry::Report(report))) =>
            core::ptr::eq(core::ptr::from_ref(report.path()), core::ptr::from_ref(self.path)) && report.class() == crate::Class::Goal,
        (Shown::Line, &Maybe::Present(Entry::Line(Line { path, kind: LineKind::Fixture(held) }))) =>
            declaration.settlement() == Settlement::Settled
                && core::ptr::eq(core::ptr::from_ref(path), core::ptr::from_ref(self.path)) && core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(declaration)),
        (Shown::Line, &Maybe::Present(Entry::Report(report))) =>
            declaration.settlement() == Settlement::Unsettled && core::ptr::eq(core::ptr::from_ref(report.path()), core::ptr::from_ref(self.path))
                && match declaration.produced().refusal() {
                    Maybe::Present(refusal) => report.class() == crate::Class::Refusal(refusal.classify()),
                    Maybe::Absent(produced_refusal::Absent::Unrefused) => matches!(report.class(), crate::Class::Unsettled(_)),
                },
        _ => false,
    })]
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
    /// - requires: nothing.
    /// - ensures: each yielded entry belongs to the source and consumes at
    ///   least one remaining candidate. Hidden declarations are skipped without
    ///   ending the traversal. Exhaustion remains exhausted on every subsequent
    ///   call.
    /// - provides: declaration order, preceded by a lowered-source ledger entry
    ///   when present; pending refusals retain their source order.
    /// - fails: never; exhaustion is None.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interleaved counted and refused declarations expose
    ///   premature stopping or reordering; empty sources and faults expose
    ///   false entries and resurrection after exhaustion. Finite pending
    ///   fixtures exercise ledger selection, not arbitrary long refusal
    ///   sequences.
    /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
    /// - witness: `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`
    /// - witness: `entry::tests::faults_and_empty_sources_stay_exhausted`
    #[spec(
        captures: [before = match self.cursor {
            Cursor::Done => 0_usize,
            Cursor::Last(_) => 1_usize,
            Cursor::Lowered { ref declarations, .. } => declarations.len().saturating_add(1_usize),
            Cursor::Declarations { ref declarations, .. } => declarations.len(),
            Cursor::Unstatable(ref refusals) => refusals.len(),
        }],
        ensures: |ref ret| {
            let remaining = match self.cursor {
                Cursor::Done => 0_usize,
                Cursor::Last(_) => 1_usize,
                Cursor::Lowered { ref declarations, .. } => declarations.len().saturating_add(1_usize),
                Cursor::Declarations { ref declarations, .. } => declarations.len(),
                Cursor::Unstatable(ref refusals) => refusals.len(),
            };
            ret.as_ref().map_or(remaining == 0_usize, |entry| remaining < before && match *entry {
                Entry::Report(report) => core::ptr::eq(core::ptr::from_ref(report.path()), core::ptr::from_ref(self.path)),
                Entry::Line(line) => core::ptr::eq(core::ptr::from_ref(line.path), core::ptr::from_ref(self.path)),
            })
        },
    )]
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

/// Entry policy through real composition and the walk's fault boundary.
#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Standing;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::compose;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Entry;
    use super::entries;

    #[test]
    fn counted_declarations_preserve_visible_order_and_exhaustion()
    {
        let text = SourceText::from(
            "def quiet = 1 ;\ndef first = missing ;\ndef middle = 2 ;\ndef second = missing ;\ndef last = 3 ;\n",
        );
        let grammar = built_in().expect("the grammar builds");
        let step = Step::Source {
            path: Path::new("ordered.gandr"),
            root: SourceRoot::Strict,
            text,
            composed: compose(
                &grammar,
                SourceRoot::Strict.corpus_root(),
                text,
                &mut LoweringCount::default(),
            )
            .expect("the source composes"),
            standing: Standing::Unsettled,
        };
        let expected = [
            text.as_ref().find("missing").expect("the first refusal"),
            text.as_ref().rfind("missing").expect("the last refusal"),
        ]
        .map(|start| {
            Maybe::Present(
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start + "missing".len()),
                )
                .expect("an ordered ASCII token"),
            )
        });
        let mut stream = entries(&step, Verb::Check(Goals::Gated));
        let actual = stream
            .by_ref()
            .map(|entry| match entry {
                | Entry::Report(report) => report.span(),
                | Entry::Line(_) => panic!("strict counted declarations are not ledger entries"),
            })
            .collect::<Vec<_>>();
        assert_eq!(actual.as_slice(), &expected);
        assert!(
            stream.next().is_none(),
            "exhaustion cannot resurrect a skipped declaration"
        );
    }

    #[test]
    fn faults_and_empty_sources_stay_exhausted()
    {
        let mut walk = Walk::new(vec![PathBuf::new()]);
        let Maybe::Present(fault) = walk.step()
        else {
            panic!("an empty path is a fault, not an empty walk");
        };
        assert!(matches!(fault, Step::Fault { .. }));
        let text = SourceText::from("");
        let grammar = built_in().expect("the grammar builds");
        let empty = Step::Source {
            path: Path::new("empty.gandr"),
            root: SourceRoot::Strict,
            text,
            composed: compose(
                &grammar,
                SourceRoot::Strict.corpus_root(),
                text,
                &mut LoweringCount::default(),
            )
            .expect("the empty source composes"),
            standing: Standing::Unsettled,
        };
        for step in [&fault, &empty] {
            for verb in [
                Verb::Check(Goals::Gated),
                Verb::Check(Goals::Reported),
                Verb::Test,
            ] {
                let mut stream = entries(step, verb);
                assert!(stream.next().is_none());
                assert!(
                    stream.next().is_none(),
                    "an exhausted stream stays exhausted"
                );
            }
        }
    }
}
